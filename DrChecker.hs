-- Simple posix thread C program data race checker
-- We use stateT error Monad to do this job.
import Text.PrettyPrint
import Control.Monad.State
import Control.Monad.Error
import Data.Char
import List
import LexC
import ParC
import ErrM
import AbsC

-- Another Type Representation. If we have "int *a;" then the type we get is Point TInt
data TypeP = Basic [Declaration_specifier]
           | Ptr TypeP
           | NULL
           deriving (Eq, Show)

type VarName = String                   -- variable name
type Type = (TypeP,Owner_specifier)     -- type
type ReferVars = [VarName]              -- possibly refered variables
type AccessTime = Int                   -- counters remember how many threads could potentially access this variable

type MethodName = String                -- method name
type ReqireVars = [VarName]             -- required variable name
data MethodTyp  = ThreadFun
                | NormalFun
                  deriving (Eq, Show)

type MutexName     = VarName
type ProtectedVars = [VarName]

type VarTypInfo    = (VarName, Type, ReferVars, AccessTime)

type MethodTypInfo = (MethodName, ReqireVars, MethodTyp)

type MutexTypInfo  = (MutexName, ProtectedVars)

data TypeInfo = Var VarTypInfo 
              | Method MethodTypInfo
              | Mutex MutexTypInfo
                deriving (Show)

type LockN = String
type Lock  = (MutexName, [LockN])
type LockS = [Lock]

data CheckingFunType = ThreadFunc
                     | NormalFunc
                     | NoFun
                       deriving (Eq,Show)

type TypeInfoS = [TypeInfo]

type TypeEnv = (TypeInfoS,LockS,CheckingFunType)

type CheckM = StateT TypeEnv (Either String)

---------------------------------------------------------------------------------------------------------------------------
-- Error Message Definition Begin
errmsg1 = "Check Error: Don't allow variable delaration in the inner block of the function"
errmsg2 = "Check Error: Sorry, don't support label, switch-case-default statement by now"
errmsg3 = "Check Error: LHS of the assignment expression is not a variable"
errmsg4 varN = "Check Error: Variable "++varN++" is not defined"
errmsg5 = "Check Error: RHS of the assignment expression is not a variable"
errmsg6 = "Check Error: RHS and LHS dosn't have the same type in the assignment expression"
errmsg7 = "Check Error: Expressions in assignment are not consistent (Ownership or Type)"
errmsg8 = "Check Error: Expression in assignment do not have the same owner"
errmsg9 = "Check Error: Sorry, don't support array type by now"
errmsg10 str = "Check Error: The lock of Var "++str++" hasn't been aquired"
errmsg11 = "Check Error: Type Environment got messed up"
errmsg12 = "Check Error: Sorry, don't support goto statement by now"
errmsg13 = "Check Error: Mutex can't be declared within functions"
errmsg14 = "Check Error: Sorry, don't support group initializer"
errmsg15 = "Check Error: The argument in pthread_mutex_lock is not of type (pthread_mutex_t *)"
errmsg16 = "Check Error: The argument in pthread_mutex_lock is more than 1"
errmsg17 str = "Check Error: Mutex "++str++" is not defined"
errmsg18 str = "Check Error: P operation of Mutex "++str++" doesn't called within this composition statement"
errmsg19 = "Check Error: P V operations of Mutex are not clear in the composition statement"
errmsg20 = "Check Error: Mutex couldn't be used in the assignment statement"
errmsg21 str = "Check Error: The variable "++str++" of owner thisThread can't be passed to thread function as a parameter"
errmsg22 str = "Check Error: The variable "++str++" of owner oneThread can't be passed as the funtion parameter"
errmsg23 = "Check Error: The 1st actual parameter of pthread_create function should be of type (pthread_t *)" 
errmsg24 = "Check Error: The 2nd actual parameter of pthread_create function should be of type (pthread_attr_t *) or NULL" 
errmsg25 = "Check Error: The 3rd actual parameter of pthread_create function should be a pointer to a thread function"
errmsg26 = "Check Error: The owner of 4th actual parameter of pthread_create function can't be oneThread"
errmsg27 = "Check Error: The owner of 4th actual parameter of pthread_create function can't be thisThread"
errmsg28 metN = "Check Error: Method "++metN++" is not defined"
errmsg29 = "Check Error: Don't have enough locks to type check the argument of the function"
errmsg30 = "Check Error: Don't have enough locks to type check the statement"
errmsg31 = "Check Error: Sorry, don't support array by now"
errmsg32 = "Check Error: Sorry, don't support function only have declaration or abstract declaration"
errmsg33 = "Check Error: Sorry, function argument should contain types"
errmsg34 = "Check Error: This couldn't happen"
errmsg35 = "Check Error: from getParaFromDirDecl, this shouldn't happen"
errmsg36 = "Check Error: typecheckThreadFunction, function is not of thread function type"
errmsg37 = "Check Error: typecheckNormalFunction, function is not of Normal function type"
errmsg38 = "Check Error: type information extraction problem"
errmsg39 = "Check Error: Global variables are not allowed to be declared as thisThread"
errmsg40 str = "Check Error: The protected variables set of Mutex "++str++" have intersections with other mutex(es)"
errmsg41 str = "Check Error: The owner of local variable "++str++" shouldn't be defined as oneThread"
errmsg42 str = "Check Error: The oneThread variable "++str++" is used by more than one thread"
-- Error Message Definition End
---------------------------------------------------------------------------------------------------------------------------

---------------------------------------------------------------------------------------------------------------------------
-- 1. We must get enough information before we could really get started. Typing information that we need is:
--    a. All the global variables and their typing information (VarName, Type, ReferVars, AccessTime).
--    b. All the normal function names and their required owners. 
--    c. All the thread functions (thread function couldn't be used as normal function).
--    d. All the mutexes names.

-- 2. What we do next is staticly check each of the normal functions and thread functions. We assume that the 
--    function hold all of locks of the variables listed in the requires statement, and the locks of all the
--    parameters. Then we type check the enclosed statements. We add all the parameters and local variables temporarily
--    into the typing environment.
--
-- 3. We stipulate that the mutex should only be closed in one compositional statements (which is a bit strict). It's
--    for the convenience of tracking it. In terms of ownership, We treat the pointers with different layers all the same.
-- 
-- 4. About the ownership. Global variable couldn't be declared as "thisThread". Local Variable couldn't be declared as
--    "oneThread". The default ownership is "Self"

-- Notice: When type check the program. If there an unknown method is called. We assume that this method is valid, because
--         it might be the system functions. But we assume that we don't need any locks to access it. We must rewrite those
--         functions and variables to make sure that programs with this kind of functions and variables could work.
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
-- Things Left To Do:
-- 1. think about another thing: if just read, don't have to get the lock
-- 2. void* assignment 
-- 3. pretty printer
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
-- Extract the global environment
---------------------------------------------------------------------------------------------------------------------------
extractEnv :: Program -> CheckM TypeInfoS
extractEnv p = do typeinfos <- extractEnvWH p 
                  return $ typeinfos
    where
      extractEnvWH :: Program -> CheckM TypeInfoS
      extractEnvWH (Progr []) = return []
      extractEnvWH (Progr (x:xs)) = do typInf <- extractExternalDec x
                                       typInfS <- extractEnv (Progr xs)
                                       return $ typInf++typInfS

checkRequiresAreGlobals :: TypeInfoS -> CheckM Bool
checkRequiresAreGlobals []     = return True
checkRequiresAreGlobals (x:xs) = case x of
                                   Method (medN, reqvars, mtyp) -> do areDeclared reqvars
                                                                      checkRequiresAreGlobals xs
                                   otherwise -> checkRequiresAreGlobals xs
                                       

---------------------------------------------------------------------------------------------------------------------------
-- test extractEnv function
---------------------------------------------------------------------------------------------------------------------------
testExtractEnv :: IO ()
testExtractEnv = do pro <- readFile "thread2.c"
                    let ts = myLexer pro in case pProgram ts of
                                              Bad s   -> do putStrLn "\nParse        Failed...\n"
                                              Ok tree -> case runStateT (extractEnv tree) ([],[],NoFun) of 
                                                           Right typeinfos -> putStrLn $ show typeinfos
                                                           Left err        -> putStrLn err
---------------------------------------------------------------------------------------------------------------------------


---------------------------------------------------------------------------------------------------------------------------
-- Help function to retrieve method and variable name from a Direct_declarator
---------------------------------------------------------------------------------------------------------------------------
getNFromDirDec :: Direct_declarator -> MethodName
getNFromDirDec (Name (Ident nam)) = nam
getNFromDirDec (ParenDecl decl) = getNFromDec decl
getNFromDirDec (InnitArray directD _) = fail errmsg9
getNFromDirDec (Incomplete directD) = fail errmsg9
getNFromDirDec (NewFuncDec directD _) = getNFromDirDec directD
getNFromDirDec (OldFuncDef directD _) = getNFromDirDec directD
getNFromDirDec (OldFuncDec directD ) = getNFromDirDec directD

---------------------------------------------------------------------------------------------------------------------------
-- Help function to retrieve method and variable name from a Declarator
---------------------------------------------------------------------------------------------------------------------------
getNFromDec :: Declarator -> MethodName
getNFromDec (BeginPointer _ directD) = getNFromDirDec directD
getNFromDec (NoPointer directD) = getNFromDirDec directD

---------------------------------------------------------------------------------------------------------------------------
-- Help function to turn Ident list to String list
---------------------------------------------------------------------------------------------------------------------------
identToStr :: [Ident] -> [String]
identToStr identlist = map (\(Ident str) -> str) identlist

---------------------------------------------------------------------------------------------------------------------------
-- Help function to extract the proper type
---------------------------------------------------------------------------------------------------------------------------
extractType :: TypeP -> Declarator -> TypeP
extractType declSpec (NoPointer dirDec) = declSpec
extractType declSpec (BeginPointer Point dirDec) = Ptr declSpec
extractType declSpec (BeginPointer (PointQual _) dirDec) = Ptr declSpec
extractType declSpec (BeginPointer (PointPoint ptr) dirDec) = extractType (Ptr declSpec) (BeginPointer ptr dirDec)
extractType declSpec (BeginPointer (PointQualPoint _ ptr) dirDec) = extractType (Ptr declSpec) (BeginPointer ptr dirDec)

---------------------------------------------------------------------------------------------------------------------------
-- Help function to see whether the variable is of mutex type
---------------------------------------------------------------------------------------------------------------------------
isMutexType :: [Declaration_specifier] -> Bool
isMutexType spec = elem True $ map (\x -> case x of
                                            Type TPthMtxT -> True
                                            otherwise     -> False) spec

---------------------------------------------------------------------------------------------------------------------------
-- Help function to extract variables and mutex to TypeInfoS
---------------------------------------------------------------------------------------------------------------------------
extractVarMutex :: String -> [Declaration_specifier] -> Owner_specifier -> TypeP -> TypeInfoS -> CheckM TypeInfoS
extractVarMutex name typ owner typp tinS = do if (isMutexType typ) 
                                                then return $ [(Mutex (name, []))]++tinS
                                                else return $ [(Var (name, (typp, owner), [name], 0))]++tinS

---------------------------------------------------------------------------------------------------------------------------
-- Help function to extract variables to TypeInfoS, if encounter mutex definition, report an error
---------------------------------------------------------------------------------------------------------------------------
extractVar :: String -> [Declaration_specifier] -> Owner_specifier -> TypeP -> CheckM TypeInfo
extractVar name typ owner typp = do if (isMutexType typ) 
                                       then fail errmsg13
                                       else return $ (Var (name, (typp, owner), [name], 0))

---------------------------------------------------------------------------------------------------------------------------
-- Help function to find the type of a variable in the environment
---------------------------------------------------------------------------------------------------------------------------
getVarType :: VarName -> CheckM TypeP
getVarType varN = do (typeinfos,locks,_) <- get
                     typeP <- getVarTypeH varN typeinfos
                     return typeP
    where
      getVarTypeH :: String -> TypeInfoS -> CheckM TypeP
      getVarTypeH "NULL" _    = return NULL
      getVarTypeH varN []     = fail $ errmsg4 varN
      getVarTypeH varN (x:xs) = case x of
                                 Var (varnam, (typep, owner), refvars, acctime) -> 
                                     if varnam == varN 
                                        then return typep
                                        else do typep <- getVarTypeH varN xs
                                                return typep
                                 Mutex (mutnam, protvars) ->
                                     if mutnam == varN
                                        then return $ Basic [Type TPthMtxT]
                                        else do typep <- getVarTypeH varN xs
                                                return typep
                                 otherwise -> getVarTypeH varN xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function to see whether a variable is in the typing environment
---------------------------------------------------------------------------------------------------------------------------
isDeclared :: VarName -> CheckM Bool
isDeclared varn = do (typeinfos,locks,_) <- get
                     isDeclaredWH varn typeinfos
    where
      isDeclaredWH :: VarName -> TypeInfoS -> CheckM Bool
      isDeclaredWH "NULL" _     = return True
      isDeclaredWH vname []     = return False
      isDeclaredWH vname (x:xs) = case x of
                                    Var (varnam, (typep, owner), refvars, acctime) -> 
                                        if varnam == vname 
                                           then return True
                                           else isDeclaredWH vname xs
                                    otherwise -> isDeclaredWH vname xs

areDeclared :: [VarName] -> CheckM Bool
areDeclared []     = return True
areDeclared (x:xs) = do b <- isDeclared x
                        assert b (errmsg4 x)
                        areDeclared xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function to find the type of a variable in the environment
---------------------------------------------------------------------------------------------------------------------------
getVarOwner :: VarName -> CheckM Owner
getVarOwner varN = do (typeinfos,locks,_) <- get
                      owner <- getVarOwnerH varN typeinfos
                      return owner
    where
      getVarOwnerH :: String -> TypeInfoS -> CheckM Owner
      getVarOwnerH "NULL" _    = return TSelf
      getVarOwnerH varN []     = fail $ errmsg4 varN
      getVarOwnerH varN (x:xs) = case x of
                                   Var (varnam, (typep, (Owner_spec owner)), refvars, acctime) -> 
                                       if varnam == varN
                                          then return owner
                                          else do owner' <- getVarOwnerH varN xs
                                                  return owner' 
                                   otherwise -> getVarOwnerH varN xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function to find the variables that the variable points to
---------------------------------------------------------------------------------------------------------------------------
getVarRef :: VarName -> TypeInfoS -> CheckM ReqireVars
getVarRef "NULL" _     = return []
getVarRef varN  []     = fail $ errmsg4 varN
getVarRef varN  (x:xs) = case x of
                           Var (varnam, (typep, owner), refvars, acctime) -> 
                               if varnam == varN 
                                  then return refvars
                                  else do typep <- getVarRef varN xs
                                          return typep   
                           otherwise -> getVarRef varN xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function to find the variables that the variables point to
---------------------------------------------------------------------------------------------------------------------------
getVarsRef :: [VarName] -> TypeInfoS -> CheckM ReqireVars
getVarsRef [] typeinfos     = return []
getVarsRef (x:xs) typeinfos = do refvars  <- getVarRef x typeinfos
                                 refvarsS <-getVarsRef xs typeinfos
                                 return $ refvars++refvarsS


---------------------------------------------------------------------------------------------------------------------------
-- Help function to update the refvars of a variable in the environment
---------------------------------------------------------------------------------------------------------------------------
updateVarRefvars :: String -> String -> CheckM ()
updateVarRefvars varN varN2 = do (typeinfos,locks,checkingt) <- get
                                 updtypinfo <- updateTypeinfos varN varN2 typeinfos
                                 put $ (updtypinfo, locks, checkingt)
                                 return ()
    where updateTypeinfos varN varN2 typingins = do v2refs <- (getVarRef varN2 typingins)
                                                    return $ map (\x -> case x of
                                                                          varinfo@(Var (varnam, (typep, owner), refvars, acctime))
                                                                              -> if varN == varnam
                                                                               -- here we use the new variable, in the if
                                                                               -- statement, we will try to bind the info
                                                                               -- of the variable in two branches into one
                                                                                    then (Var (varnam, (typep, owner), v2refs, acctime))
                                                                                    else varinfo
                                                                          methodinfo@(Method mtdtinfo) -> methodinfo
                                                                          mutexinfo@(Mutex mutinfo) -> mutexinfo
                                                                 ) typingins

---------------------------------------------------------------------------------------------------------------------------
-- Helper function: update the access time of oneThread variables
---------------------------------------------------------------------------------------------------------------------------
updateAccessTime :: VarName -> TypeInfoS -> CheckM TypeInfoS
updateAccessTime varn []     = fail $ errmsg4 varn
updateAccessTime varn (x:xs) = case x of
                                 Var (varn',typ, varrefs, a) -> 
                                     if varn == varn'
                                        then do assert (a<1) $ errmsg42 varn'
                                                --typeinfos <- updateAccessTime varn xs
                                                return $ [Var (varn',typ, varrefs, a+1)]++xs
                                        else do typeinfos <- updateAccessTime varn xs
                                                return $ [Var (varn',typ, varrefs, a)]++typeinfos
                                 otherwise -> do typeinfos <- updateAccessTime varn xs
                                                 return (x:typeinfos)
                                                
---------------------------------------------------------------------------------------------------------------------------
-- Help function, to check whether a variable is within the current lockset. if we check oneThread variables in thread
-- function, it would increase the value of its access time.
---------------------------------------------------------------------------------------------------------------------------
isAccessible :: VarName -> CheckM Bool
isAccessible varN = do (typinfos,locks,checking) <- get
                       owner <- getVarOwner varN
                       if owner==TThisThread
                          then return True
                          else if (owner==TOneThread) && (checking==ThreadFunc)
                                  then do typeinfos' <- updateAccessTime varN typinfos
                                          put (typeinfos',locks,checking)
                                          return True
                                  else do varRefs <- getVarRef varN typinfos
                                          return $ elem True $ map (\nam -> (elem nam varRefs)) $ foldr (\x->(\y->x++y)) [] (map (\(n,v) -> v) locks)

---------------------------------------------------------------------------------------------------------------------------
-- Help function, to check whether a couple of variables are within the current lockset. if we check oneThread variables 
-- in thread function, it would increase the value of its access time.
---------------------------------------------------------------------------------------------------------------------------
areAccessible :: [VarName] -> CheckM Bool
areAccessible []     = return True
areAccessible (x:xs) = do b <- isAccessible x
                          assert b errmsg30
                          areAccessible xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function, to get the name of the expression if it's a variable or (&/*) of a variable
---------------------------------------------------------------------------------------------------------------------------
getExpVarNam :: Exp -> CheckM String
getExpVarNam (Evar (Ident varN))        = return varN
getExpVarNam (Epreop Address exp)       = getExpVarNam exp
getExpVarNam (Epreop Indirection exp)   = getExpVarNam exp
getExpVarNam _                          = fail errmsg7

---------------------------------------------------------------------------------------------------------------------------
-- Help function, assignment expression update
---------------------------------------------------------------------------------------------------------------------------
typecheckAssignExp :: String -> Exp -> CheckM ()
typecheckAssignExp varN exp = do varN2 <- getExpVarNam exp
                                 typ   <- getExpType 0 exp
                                 case typ of 
                                   ((Basic specs),True) -> return ()
                                   ((Ptr t),True)       -> updateVarRefvars varN varN2
                                   otherwise            -> return ()   --it's not possible to reach here

---------------------------------------------------------------------------------------------------------------------------
-- Help function, to see whether two types are equal
---------------------------------------------------------------------------------------------------------------------------
isTypeEqual :: TypeP -> TypeP -> Bool
isTypeEqual (Basic a) (Basic b) = a==b           -- ** maybe it's a little bit strict to let even the order equal
isTypeEqual (Basic a) (Ptr b)   = False
isTypeEqual (Ptr a) (Basic b)   = False
isTypeEqual (Ptr a) (Ptr b)     = isTypeEqual a b
isTypeEqual (Ptr _) NULL        = True
isTypeEqual NULL (Ptr _)        = True

---------------------------------------------------------------------------------------------------------------------------
-- Help function, see whether two types are equal. If one of the expression is not a variable or a pointer/address 
-- of variable then return false. If two variables (pointer/address) are of different types, it fails. 
-- Otherwise return True
---------------------------------------------------------------------------------------------------------------------------
isTypeEqual2 :: (TypeP, Bool) -> (TypeP, Bool) -> CheckM Bool
isTypeEqual2 (typ1, True) (typ2, True) = if (isTypeEqual typ1 typ2)
                                            then return True
                                            else fail errmsg6
isTypeEqual2 _ _                       = return False

---------------------------------------------------------------------------------------------------------------------------
-- Help function. Get the type of variable or (*/&) of a variable. Using a boolean variable to indicate it's not the case.
---------------------------------------------------------------------------------------------------------------------------
getExpType :: Int -> Exp -> CheckM (TypeP, Bool)
getExpType n (Evar (Ident varN1)) = do typeP1 <- getVarType varN1  --n indicate how many indirections we should add
                                       return $ convertType n typeP1
getExpType n (Epreop Indirection e) = getExpType (n-1) e
getExpType n (Epreop Address e) = getExpType (n+1) e
getExpType n _ = return (Basic [], False)

convertType :: Int -> TypeP -> (TypeP, Bool)
convertType 0 t = (t, True)
convertType n typ@(Ptr t) = if n>0 
                               then convertType (n-1) (Ptr typ)
                               else convertType (n+1) t
convertType n typ@(Basic t) = if n>0
                                 then convertType (n-1) (Ptr typ)
                                 --when it's already a basic type, it shouldn't be instanticate again
                                 else ((Basic t), False)

---------------------------------------------------------------------------------------------------------------------------
-- Help function. Get the owner of the expression, with the same assumption as getExpType
---------------------------------------------------------------------------------------------------------------------------
getExpOwner :: Exp -> CheckM (Owner, Bool)
getExpOwner (Evar (Ident varN1)) = do owner <- getVarOwner varN1
                                      return (owner, True)
getExpOwner (Epreop Indirection e) = getExpOwner e
getExpOwner (Epreop Address e) = getExpOwner e
getExpOwner _ = return (TSelf, False)

---------------------------------------------------------------------------------------------------------------------------
-- Help function, see whether two owners are equal. if one of the expression is not a variable or variable pointer/address
-- then return false. if two variables (pointer/address) are of the different owner, it fails. Otherwise return True
---------------------------------------------------------------------------------------------------------------------------
isOwnerEqual ::(Owner, Bool) -> (Owner, Bool) -> CheckM Bool
isOwnerEqual (owner1, True) (owner2, True) = if owner1==owner2 
                                                then return True
                                                else fail errmsg7
isOwnerEqual _ _ = return False

---------------------------------------------------------------------------------------------------------------------------
-- Help function. Update the variables that this mutex protects, the variables should be the refered ones pointed 
-- by the [ident]
---------------------------------------------------------------------------------------------------------------------------
updateMutexLocks :: MutexName -> [Ident] -> CheckM ()
updateMutexLocks mutN idents = do (typeinfos, locks, checkingt) <- get
                                  typeinfos' <- updateMutexLocks mutN idents typeinfos
                                  put (typeinfos', locks, checkingt)
                                  return ()
    where 
      updateMutexLocks :: MutexName -> [Ident] -> TypeInfoS -> CheckM TypeInfoS
      updateMutexLocks mutN idents []     = fail $ errmsg17 mutN
      updateMutexLocks mutN idents (x:xs) = case x of
                                              mutt@(Mutex (mutN', protVars)) -> if mutN==mutN'
                                                                                   then do (typeinfos, locks, _) <- get
                                                                                           varsrefs <- getVarsRef (identToStr idents) typeinfos
                                                                                           
                                                                                           return $ [Mutex (mutN, nub ((identToStr idents)++protVars++varsrefs))]++xs
                                                                                   else do ys <- updateMutexLocks mutN idents xs
                                                                                           return $ [mutt]++ys
                                              vart@(Var vartypeinfo)          -> do ys <- updateMutexLocks mutN idents xs
                                                                                    return $ [vart]++ys
                                              mett@(Method methodtypeinfo)    -> do ys <- updateMutexLocks mutN idents xs
                                                                                    return $ [mett]++ys
      
---------------------------------------------------------------------------------------------------------------------------
-- Update the current lock set
-- This function should be called after updateMutexLocks, so that it doesn't have to check whether the mutex was defined
---------------------------------------------------------------------------------------------------------------------------
addLockSet :: MutexName -> [Ident] -> CheckM ()
addLockSet mutN idents = do (typeinfos, locks, checkingt) <- get
                            varsrefs <- getVarsRef (identToStr idents) typeinfos
                            put (typeinfos, ((mutN,(identToStr idents)++varsrefs):locks), checkingt)

removeLockSet :: MutexName -> CheckM ()
removeLockSet mutN = do (typeinfos, locks, checkingt) <- get
                        locks' <- removeLocks mutN locks
                        put $ (typeinfos,locks',checkingt)
    where
      removeLocks mutN []               = fail $ errmsg18 mutN
      removeLocks mutN ((mutN', ls):xs) = if mutN==mutN' 
                                             then return xs
                                             else do ys <- removeLocks mutN xs
                                                     return $ (mutN', ls):ys

---------------------------------------------------------------------------------------------------------------------------
-- Help function, assertion      
---------------------------------------------------------------------------------------------------------------------------
assert :: Bool -> String -> CheckM ()
assert True  str = return ()
assert False str = fail str

---------------------------------------------------------------------------------------------------------------------------
-- Help function. See whether an expression is a mutex
---------------------------------------------------------------------------------------------------------------------------
isMutex :: Exp -> CheckM Bool
isMutex exp = do varN <- getExpVarNam exp
                 (typeinfos, locks, _) <- get
                 isMutexWH varN typeinfos
    where
      isMutexWH :: MutexName -> TypeInfoS -> CheckM Bool
      isMutexWH mutN []     = return False
      isMutexWH mutN (x:xs) = case x of
                                Mutex (mutN',_) -> return True
                                otherwise -> isMutexWH mutN xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function. See whether the owner of variable (address || pointer) is thisThread
---------------------------------------------------------------------------------------------------------------------------
isExpthisThread :: Exp -> CheckM Bool
isExpthisThread (Evar (Ident varN))        = do owner <- getVarOwner varN 
                                                return $ owner==TThisThread
isExpthisThread (Epreop Address exp)       = isExpthisThread exp
isExpthisThread (Epreop Indirection exp)   = isExpthisThread exp
isExpthisThread _                          = return False 

---------------------------------------------------------------------------------------------------------------------------
-- Help function. See whether the owner of variable (address || pointer) is oneThread
---------------------------------------------------------------------------------------------------------------------------
isExponeThread :: Exp -> CheckM Bool
isExponeThread (Evar (Ident varN))        = do owner <- getVarOwner varN 
                                               return $ owner==TOneThread
isExponeThread (Epreop Address exp)       = isExponeThread exp
isExponeThread (Epreop Indirection exp)   = isExponeThread exp
isExponeThread _                          = return False 

isExpSOneThread :: [Exp] -> CheckM Bool
isExpSOneThread []     = return True
isExpSOneThread (x:xs) = do b1 <- isExponeThread x
                            assert (not b1) errmsg29
                            isExpSOneThread xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function. See the type of the function: Thread function or Normal function
---------------------------------------------------------------------------------------------------------------------------
getFunctionType :: Exp -> CheckM MethodTyp
getFunctionType (Evar (Ident metN)) = do (typeinfos, locks, _) <- get
                                         getFunTyp metN typeinfos
    where
      getFunTyp :: MethodName -> TypeInfoS -> CheckM MethodTyp
      getFunTyp metN []     = fail $ errmsg28 metN
      getFunTyp metN (x:xs) = case x of
                                Method (metN', revars, metT) -> if metN==metN'
                                                                   then return metT
                                                                   else getFunTyp metN xs
                                otherwise -> getFunTyp metN xs

---------------------------------------------------------------------------------------------------------------------------
-- Help function. get the variables that are refered by the list of variables in the requires statement of a function
---------------------------------------------------------------------------------------------------------------------------
getFunctionRequires :: MethodName -> CheckM ReqireVars
getFunctionRequires metN = do (typeinfos, locks, _) <- get
                              getFunReq metN typeinfos
    where
      getFunReq :: MethodName -> TypeInfoS -> CheckM ReqireVars
      getFunReq metN []     = return [] --fail $ errmsg28 metN
      getFunReq metN (x:xs) = case x of
                                Method (metN', revars, metT) -> if metN==metN'
                                                                   then return revars
                                                                   else getFunReq metN xs
                                otherwise -> getFunReq metN xs

---------------------------------------------------------------------------------------------------------------
-- Help functions: Following four functions are used to update mutex protected information between 
-- the check of different functions
---------------------------------------------------------------------------------------------------------------
getMutexProtectsVars :: MutexName -> TypeInfoS -> CheckM ProtectedVars
getMutexProtectsVars mutexn []     = fail $ errmsg17 mutexn
getMutexProtectsVars mutexn (x:xs) = case x of
                                       Mutex (mutexn', pvars) -> if mutexn'==mutexn
                                                                    then return pvars
                                                                    else getMutexProtectsVars mutexn xs
                                       otherwise              -> getMutexProtectsVars mutexn xs

getVarAccessTime :: VarName -> TypeInfoS -> CheckM AccessTime
getVarAccessTime varn []     = fail $ errmsg4 varn
getVarAccessTime varn (x:xs) = case x of
                                 Var (varn',_,_,accesstime) -> if varn'==varn
                                                                  then return accesstime
                                                                  else getVarAccessTime varn xs
                                 otherwise                  -> getVarAccessTime varn xs

updateMutexOneThreadVarTypeInfo :: TypeInfoS -> TypeInfoS -> CheckM TypeInfoS
updateMutexOneThreadVarTypeInfo [] typeinfos' = return []
updateMutexOneThreadVarTypeInfo (ti:typeinfos) typeinfos' = case ti of
                                                              Mutex (mutexn, pvars) -> 
                                                                  do pvars' <- getMutexProtectsVars mutexn typeinfos'
                                                                     tpins  <- updateMutexOneThreadVarTypeInfo typeinfos typeinfos'
                                                                     return ((Mutex (mutexn, nub (pvars++pvars'))):tpins)
                                                              Var (varn',(tp,owner),varrefs,accesstime) ->
                                                                  if owner==(Owner_spec TOneThread)
                                                                     then do t <- getVarAccessTime varn' typeinfos'
                                                                             tpins <- updateMutexOneThreadVarTypeInfo typeinfos typeinfos'
                                                                             return ((Var (varn',(tp,owner),varrefs,t)):tpins)
                                                                     else do tpins  <- updateMutexOneThreadVarTypeInfo typeinfos typeinfos'
                                                                             return (ti:tpins)
                                                                             
                                                              otherwise -> 
                                                                  do tpins  <- updateMutexOneThreadVarTypeInfo typeinfos typeinfos'
                                                                     return (ti:tpins)

updateMutexOneThreadVarTypeEnv :: TypeEnv -> TypeEnv -> CheckM TypeEnv
updateMutexOneThreadVarTypeEnv (typeinfos, locks, checkingt) (typeinfos', locks', checkingt') = do typeinfos'' <- updateMutexOneThreadVarTypeInfo typeinfos typeinfos'
                                                                                                   return (typeinfos'', locks, checkingt)
---------------------------------------------------------------------------------------------------------------


------------------------------------------------------------------------------------------------------------------
-- Help function: Following 3 Functions check whether two mutex have intersections
------------------------------------------------------------------------------------------------------------------
isMutexIntersect :: ProtectedVars -> TypeInfoS -> CheckM ()
isMutexIntersect pvars []     = return ()
isMutexIntersect pvars (x:xs) = case x of
                                  Mutex (mnam, pvar') -> do assert (not (isIntersect pvars pvar')) $ errmsg40 mnam
                                                            isMutexIntersect pvars xs
                                  otherwise -> isMutexIntersect pvars xs

isIntersect :: ProtectedVars -> ProtectedVars -> Bool
isIntersect pvar []      = False
isIntersect [] pvars'    = False
isIntersect (x':xs) pvar' = if (elem True (map (\x-> x==x') pvar'))
                               then True
                               else isIntersect xs pvar'
                                  
-- Function that check whether two mutexes in typeinfos have intersections
areMutexesIntersect :: TypeInfoS -> CheckM ()
areMutexesIntersect [] = return ()
areMutexesIntersect (x:xs) = case x of
                               Mutex (mnam, pvar') -> do isMutexIntersect pvar' xs
                                                         areMutexesIntersect xs
                               otherwise -> areMutexesIntersect xs
------------------------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------------------------
-- function that's used to extract the global variable/method information.
----------------------------------------------------------------------------------------------------------------------
extractExternalDec :: External_declaration -> CheckM TypeInfoS
-- normal functions always need a require clause, if it doesn't, the it's deemed as thread function.
extractExternalDec (Afunc (OldFunc retTyp decl decs _)) = return [(Method (getNFromDec decl, [], ThreadFun))]
extractExternalDec (Afunc (NewFunc retTyp decl _)) = return [(Method (getNFromDec decl, [], ThreadFun))]
extractExternalDec (Afunc (OldFuncInt decl decs _)) = return [(Method (getNFromDec decl, [], ThreadFun))]
extractExternalDec (Afunc (NewFuncInt decl _)) = return [(Method (getNFromDec decl, [], ThreadFun))]
extractExternalDec (Afunc (OldFuncReqires retTyp decl decs reqs _)) = 
    return [(Method (getNFromDec decl, identToStr reqs, NormalFun))]
extractExternalDec (Afunc (NewFuncReqires retTyp decl reqs _)) = 
    return [(Method (getNFromDec decl, identToStr reqs, NormalFun))]
extractExternalDec (Afunc (OldFuncIntReqires decl decs reqs _)) = 
    return [(Method (getNFromDec decl, identToStr reqs, NormalFun))]
extractExternalDec (Afunc (NewFuncIntReqires decl reqs _)) = 
    return [(Method (getNFromDec decl, identToStr reqs, NormalFun))]
-- aquire the global variable information, default lock = "Self"
extractExternalDec (Global (NoDeclarator typ)) = 
    return [(Var ("no name", ((Basic typ),(Owner_spec TSelf)), ["no name"], 0))]
extractExternalDec (Global (Declarators typ [])) = return []
extractExternalDec (Global (Declarators typ ((OnlyDecl decl):xs))) = 
    do varTypInfoS <- (extractExternalDec (Global (Declarators typ xs)))
       extractVarMutex (getNFromDec decl) typ (Owner_spec TSelf) (extractType (Basic typ) decl) varTypInfoS
-- The global variable can't be assigned to any variables: C's rule
extractExternalDec (Global (Declarators typ ((InitDecl decl _):xs))) = 
    do varTypInfoS <- (extractExternalDec (Global (Declarators typ xs)))
       extractVarMutex (getNFromDec decl) typ (Owner_spec TSelf) (extractType (Basic typ) decl) varTypInfoS
extractExternalDec (Global (NoDeclaratorOwner typ ownerSpec)) = 
    do assert (not (ownerSpec==(Owner_spec TThisThread))) errmsg39
       return [(Var ("no name", ((Basic typ),ownerSpec), ["no name"], 0))]
extractExternalDec (Global (DeclaratorsOwner typ ownerSpec [])) =
    do assert (not (ownerSpec==(Owner_spec TThisThread))) errmsg39
       return []
extractExternalDec (Global (DeclaratorsOwner typ ownerSpec ((OnlyDecl decl):xs))) = 
    do assert (not (ownerSpec==(Owner_spec TThisThread))) errmsg39
       varTypInfoS <- (extractExternalDec (Global (DeclaratorsOwner typ ownerSpec xs)))
       extractVarMutex (getNFromDec decl) typ ownerSpec (extractType (Basic typ) decl) varTypInfoS
extractExternalDec (Global (DeclaratorsOwner typ ownerSpec ((InitDecl decl _):xs))) = 
    do assert (not (ownerSpec==(Owner_spec TThisThread))) errmsg39
       varTypInfoS <- (extractExternalDec (Global (DeclaratorsOwner typ ownerSpec xs)))
       extractVarMutex (getNFromDec decl) typ ownerSpec (extractType (Basic typ) decl) varTypInfoS

----------------------------------------------------------------------------------------------------------------------
-- Policy:
-- 1. Thread functions couldn't be called as normal functions. (must check)
-- 2. Step into the functions and take a look at each local variables, add those variables to the state
-- 3. All the mutex should be globally declared, it can't be the function argument, it cann't be assigned(must check). 
--    Collect the Mutex information. mutex should be ended within one function.
-- 4. All the functions declared local variables in the beginning. we don't allow variables to be declared within 
--    for example the for statement.
-- ** now two pointers should have exactly the same type to be assigned. the refvars of the RHS is assigned to refvars of LHS
--    060515 Liu Hongchao 
-- for example : a = b          
--               LHS must be a pointer
--               RHS must be a pointer of the same type as LHS
--               Then we put the refvars of b to the refvars of a
--               if LHS is not a pointer, RHS has the same type as LHC, we don't do anything. 
-- 5. Turn the argument to be final, that means arguments couldn't be changed after the execution of the function
-- 6. When we type check the function, we also assume that we also have the lock of the pointer type variables.
--    when we check the invocation of this function, we must check all the lock of the actual parameter have been aquired.
----------------------------------------------------------------------------------------------------------------------

----------------------------------------------------------------------------------------------------------------------
-- entry function to check all the statements
----------------------------------------------------------------------------------------------------------------------
typecheckStm :: Stm -> TypeEnv -> CheckM ()
typecheckStm stm typeenv = case stm of
                             LabelS lstm -> typecheckLabelStmt lstm typeenv
                             CompS  cstm -> do typecheckLocalFuncInfo cstm typeenv
                                               typeenv' <- get
                                               assert ((snd' typeenv)==(snd' typeenv')) errmsg19
                             ExprS  estm -> typecheckExprStmt estm typeenv
                             SelS   sstm -> typecheckSelStmt sstm typeenv
                             IterS  istm -> typecheckIterS istm typeenv
                             JumpS  jstm -> typecheckJumpS jstm typeenv
    where
      snd' = (\(a,b,c)-> b)

----------------------------------------------------------------------------------------------------------------------
-- typecheck type information from labeled statements
-- ** temporarily, we don't support switch-case-default statement and label statement
----------------------------------------------------------------------------------------------------------------------
typecheckLabelStmt :: Labeled_stm -> TypeEnv -> CheckM ()
typecheckLabelStmt (SlabelOne id stms) typeenv = fail errmsg2
typecheckLabelStmt (SlabelTwo _ _) typeenv     = fail errmsg2
typecheckLabelStmt (SlabelThree _) typeenv     = fail errmsg2

----------------------------------------------------------------------------------------------------------------------
-- typecheck type information from expression statements
-- expression statements also contains function calls.
----------------------------------------------------------------------------------------------------------------------
typecheckExprStmt :: Expression_stm -> TypeEnv -> CheckM ()
typecheckExprStmt SexprOne typeenv = return ()
typecheckExprStmt (SexprTwo exp) typeenv  = typecheckExpr exp typeenv

typecheckExprs :: [Exp] -> TypeEnv -> CheckM ()
typecheckExprs [] typeenv     = return ()
typecheckExprs (x:xs) typeenv = do typecheckExpr x typeenv
                                   typeenv' <- get
                                   typecheckExprs xs typeenv'

----------------------------------------------------------------------------------------------------------------------
-- typecheck the expression
----------------------------------------------------------------------------------------------------------------------
typecheckExpr :: Exp -> TypeEnv -> CheckM ()
typecheckExpr exp typeenv = case exp of
                              EMutexLockProt exps idents -> do assert (length exps==1) errmsg16
                                                               typp <- getExpType 0 (exps!!0)
                                                               typeB <- isTypeEqual2 typp ((Ptr (Basic [Type TPthMtxT])), True)
                                                               assert typeB errmsg15
                                                               varN <- getExpVarNam (exps!!0)
                                                               -- Check whether the variables mutex protects are declared
                                                               areDeclared (map (\(Ident x)->x) idents)
                                                               updateMutexLocks varN idents
                                                               addLockSet varN idents
                              EMutexLock exps            -> do assert (length exps==1) errmsg16
                                                               typp  <- getExpType 0 (exps!!0)
                                                               typeB <- isTypeEqual2 typp ((Ptr (Basic [Type TPthMtxT])), True)
                                                               assert typeB errmsg15
                                                               return ()
                              EMutexUnLock exps          -> do assert (length exps==1) errmsg16
                                                               typp  <- getExpType 0 (exps!!0)
                                                               typeB <- isTypeEqual2 typp ((Ptr (Basic [Type TPthMtxT])), True)
                                                               assert typeB errmsg15
                                                               mutN <- getExpVarNam $ exps!!0
                                                               removeLockSet mutN
                              EThreadCreat exps          -> do assert (length exps==4) errmsg23
                                                               typp1  <- getExpType 0 (exps!!0)
                                                               typeB1 <- isTypeEqual2 typp1 (((Ptr (Basic [Type TPthT]))),True)
                                                               assert typeB1 errmsg23  --first parameter type assertion
                                                               typp2  <- getExpType 0 (exps!!1)
                                                               typeB2 <- isTypeEqual2 typp2 (((Ptr (Basic [Type TPthAttrS]))),True)
                                                               assert typeB2 errmsg24
                                                               funcT <- getFunctionType (exps!!2)
                                                               assert (funcT==ThreadFun) errmsg25
                                                               oneB  <- isExponeThread (exps!!3) 
                                                               -- can't be oneThread
                                                               assert (not oneB) errmsg26  
                                                               thisB <- isExpthisThread (exps!!3)   
                                                               -- can't be thisThread
                                                               assert (not thisB) errmsg27 
                              Ecomma e1 e2               -> typecheckPara2 e1 e2 typeenv
                              -- assignment is relatively complicated
                              -- ** NOTICE: maybe we need to check the accessibility here, or we check later
                              Eassign e1 Assign e2       -> do typecheckPara2 e1 e2 typeenv
                                                               --first we check whether e1 and e2 are ok
                                                               --then we check whether they satisfy the 
                                                               --requirement of assignment expression
                                                               isMB <- isMutex e1 --can't be mutex
                                                               assert isMB errmsg20
                                                               owner1 <- getExpOwner e1
                                                               owner2 <- getExpOwner e2
                                                               ownerB <- isOwnerEqual owner1 owner2 --owner equal
                                                               if ownerB
                                                                  then do typp1 <- getExpType 0 e1
                                                                          typp2 <- getExpType 0 e2
                                                                          typeB <- isTypeEqual2 typp1 typp2 -- type equal
                                                                          if typeB
                                                                             then do varN1 <- getExpVarNam e1
                                                                                     typecheckAssignExp varN1 e2
                                                                                     return ()
                                                                             else return ()
                                                                   else return ()
                              Econdition e1 e2 e3        -> typecheckPara3 e1 e2 e3 typeenv
                              Elor e1 e2                 -> typecheckPara2 e1 e2 typeenv
                              Eland e1 e2                -> typecheckPara2 e1 e2 typeenv
                              Ebitor e1 e2               -> typecheckPara2 e1 e2 typeenv
                              Ebitexor e1 e2             -> typecheckPara2 e1 e2 typeenv
                              Ebitand e1 e2              -> typecheckPara2 e1 e2 typeenv
                              Eeq e1 e2                  -> typecheckPara2 e1 e2 typeenv
                              Eneq e1 e2                 -> typecheckPara2 e1 e2 typeenv
                              Elthen e1 e2               -> typecheckPara2 e1 e2 typeenv
                              Egrthen e1 e2              -> typecheckPara2 e1 e2 typeenv
                              Ele e1 e2                  -> typecheckPara2 e1 e2 typeenv
                              Ege e1 e2                  -> typecheckPara2 e1 e2 typeenv
                              Eleft e1 e2                -> typecheckPara2 e1 e2 typeenv
                              Eright e1 e2               -> typecheckPara2 e1 e2 typeenv
                              Eplus e1 e2                -> typecheckPara2 e1 e2 typeenv
                              Eminus e1 e2               -> typecheckPara2 e1 e2 typeenv
                              Etimes e1 e2               -> typecheckPara2 e1 e2 typeenv
                              Ediv e1 e2                 -> typecheckPara2 e1 e2 typeenv
                              Emod e1 e2                 -> typecheckPara2 e1 e2 typeenv
                              Etypeconv tnam e           -> do typecheckExpr e typeenv  --ignore the type convertion
                                                               return ()
                              Epreinc e                  -> do typecheckExpr e typeenv
                                                               return ()
                              Epredec e                  -> do typecheckExpr e typeenv
                                                               return ()
                              Epreop uoper e             -> do typecheckExpr e typeenv
                                                               return ()
                              Ebytesexpr e               -> do typecheckExpr e typeenv
                                                               return ()
                              Ebytestype tnam            -> return ()  --ignore it
                              Earray e1 e2               -> fail errmsg9
                              Efunk e1                   -> do metN     <- getExpVarNam e1   --requres statement variable ok
                                                               reqvars  <- getFunctionRequires metN
                                                               (typeinfos, locks, _) <- get
                                                               reqvarsReq <- getVarsRef reqvars typeinfos
                                                               areAccessible reqvarsReq 
                                                               return ()
                              Efunkpar e1 exs            -> do metN     <- getExpVarNam e1   --requres statement variable ok
                                                               reqvars  <- getFunctionRequires metN
                                                               (typeinfos, locks, _) <- get
                                                               reqvarsReq <- getVarsRef reqvars typeinfos
                                                               areAccessible reqvarsReq 
                                                               -- owners of parameters can't be oneThread
                                                               isExpSOneThread exs  
                                                               -- all the variables should be owned
                                                               typecheckExprs exs typeenv 
                                                               return ()
                              -- ** Notice: maybe we need to transform the variables to our name (i.e.funN#varN)
                              Eselect e (Ident str)      -> do typecheckExpr e typeenv
                                                               return ()
                              Epoint e (Ident str)       -> do typecheckExpr e typeenv
                                                               return ()
                              Epostinc e                 -> do typecheckExpr e typeenv
                                                               return ()
                              Epostdec e                 -> do typecheckExpr e typeenv
                                                               return ()
                              Evar (Ident str)           -> do bAcc <- (isAccessible str) 
                                                               if bAcc
                                                                  then return ()
                                                                  else if str=="NULL"
                                                                       then return ()
                                                                       else fail $ errmsg10 str
                              Econst cons                -> return ()
                              Estring str                -> return ()
                              otherwise                  -> return ()  -- I guess except assignment, we all return ()
    where
      typecheckPara2 :: Exp -> Exp -> TypeEnv -> CheckM ()
      typecheckPara2 e1 e2 typeenv = do typecheckExpr e1 typeenv
                                        typeenv' <- get
                                        typecheckExpr e2 typeenv'
                                        return ()
      typecheckPara3 e1 e2 e3 typeenv = do typecheckExpr e1 typeenv
                                           typeenv' <- get
                                           typecheckExpr e2 typeenv'
                                           typeenv'' <- get
                                           typecheckExpr e3 typeenv''
                                           return ()

----------------------------------------------------------------------------------------------------------------------
-- extract type information from selection statements
----------------------------------------------------------------------------------------------------------------------
typecheckSelStmt :: Selection_stm -> TypeEnv -> CheckM ()
typecheckSelStmt (SselOne exp stm) typeenv = do put typeenv
                                                typecheckExpr exp typeenv
                                                typeenv' <- get
                                                typecheckStm stm typeenv
                                                return ()
typecheckSelStmt (SselTwo exp stm1 stm2) typeenv = do put typeenv
                                                      typecheckExpr exp typeenv
                                                      typeenv' <- get
                                                      typecheckStm stm1 typeenv'
                                                      typeenv1 <- get
                                                      typecheckStm stm2 typeenv'
                                                      typeenv2 <- get
                                                      typeenvF <- typeenvMerge typeenv1 typeenv2
                                                      put typeenvF
                                                      return ()
typecheckSelStmt (SselThree exp stm) typeenv = fail errmsg2

----------------------------------------------------------------------------------------------------------------------
-- extract type information from iteration statements
----------------------------------------------------------------------------------------------------------------------
typecheckIterS :: Iter_stm -> TypeEnv -> CheckM ()
typecheckIterS (SiterOne exp stm) typeenv = do typecheckExpr exp typeenv
                                               typeenv' <- get
                                               typecheckStm stm typeenv'
                                               return ()
typecheckIterS (SiterTwo stm exp) typeenv = do typecheckStm stm typeenv
                                               typeenv' <- get
                                               typecheckExpr exp typeenv'
                                               return ()
-- ** maybe in for loops, things might also be screwed up
typecheckIterS (SiterThree exps1 exps2 stm) typeenv = do typecheckExprStmt exps1 typeenv
                                                         typeenv' <- get
                                                         typecheckExprStmt exps2 typeenv'
                                                         typeenv'' <- get
                                                         typecheckStm stm typeenv''
                                                         return ()
typecheckIterS (SiterFour exps1 exps2 exp stm) typeenv = do typecheckExprStmt exps1 typeenv
                                                            typeenv' <- get
                                                            typecheckExprStmt exps2 typeenv'
                                                            typeenv'' <- get
                                                            typecheckExpr exp typeenv''
                                                            typeenv''' <- get
                                                            typecheckStm stm typeenv'''
                                                            return ()

----------------------------------------------------------------------------------------------------------------------
-- extract type information from jump statements
----------------------------------------------------------------------------------------------------------------------
typecheckJumpS :: Jump_stm -> TypeEnv -> CheckM ()
typecheckJumpS (SjumpOne id) typeenv   = fail errmsg12
typecheckJumpS SjumpTwo typeenv        = return ()
typecheckJumpS SjumpThree typeenv      = return ()
typecheckJumpS SjumpFour typeenv       = return ()
typecheckJumpS (SjumpFive exp) typeenv = do typecheckExpr exp typeenv
                                            return ()

----------------------------------------------------------------------------------------------------------------------
-- merge two typeenv after the if statement
-- because we don't allow declaration of new variables, and the mutex should end within 1 composition statement, so
-- after the two branches, what we should use as an approximation is:
-- 1. the refvars of every variable (union)
-- 2. the protected variables of every mutex (union)
-- 3. access time
-- the structure of the typeenv shouldn't be changed, that means the elements and their order should be the same.
----------------------------------------------------------------------------------------------------------------------
typeenvMerge :: TypeEnv -> TypeEnv -> CheckM TypeEnv
typeenvMerge (typeinfos1, l1, a) (typeinfos2, l2, a') = do typeinfo <- typeinfoMerge typeinfos1 typeinfos2
                                                           return (typeinfo, l1, a)
    where
      typeinfoMerge :: TypeInfoS -> TypeInfoS -> CheckM TypeInfoS
      typeinfoMerge [] [] = return []
      typeinfoMerge (t1:typeenv1) (t2:typeenv2) = do t  <- mergeTypeinfo t1 t2
                                                     ts <- typeinfoMerge typeenv1 typeenv2
                                                     return (t:ts)
      mergeTypeinfo :: TypeInfo -> TypeInfo -> CheckM TypeInfo
      mergeTypeinfo (Var (varN1, t1, ref1, acctim1)) (Var (varN2, t2, ref2, acctim2)) =
          if varN1/=varN2
             then fail errmsg11
             else return (Var (varN1, t1, nub (ref1++ref2), acctim1))
      mergeTypeinfo mtinf@(Method _) (Method _) = return mtinf
      mergeTypeinfo (Mutex (mutN1, pvars1)) (Mutex (mutN2, pvars2)) =
          if mutN1/=mutN2
             then fail errmsg11
             else return (Mutex (mutN1, nub (pvars1++pvars2)))
      mergeTypeinfo _ _ = fail errmsg11

-- extract type information from local composition statements
extractLocalComp :: Compound_stm -> TypeEnv -> CheckM ()
extractLocalComp ScompOne typeenv = return ()
extractLocalComp (ScompTwo []) typeenv = return ()
extractLocalComp (ScompTwo (x:xs)) typeenv = do put typeenv
                                                typecheckStm x typeenv
                                                typeenv' <- get
                                                extractLocalComp (ScompTwo xs) typeenv'
                                                return ()
extractLocalComp (ScompThree decs) typeenv = fail errmsg1
extractLocalComp (ScompFour decs stms) typeenv = fail errmsg1

----------------------------------------------------------------------------------------------------------------------
-- extract type information from function composition statements, UNDER CONSTRUCTION
-- this is the entry for normal function, before calling this function we should assume 
-- that all variables that're listed in the require statement are all aquired. So does the arguments.
----------------------------------------------------------------------------------------------------------------------
typecheckLocalFuncInfo :: Compound_stm -> TypeEnv -> CheckM ()
typecheckLocalFuncInfo ScompOne typeenv = return ()
typecheckLocalFuncInfo (ScompTwo []) typeenv = return ()
typecheckLocalFuncInfo (ScompTwo (x:xs)) typeenv = do put typeenv 
                                                      typecheckStm x typeenv
                                                      typeenv' <- get
                                                      typecheckLocalFuncInfo (ScompTwo xs) typeenv'
                                                      return ()
-- although in this kind of function, it declares some local variable. but because it never uses them, we can
-- just ignore them
typecheckLocalFuncInfo (ScompThree decs) typeenv = do put typeenv
                                                      return ()
-- in the function definition, since we don't use different spaces, we use a different name for local variables,
-- with the format of "functionName#variable"
typecheckLocalFuncInfo (ScompFour decs stms) typeenv@(typeinfos, locks, checkingt) = 
    do put typeenv 
       typeinfos' <- extractLocalDecsInfo decs typeenv
       put ((typeinfos++typeinfos'),locks,checkingt)
       typecheckLocalFuncInfo (ScompTwo stms) ((typeinfos++typeinfos'),locks,checkingt)

-- help function for extractLocalDecsInfo 
decInitHelper :: Initializer -> TypeEnv -> VarName -> TypeP -> Owner -> TypeInfo -> CheckM TypeInfoS
decInitHelper inlr typeenv vn typp owner typeinfo@(Var (vn', (typp',(Owner_spec owner')), refs', acct')) =
    case inlr of
      Initexpr e -> do typecheckExpr e typeenv
                       owner1   <- getExpOwner e
                       ownerB   <- isOwnerEqual owner1 (owner, True)
                       if ownerB
                          then do typp1 <- getExpType 0 e
                                  typeB <- isTypeEqual2 typp1 (typp,True)
                                  if typeB
                                     then do varN1 <- getExpVarNam e
                                             --typecheckAssignExp vn e
                                             refs <- getVarRef varN1 ((\(a,b,c)->a) typeenv)
                                             --(typeinfos,locks) <- get
                                             case typp of
                                               Basic _   -> return [(Var (vn', (typp',(Owner_spec owner')), refs', acct'))]
                                               otherwise -> return [(Var (vn', (typp',(Owner_spec owner')), refs, acct'))]
                                     else do typeenv' <- get
                                             return ((\(a,b,c)->a) typeenv')
                          else return [typeinfo]
      otherwise -> fail errmsg14      

-- extract the local declarations in functions
extractLocalDecsInfo :: [Dec] -> TypeEnv -> CheckM TypeInfoS
extractLocalDecsInfo [] typeenv = return []
extractLocalDecsInfo (x:xs) typeenv =  do typeinfos  <- extractLocalDecInfo x typeenv
                                          typeinfos' <- extractLocalDecsInfo xs typeenv
                                          return $ typeinfos++typeinfos'
    where
      extractLocalDecInfo :: Dec -> TypeEnv -> CheckM TypeInfoS
      extractLocalDecInfo (NoDeclarator typ) typeenv = 
          return [(Var ("no name", ((Basic typ),(Owner_spec TSelf)), ["no name"], 0))]
      extractLocalDecInfo (Declarators typ []) typeenv = return []
      extractLocalDecInfo (Declarators typ ((OnlyDecl decl):xs)) typeenv = 
                          do typinfo   <- extractVar (getNFromDec decl) typ (Owner_spec TSelf) (extractType (Basic typ) decl)
                             typeinfos <- extractLocalDecInfo (Declarators typ xs) typeenv
                             return (typinfo:typeinfos)
      extractLocalDecInfo (Declarators typ ((InitDecl decl inlr):xs)) typeenv = 
                          do typeinfo@(Var (vn, (typp,(Owner_spec owner)), _, _)) <- 
                                 extractVar (getNFromDec decl) typ (Owner_spec TSelf) (extractType (Basic typ) decl)
                             decInitHelper inlr typeenv vn typp owner typeinfo
      extractLocalDecInfo (NoDeclaratorOwner typ ownerSpec) typeenv = 
          do assert (not (ownerSpec==(Owner_spec TOneThread))) $ errmsg41 "no name"
             return [(Var ("no name", ((Basic typ),ownerSpec), ["no name"], 0))]
      extractLocalDecInfo (DeclaratorsOwner typ ownerSpec []) typeenv = return []
      extractLocalDecInfo (DeclaratorsOwner typ ownerSpec ((OnlyDecl decl):xs)) typeenv =
                          do assert (not (ownerSpec==(Owner_spec TOneThread))) $ errmsg41 $ getNFromDec decl
                             typinfo   <- extractVar (getNFromDec decl) typ ownerSpec (extractType (Basic typ) decl)
                             typeinfos <- extractLocalDecInfo (DeclaratorsOwner typ ownerSpec xs) typeenv
                             return (typinfo:typeinfos) 
      extractLocalDecInfo (DeclaratorsOwner typ ownerSpec ((InitDecl decl inlr):xs)) typeenv =
                          do assert (not (ownerSpec==(Owner_spec TOneThread))) $ errmsg41 $ getNFromDec decl
                             typeinfo@(Var (vn, (typp,(Owner_spec owner)), _, _)) <- 
                                 extractVar (getNFromDec decl) typ ownerSpec (extractType (Basic typ) decl)
                             decInitHelper inlr typeenv vn typp owner typeinfo


----------------------------------------------------------------------------------------------------------------------
-- what I'm gonna do now:
-- 1. mutex handle: a. must ended within one composition stmt   ...ok
--                  b. must not be defined within function   ...ok
--                  c. collect the variables that it protects   ...ok
--                  d. the sets of the variables that the mutexes protects would never intersect (will be done at last) ..ok
--                  e. it is final variable, which means it could never be assigned   ...ok
-- 2. normal function definition:
--                  a. assume that all the locks in the require clause and arguments are aquired  ...ok
-- 3. thread function definition:
--                  a. the lock should be thisThread only    ...ok
--                  b. variables of thisThread and oneThread couldn't be assigned
--                  c. oneThread variables could add access time, more than 1 times should report an error  ...ok
-- 4. normal function invocation:
--                  a. see whether current lock set is enough for typecheck the invocation   ...ok
--                  b. variables of oneThread couldn't be assigned    ...ok
-- 5. thread function invocation:
--                  a. variables of thisThread and oneThread couldn't be assigned    ...ok
-- 6. Main function:
--                  a. Typecheck both normal functions definition and thread functions definition   ...ok
--                  b. The sets of the variables that the mutexes protects would never intersect (Mutex handle d) ...ok
-- 7. About the form like a.b or a->e, we only check the type of a. if we get "a" then we get a.b or a->e; 
--    the variable of oneThread couldn't be assigned. About adding funtion name before the local variable name
----------------------------------------------------------------------------------------------------------------------


----------------------------------------------------------------------------------------------------------------------
-- get all the parameters and their types of a function, following couple of functions are all help functions to this
----------------------------------------------------------------------------------------------------------------------
getAllParameters :: Declarator -> CheckM [(Type, VarName)]
getAllParameters (BeginPointer _ dirdecl) = do xs <- getAllParametersWH dirdecl
                                               return $ nub xs
getAllParameters (NoPointer dirdecl) = do xs <- getAllParametersWH dirdecl
                                          return $ nub xs

-- getAllParameters work horse
getAllParametersWH :: Direct_declarator -> CheckM [(Type, VarName)]
getAllParametersWH (Name (Ident str)) = fail errmsg33 --return [str]
getAllParametersWH (ParenDecl decl)   = fail errmsg33 -- getAllParameters decl
getAllParametersWH (InnitArray _ _)   = fail errmsg31
getAllParametersWH (Incomplete _)     = fail errmsg31
getAllParametersWH (NewFuncDec dirdecl' paratype) = getAllParametersFromParamType paratype
getAllParametersWH (OldFuncDef dirdecl xs) = fail errmsg32 -- return $ map (\(Ident x)->x) xs   -- temp
getAllParametersWH (OldFuncDec dirdecl) = return []

-- getAllParametersWH work horse
getAllParametersFromParamType :: Parameter_type -> CheckM [(Type, VarName)]
getAllParametersFromParamType (AllSpec paradecls) = getAllParametersFromParaDefs paradecls
getAllParametersFromParamType (More _) = fail errmsg31


getParameterFromDecl :: [Declaration_specifier] -> Declarator -> CheckM (Type, VarName)
getParameterFromDecl t (NoPointer dir_dcl) = return (((Basic t),(Owner_spec TSelf)),(getParaFromDirDecl dir_dcl))
getParameterFromDecl t (BeginPointer Point dir_dcl) = return (((Ptr (Basic t),(Owner_spec TSelf))), (getParaFromDirDecl dir_dcl))
getParameterFromDecl t (BeginPointer (PointQual t') dir_dcl) = return (((Ptr (Basic t)),(Owner_spec TSelf)), (getParaFromDirDecl dir_dcl))
getParameterFromDecl t (BeginPointer (PointPoint p) dir_dcl) = do (t, vnam) <- getParameterFromDecl t (BeginPointer p dir_dcl)
                                                                  return (((Ptr (fst t)),snd t), vnam)
getParameterFromDecl t (BeginPointer (PointQualPoint t' p) dir_dcl) = do (t, vnam) <- getParameterFromDecl t (BeginPointer p dir_dcl)
                                                                         return (((Ptr (fst t)),snd t), vnam)

getParaFromDirDecl :: Direct_declarator -> VarName
getParaFromDirDecl (Name (Ident varnam)) = varnam
getParaFromDirDecl _                     = fail errmsg35

getAllParametersFromParaDecl :: Parameter_declaration -> CheckM [(Type, VarName)] 
getAllParametersFromParaDecl (OnlyType _) = return []
getAllParametersFromParaDecl (TypeAndParam t decl) = do tn <- getParameterFromDecl t decl  --getAllParameters decl
                                                        return [tn]
getAllParametersFromParaDecl (Abstract _ _) = fail errmsg32

getAllParametersFromParaDefs :: Parameter_declarations -> CheckM [(Type, VarName)]
getAllParametersFromParaDefs (ParamDec paradecl) = getAllParametersFromParaDecl paradecl
getAllParametersFromParaDefs (MoreParamDec paradecls paradecl) = do xs <- getAllParametersFromParaDefs paradecls
                                                                    x  <- getAllParametersFromParaDecl paradecl
                                                                    return $ xs++x
----------------------------------------------------------------------------------------------------------------------


----------------------------------------------------------------------------------------------------------------------
-- Before type check the thread function. Update the environmet to let it include all the arguments
----------------------------------------------------------------------------------------------------------------------
updateTypeEnvThreadfunc :: TypeEnv -> [(Type, VarName)] -> TypeEnv
updateTypeEnvThreadfunc (typeinfos,locks, checkingt) nts = ((typeinfos++(map (\(t,n)-> Var (n,t,[n],0)) nts)),[("thisThread",["thisThread"])],ThreadFunc)

-- typecheckThreadFunction work horse
typecheckThreadFunctionWH :: Declarator -> Compound_stm -> CheckM ()
typecheckThreadFunctionWH dtor cstmts = do tn      <- getAllParameters dtor
                                           typeenv <- get
                                           put (updateTypeEnvThreadfunc typeenv tn)
                                           typecheckStm (CompS cstmts) (updateTypeEnvThreadfunc typeenv tn)
                                           typeenv' <- get
                                           typeenv''<- updateMutexOneThreadVarTypeEnv typeenv typeenv'
                                           put typeenv''
                                           return ()

----------------------------------------------------------------------------------------------------------------------
-- typecheck the thread function
-- put thisThread in the typing environment as well as argument variables, if it's a structure, simply put the 
-- name of the structure.
----------------------------------------------------------------------------------------------------------------------
typecheckThreadFunction :: Function_def ->  CheckM ()
typecheckThreadFunction (OldFunc dclr dtor decs cstmts) = typecheckThreadFunctionWH dtor cstmts
typecheckThreadFunction (NewFunc dclr dtor cstmts) = typecheckThreadFunctionWH dtor cstmts
typecheckThreadFunction (OldFuncInt dtor decs cstmts) = typecheckThreadFunctionWH dtor cstmts
typecheckThreadFunction (NewFuncInt dtor cstmts) = typecheckThreadFunctionWH dtor cstmts
typecheckThreadFunction _ = fail errmsg36

----------------------------------------------------------------------------------------------------------------------
-- Before type check the normal function. Update the environmet to let it include all the arguments and variables in 
-- require statement
----------------------------------------------------------------------------------------------------------------------
updateTypeEnvNormalfunc :: TypeEnv -> [(Type, VarName)] -> [Ident] -> TypeEnv
updateTypeEnvNormalfunc (typeinfos, _, checkingt) nts reqs = ((typeinfos++(map (\(t,n)-> Var (n,t,[n],0)) nts)),[("thisThread",["thisThread"]++reqsNs++paraNs)],NormalFunc)
    where
      reqsNs = identToStr reqs
      paraNs = map (\(t,n) -> n) nts

-- typecheckNormalFunction work horse
typecheckNormalFunctionWH :: Declarator -> Compound_stm -> [Ident] -> CheckM ()
typecheckNormalFunctionWH dtor cstmts reqs = do tn      <- getAllParameters dtor
                                                typeenv <- get 
                                                put (updateTypeEnvNormalfunc typeenv tn reqs)
                                                typecheckStm (CompS cstmts) (updateTypeEnvNormalfunc typeenv tn reqs)
                                                typeenv' <- get
                                                typeenv''<- updateMutexOneThreadVarTypeEnv typeenv typeenv'
                                                put typeenv''
                                                return ()

---------------------------------------------------------------------------------------------------------------
-- typecheck the normal function
---------------------------------------------------------------------------------------------------------------
typecheckNormalFunction :: Function_def -> CheckM ()
typecheckNormalFunction (OldFuncReqires dclr dtor decs reqs cstmts) = typecheckNormalFunctionWH dtor cstmts reqs
typecheckNormalFunction (NewFuncReqires dclr dtor reqs cstmts) = typecheckNormalFunctionWH dtor cstmts reqs
typecheckNormalFunction (OldFuncIntReqires dtor decs reqs cstmts) = typecheckNormalFunctionWH dtor cstmts reqs
typecheckNormalFunction (NewFuncIntReqires dtor reqs cstmts) = typecheckNormalFunctionWH dtor cstmts reqs
typecheckNormalFunction _ = fail errmsg37

-- Get the method definition by method name
extractFunction :: MethodName -> Program -> CheckM Function_def
extractFunction mname (Progr (x:xs)) = case x of
                                         Afunc (NewFuncReqires retTyp decl reqs x) -> 
                                             if mname == (getNFromDec decl)
                                                then return (NewFuncReqires retTyp decl reqs x)
                                                else extractFunction mname (Progr xs)
                                         Afunc (OldFuncReqires dclr dtor decs reqs cstmts) ->
                                             if mname == (getNFromDec dtor)
                                                then return (OldFuncReqires dclr dtor decs reqs cstmts)
                                                else extractFunction mname (Progr xs)
                                         Afunc (OldFuncIntReqires dtor decs reqs cstmts) ->
                                             if mname == (getNFromDec dtor)
                                                then return (OldFuncIntReqires dtor decs reqs cstmts)
                                                else extractFunction mname (Progr xs)
                                         Afunc (NewFuncIntReqires dtor reqs cstmts) -> 
                                               if mname == (getNFromDec dtor)
                                                  then return (NewFuncIntReqires dtor reqs cstmts)
                                                  else extractFunction mname (Progr xs)
                                         Afunc (OldFunc dclr dtor decs cstmts) ->
                                             if mname == (getNFromDec dtor)
                                                then return (OldFunc dclr dtor decs cstmts)
                                                else extractFunction mname (Progr xs)
                                         Afunc (NewFunc dclr dtor cstmts) -> 
                                             if mname == (getNFromDec dtor)
                                                then return (NewFunc dclr dtor cstmts)
                                                else extractFunction mname (Progr xs)
                                         Afunc (OldFuncInt dtor decs cstmts) ->
                                             if mname == (getNFromDec dtor)
                                                then return (OldFuncInt dtor decs cstmts)
                                                else extractFunction mname (Progr xs)
                                         Afunc (NewFuncInt dtor cstmts) ->
                                             if mname == (getNFromDec dtor)
                                                then return (NewFuncInt dtor cstmts)
                                                else extractFunction mname (Progr xs)
                                         otherwise -> extractFunction mname (Progr xs)
extractFunction mname (Progr []) = fail "No such function"

-- typecheckFunctions work horse
typecheckFunctionsWH :: Function_def -> CheckM ()
typecheckFunctionsWH func@(OldFunc _ _ _ _)           = typecheckThreadFunction func
typecheckFunctionsWH func@(NewFunc _ _ _)             = typecheckThreadFunction func
typecheckFunctionsWH func@(OldFuncInt _ _ _)          = typecheckThreadFunction func
typecheckFunctionsWH func@(NewFuncInt _ _)            = typecheckThreadFunction func
typecheckFunctionsWH func@(OldFuncReqires _ _ _ _ _)  = typecheckNormalFunction func
typecheckFunctionsWH func@(NewFuncReqires _ _ _ _)   = typecheckNormalFunction func
typecheckFunctionsWH func@(OldFuncIntReqires _ _ _ _) = typecheckNormalFunction func
typecheckFunctionsWH func@(NewFuncIntReqires _ _ _)   = typecheckNormalFunction func

-----------------------------------------------------------------------------------------------------------------
-- The entry function to type check all the methods definition
-- about the structure, we only care about the name of the structure, instead of fields
-----------------------------------------------------------------------------------------------------------------
typecheckFunctions :: Program -> CheckM ()
typecheckFunctions (Progr [])     = return ()
typecheckFunctions (Progr (x:xs)) = case x of
                                      Afunc f    -> do typecheckFunctionsWH f
                                                       typecheckFunctions (Progr xs)
                                      Global dec -> typecheckFunctions (Progr xs)

-- The entry function to type check the program
typecheckProgram :: Program -> CheckM ()
typecheckProgram p = do typeinfos <- extractEnv p
                        put (typeinfos,[],NoFun)
                        checkRequiresAreGlobals typeinfos
                        typecheckFunctions p
                        (typeinfos',locks', checkingt) <- get
                        areMutexesIntersect typeinfos'

-- program checker
programChecker :: String -> IO ()
programChecker filnam = do pro <- readFile "thread2.c"
                           let ts = myLexer pro in case pProgram ts of
                                                     Bad s   -> do putStrLn "\nParse        Failed...\n"
                                                     Ok tree -> 
                                                         do --putStrLn $ show tree
                                                            case (runStateT (typecheckProgram tree) ([],[],NoFun)) of 
                                                              Left err -> putStrLn err
                                                              Right s  -> putStrLn $ show s



------------------------------------------------------------------------------------------------------------
-- TEST functions 
------------------------------------------------------------------------------------------------------------

-- Convert (Check m) to (IO ())
convert :: (Show m) => CheckM m -> IO ()
convert m = case runStateT m ([],[],NoFun) of
              Left err -> putStrLn err
              Right r  -> putStrLn $ show $ fst r

--test typecheckNormalFunctiontest
typecheckNormalFunctiontest :: Function_def -> CheckM TypeEnv
typecheckNormalFunctiontest (OldFuncReqires dclr dtor decs reqs cstmts) = typecheckNormalFunctionWHtest dtor cstmts reqs
typecheckNormalFunctiontest (NewFuncReqires dclr dtor reqs cstmts) = typecheckNormalFunctionWHtest dtor cstmts reqs
typecheckNormalFunctiontest (OldFuncIntReqires dtor decs reqs cstmts) = typecheckNormalFunctionWHtest dtor cstmts reqs
typecheckNormalFunctiontest (NewFuncIntReqires dtor reqs cstmts) = typecheckNormalFunctionWHtest dtor cstmts reqs
typecheckNormalFunctiontest _ = fail errmsg37

typecheckNormalFunctionWHtest :: Declarator -> Compound_stm -> [Ident] -> CheckM TypeEnv
typecheckNormalFunctionWHtest dtor cstmts reqs = do tn      <- getAllParameters dtor
                                                    typeenv <- get 
                                                    put (updateTypeEnvNormalfunc typeenv tn reqs)
                                                    typecheckStm (CompS cstmts) (updateTypeEnvNormalfunc typeenv tn reqs)
                                                    get

--test typecheckNormalFunction
testTypecheckNormalFunction :: IO ()
testTypecheckNormalFunction = do pro <- readFile "thread2.c"
                                 let ts = myLexer pro in case pProgram ts of
                                                           Bad s   -> do putStrLn "\nParse        Failed...\n"
                                                           Ok tree -> do convert $ testNormalFunction tree
    where
      testNormalFunction :: Program -> CheckM TypeEnv
      testNormalFunction program = do tinfos <- extractEnv program
                                      put (tinfos, [], NormalFunc)
                                      checkRequiresAreGlobals tinfos
                                      f <- extractFunction "normal_function" program
                                      typecheckNormalFunctiontest f
                                      get
      testGetFunctionRequiresTT :: Program -> CheckM Bool --ReqireVars
      testGetFunctionRequiresTT program = do tinfos <- extractEnv program                                            
                                             put (tinfos, [], NormalFunc)
                                             checkRequiresAreGlobals tinfos
                                             refvars <- testGetFunctionRequires "fun" --"normal_function"
                                             areAccessible refvars
      testtypeEnvMerge :: TypeEnv -> TypeEnv -> CheckM TypeEnv
      testtypeEnvMerge t1 t2 = typeenvMerge t1 t2

-- test getFunctionRequires
testGetFunctionRequires :: MethodName -> CheckM ReqireVars
testGetFunctionRequires metN = do reqvars <- getFunctionRequires metN
                                  (typeinfos, locks, checkingt) <- get
                                  getVarsRef reqvars typeinfos
         
-- test isAccessible
testIsAccessible :: Function_def -> VarName -> IO ()
testIsAccessible (NewFuncReqires dclr dtor reqs cstmts) varn = 
    do pro <- readFile "thread2.c"
       let ts = myLexer pro in case pProgram ts of
                                 Bad s   -> do putStrLn "\nParse        Failed...\n"
                                 Ok tree -> convert $ do tinfos <- extractEnv tree
                                                         put (tinfos, [], NoFun)
                                                         checkRequiresAreGlobals tinfos
                                                         tn <- getAllParameters dtor
                                                         typeenv <- get
                                                         put $ updateTypeEnvNormalfunc typeenv tn reqs
                                                         case cstmts of
                                                           (ScompFour decs stms) -> 
                                                               do typeenv'@(typeinfos, locks, checkingt) <- get
                                                                  typeinfos' <- extractLocalDecsInfo decs typeenv'
                                                                  put ((typeinfos++typeinfos'),locks,checkingt)
                                                           otherwise -> return ()
                                                         get

-- test typecheckProgram 
typecheckProgramtest :: Program -> CheckM TypeEnv
typecheckProgramtest p = do typeinfos <- extractEnv p
                            put (typeinfos,[],NoFun)
                            checkRequiresAreGlobals typeinfos
                            typecheckFunctions p
                            get

-- test typecheckProgram 
testtypecheckProgram :: IO ()
testtypecheckProgram = do pro <- readFile "thread2.c"
                          let ts = myLexer pro in case pProgram ts of
                                                    Bad s   -> do putStrLn "\nParse        Failed...\n"
                                                    Ok tree -> do convert $ typecheckProgramtest tree
-----------------------------------------------------------------------------------------------------------------

