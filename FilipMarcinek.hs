{-# LANGUAGE Safe #-}

module FilipMarcinek (typecheck, eval) where

import AST
import DataTypes
import qualified Data.Map as DM


data Val p =
    VNum Integer
    | VBool Bool
    | VUnit ()
    | VPair (Val p,Val p)
    | VList [Val p]
    | VLambda ((Env (Val p)), (Var, (Expr p)))
    | VFun ([FunctionDef p], (Var, (Expr p)))

type Env a = DM.Map Var a
-- type Func_Env a = DM.Map FSym a
-- type Function = (Val -> Maybe Val)

type Err p = (p, ErrKind)
data ErrKind =
    EUndefinedVariable Var
    | ETypeMismatch Type Type
    | EIfMismatch Type Type
    | EWrongFuncDef ErrKind
    | EUndefinedFunction Var
    | EIsNotPair Type
    | EIsNotList Type
    | EIsNotFunc Type
    | EListWithoutType
    | EWrongInput


instance Show ErrKind where
  show (EUndefinedVariable x) =
    "Undefined variable " ++ show x ++ "."
  show (ETypeMismatch t1 t2)  =
    "Type mismatch: expected " ++ show t1 ++ " but received " ++ show t2 ++ "."
  show (EIfMismatch t1 t2)    =
    "Type mismatch in the branches of an if or match: " ++ show t1 ++ " and " ++ show t2 ++ "."
  show (EWrongFuncDef t)      =
    "Wrong function definiton: " ++ show t
  show (EUndefinedFunction f) =
    "Undefined function named: " ++ show f ++ "."
  show (EIsNotPair t)         =
    "Type " ++ show t ++ " is not a type of pair."
  show (EIsNotList t)         =
    "Type " ++ show t ++ " is not a type of list."
  show (EIsNotFunc t)         =
    "Type " ++ show t ++ " is not a type of function."
  show (EListWithoutType)     =
    "Probably you forgot write word 'list' after expression:   []:'type'  ."
  show (EWrongInput)          =
    "All variables and functions must have different names!"


-- WIELKIE TYPOWANIE -----------------------------------------------------------

infer_type :: Env Type -> Expr p -> Either (Err p) Type

-- ZMIENNE
infer_type env (EVar p x) =
    case DM.lookup x env of
        Just t -> Right t
        Nothing -> Left (p, EUndefinedVariable x)

-- STAŁE
infer_type _ (ENum _ _) = Right TInt

infer_type _ (EBool _ _) = Right TBool

infer_type _ (EUnit _) = Right TUnit

-- LISTA PUSTA
infer_type _ (ENil p typ) =
    case typ of
        (TList t) -> Right (TList t)
        _ -> Left (p, EListWithoutType)


-- OPERATORY UNARNE
infer_type env (EUnary _ op expr) =
    case check_type env expr typ of
        Just err -> Left err
        Nothing -> Right res_type
        where (typ, res_type) = unaryOpType op

-- OPERATORY BINARNE
infer_type env (EBinary _ op expr1 expr2) =
    case check_type env expr1 typ1 of
        Just err -> Left err
        Nothing ->
            case check_type env expr2 typ2 of
                Just err -> Left err
                Nothing -> Right res_type
    where (typ1, typ2, res_type) = binaryOpType op

-- WYRAŻENIE LET
infer_type env (ELet p x expr1 expr2) =
    case infer_type env expr1 of
        Left err -> Left err
        Right t1 -> infer_type env' expr2
          where
              env' = DM.insert x t1 env

-- WYRAŻENIE WARUNKOWE IF ELSE
infer_type env (EIf p expr1 expr2 expr3) =
    case check_type env expr1 TBool of
        Just err -> Left err
        Nothing ->
            case equal_types p typ1 typ2 of
                Left err -> Left err
                Right t -> Right t
            where
                typ1 = infer_type env expr2
                typ2 = infer_type env expr3

-- APLIKACJA FUNKCJI
infer_type env (EApp p f_expr arg_expr) =
    case infer_type env f_expr of
        Left err -> Left err
        Right f_type ->
            case f_type of
                TArrow arg_type res_type ->
                    case check_type env arg_expr arg_type of
                        Just err -> Left err
                        Nothing -> Right res_type
                t -> Left (p, EIsNotFunc t)

-- WYRAŻENIE LAMBDA
infer_type env (EFn p var t1 expr) =
    case infer_type env' expr of
        Left err -> Left err
        Right t2 -> Right (TArrow t1 t2)
    where
        env' = DM.insert var t1 env


-- PARA
infer_type env (EPair p expr1 expr2) =
    case infer_type env expr1 of
        Left err -> Left err
        Right t1 ->
            case infer_type env expr2 of
                Left err -> Left err
                Right t2 -> Right (TPair t1 t2)

-- PROJEKCJE PARY
infer_type env (EFst p expr) =
    case infer_type env expr of
        Left err -> Left err
        Right (TPair t1 _) -> Right t1
        Right t -> Left (p, EIsNotPair t)

infer_type env (ESnd p expr) =
    case infer_type env expr of
        Left err -> Left err
        Right (TPair _ t2) -> Right t2
        Right t -> Left (p, EIsNotPair t)

-- TWORZENIE LISTY
infer_type env (ECons p expr1 expr2) =
    case infer_type env expr2 of
        Left err -> Left err
        Right (TList typ) ->
            case check_type env expr1 typ of
                Just err -> Left err
                Nothing -> Right (TList typ)
        Right t -> Left (p, EIsNotList t)

-- WZORZEC MATCH
infer_type env (EMatchL p expr patt1 (var1, var2, patt2)) =
    case infer_type env expr of
        Left err -> Left err
        Right (TList t1) ->
            equal_types p typ1 typ2
            where
                typ1 = infer_type env patt1
                typ2 = infer_type env' patt2
                env' = DM.insert var1 t1 (DM.insert var2 (TList t1) env)
        Right t2 -> Left (p, EIsNotList t2)


-- SPRAWDZA, CZY TYPY SĄ TAKIE SAME
equal_types :: p -> Either (Err p) Type -> Either (Err p) Type -> Either (Err p) Type

equal_types _ (Left err) _ = (Left err)
equal_types _ _ (Left err) = (Left err)
equal_types p (Right typ1) (Right typ2) =
    if typ1 == typ2 then Right typ1
        else Left (p, EIfMismatch typ1 typ2)

-- FUNKCJE GRUPUJĄCE OPERATORY
unaryOpType :: UnaryOperator -> (Type, Type)
unaryOpType UNot = (TBool, TBool)
unaryOpType UNeg = (TInt,  TInt)

binaryOpType :: BinaryOperator -> (Type, Type, Type)
binaryOpType op = case op of
    BAnd -> type_bool
    BOr  -> type_bool
    BEq  -> type_compare
    BNeq -> type_compare
    BLt  -> type_compare
    BLe  -> type_compare
    BGt  -> type_compare
    BGe  -> type_compare
    BAdd -> type_arith
    BSub -> type_arith
    BMul -> type_arith
    BDiv -> type_arith
    BMod -> type_arith
    where type_bool = (TBool, TBool, TBool)
          type_compare = (TInt,  TInt,  TBool)
          type_arith = (TInt,  TInt,  TInt)

-- SPRAWDZA, CZY WYRAŻENIE MA DANY TYP
check_type :: Env Type -> Expr p -> Type -> Maybe (Err p)

check_type env expr typ =
    case infer_type env expr of
        Left err -> Just err
        Right typ2 ->
            if typ == typ2 then Nothing
              else Just (getData expr, ETypeMismatch typ2 typ)

-- TWORZY ŚRODOWISKO POCZĄTKOWE ZE ZMIENNYCH W INPUT
env_init_type :: [Var] -> Env Type -> Maybe (Env Type)

env_init_type [] env_partial = Just env_partial
env_init_type (h:list) env_partial =
    case DM.lookup h env_partial of
        Just t -> Nothing
        Nothing ->
            env_init_type list new_env
            where
                new_env = DM.insert h TInt env_partial


-- FUNKCJA POMOCNICZA DO SPRAWDZANIA POPRAWNOŚCI PROGRAMOWYCH FUNKCJI
preprocessor :: [FunctionDef p] -> Env Type -> Env Type

preprocessor [] env_partial = env_partial
preprocessor (h:list) env_partial =
    preprocessor list (DM.insert func_name func_types env_partial)
    where
        func_name = funcName h
        func_types = (TArrow (funcArgType h) (funcResType h))

-- FUNKCJA SPRAWDZAJĄCA POPRAWNOŚĆ PROGRAMOWYCH FUNKCJI
init_func_check :: [FunctionDef p] -> Env Type -> Maybe (Err p)

init_func_check [] _ = Nothing
init_func_check (h:defs) f_env =
    case check_type env expr typ of
        Just err -> Just (p, EWrongFuncDef $ snd err)
        Nothing -> init_func_check defs f_env
    where
      expr = funcBody h
      env = DM.insert (funcArg h) (funcArgType h) f_env
      typ = funcResType h
      p = funcPos h


-- TYPECHECK-----------------------------------

typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p

typecheck fs vars body =
    case init_func_check fs f_env of
        Just (p, err) -> Error p $ show err
        Nothing ->
            case check_type env body TInt of
                Just (p, err) -> Error p $ show err
                Nothing -> Ok
    where
        f_env = preprocessor fs DM.empty
        Just env = env_init_type vars f_env


-- EVAL ---------------------------------------

eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult

eval fs vars body =
    case evaluation env body of
        Just (VNum n) -> Value n
        Nothing -> RuntimeError
    where
        f_env = make_func_env fs
        env = env_init_eval vars f_env


-- FUNKCJA INICJUJĄCA ŚRODOWISKO FUNKCJI Z PROGRAMU
make_func_env :: [FunctionDef p] -> Env (Val p)
make_func_env f_defs = make_func_env' f_defs f_defs DM.empty

make_func_env' :: [FunctionDef p] -> [FunctionDef p]-> Env (Val p) -> Env (Val p)
make_func_env' [] _ env_partial = env_partial
make_func_env' (h:fs) f_defs env_partial =
    make_func_env' fs f_defs (DM.insert f_name f_closure env_partial)
    where
        f_name = funcName h
        f_closure = VFun (f_defs, (funcArg h, funcBody h))


-- FUNKCJA INICJUJĄCA ŚRODOWISKO ZMIENNYCH Z INPUT
env_init_eval :: [(Var, Integer)] -> Env (Val p) -> Env (Val p)
env_init_eval [] env_partial = env_partial
env_init_eval (h:list) env_partial =
    env_init_eval list (DM.insert var (VNum value) env_partial)
    where
        var = fst h
        value = snd h


-- POMOCNICZA FUNKCJA EWALUUJĄCA
evaluation :: Env (Val p) -> Expr p -> Maybe (Val p)

-- EWALUACJA STAŁYCH

evaluation _ (ENum _ n) = Just $ VNum n

evaluation _ (EBool _ bool) = Just $ VBool bool

evaluation _ (EUnit _) = Just $ VUnit ()

evaluation _ (ENil _ _) = Just $ VList []

-- ZMIENNA
evaluation env (EVar _ var) = DM.lookup var env

-- OPERATORY UNARNE
evaluation env (EUnary _ op expr) =
  case evaluation env expr of
    Nothing -> Nothing
    Just n -> evalOpUnary op n

-- OPERATORY BINARNE
evaluation env (EBinary _ op expr1 expr2) =
    case evaluation env expr1 of
      Nothing -> Nothing
      Just n1 ->
          case evaluation env expr2 of
              Nothing -> Nothing
              Just n2 -> evalOpBinary op n1 n2

-- WYRAŻENIE LET
evaluation env (ELet _ var expr1 expr2) =
    case evaluation env expr1 of
      Nothing -> Nothing
      Just n ->
          evaluation env' expr2
          where env' = DM.insert var n env

-- WYRAŻENIE WARUNKOWE IF ELSE
evaluation env (EIf _ expr1 expr2 expr3) =
    case evaluation env expr1 of
        Nothing -> Nothing
        Just (VBool True) -> evaluation env expr2
        Just (VBool False) -> evaluation env expr3

-- APLIKACJA FUNKCJI
evaluation env (EApp _ expr1 expr2) =
    case evaluation env expr2 of
        Nothing -> Nothing
        Just v ->
            case evaluation env expr1 of
                Nothing -> Nothing
                Just (VLambda (env', (x, expr'))) ->
                    evaluation new_env expr'
                    where
                      new_env = DM.insert x v env'
                Just (VFun (f_defs, (x, expr'))) ->
                    evaluation new_env expr'
                    where
                      f_env = make_func_env f_defs
                      new_env = DM.insert x v f_env

-- LAMBDA-ABSTRAKCJA
evaluation env (EFn _ var _ expr) = Just $ VLambda $ (env, (var, expr))

-- PARA
evaluation env (EPair _ expr1 expr2) =
    case (expr1', expr2') of
        (Just v1, Just v2) -> Just $ VPair $ (v1, v2)
        _ -> Nothing
    where
        expr1' = evaluation env expr1
        expr2' = evaluation env expr2

-- PROJEKCJE PARY
evaluation env (EFst _ expr) =
    case evaluation env expr of
        Nothing -> Nothing
        Just (VPair (v1, v2)) -> Just v1

evaluation env (ESnd _ expr) =
    case evaluation env expr of
        Nothing -> Nothing
        Just (VPair (v1, v2)) -> Just v2

-- TWORZENIE LISTY
evaluation env (ECons _ expr1 expr2) =
    case evaluation env expr1 of
        Nothing -> Nothing
        Just h ->
            case evaluation env expr2 of
                Nothing -> Nothing
                Just (VList list) ->
                    consList h list

-- WZORZEC MATCH
evaluation env (EMatchL _ expr1 patt1 (var1, var2, patt2)) =
    case evaluation env expr1 of
        Just (VList []) ->
            evaluation env patt1
        Just (VList (x:xs)) ->
            evaluation env' patt2
            where
                env' = DM.insert var1 x (DM.insert var2 (VList xs) env)
        _ -> Nothing

-- FUNKCJA POMOCNICZA TWORZĄCA LISTĘ HASKELLOWĄ
consList h list = Just $ VList $ (h:list)

-- FUNKCJE POMOCNICZE EWALUUJĄCE OPERATORY
evalOpUnary UNot (VBool b) = Just . VBool $ not b
evalOpUnary UNeg (VNum n)  = Just . VNum $ -n

evalOpBinary BAnd (VBool b1) (VBool b2) = Just $ VBool $ b1 && b2
evalOpBinary BOr  (VBool b1) (VBool b2) = Just $ VBool $ b1 || b2
evalOpBinary BEq  (VNum n1)  (VNum n2)  = Just $ VBool $ n1 == n2
evalOpBinary BNeq (VNum n1)  (VNum n2)  = Just $ VBool $ n1 /= n2
evalOpBinary BLt  (VNum n1)  (VNum n2)  = Just $ VBool $ n1 <  n2
evalOpBinary BLe  (VNum n1)  (VNum n2)  = Just $ VBool $ n1 <= n2
evalOpBinary BGt  (VNum n1)  (VNum n2)  = Just $ VBool $ n1 >  n2
evalOpBinary BGe  (VNum n1)  (VNum n2)  = Just $ VBool $ n1 >= n2
evalOpBinary BAdd (VNum n1)  (VNum n2)  = Just $ VNum  $ n1 + n2
evalOpBinary BSub (VNum n1)  (VNum n2)  = Just $ VNum  $ n1 - n2
evalOpBinary BMul (VNum n1)  (VNum n2)  = Just $ VNum  $ n1 * n2
evalOpBinary BDiv (VNum n1)  (VNum n2)
    | n2 == 0   = Nothing
    | otherwise = Just $ VNum  $ n1 `div` n2
evalOpBinary BMod (VNum n1)  (VNum n2)
    | n2 == 0   = Nothing
    | otherwise = Just $ VNum  $ n1 `mod` n2
