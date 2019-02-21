{-# LANGUAGE Safe #-}

module FilipMarcinek (typecheck, eval) where

import AST
import DataTypes
import qualified Data.Map as DM


data Val =
    VNum Integer
    | VBool Bool
    | VUnit ()
    | VPair (Val,Val)
    | VList [Val]


type Env a = DM.Map Var a
type Env_Func a = DM.Map FSym a
type Function = (Val -> Maybe Val)

type Err p = (p, ErrKind)
data ErrKind =
    EUndefinedVariable Var
    | ETypeMismatch Type Type
    | EIfMismatch Type Type
    | EWrongFuncDef ErrKind
    | EUndefinedFunction FSym
    | EIsNotPair Type
    | EIsNotList Type
    | EListWithoutType


instance Show ErrKind where
  show (EUndefinedVariable x) =
    "Undefined variable " ++ show x ++ "."
  show (ETypeMismatch t1 t2)  =
    "Type mismatch: expected " ++ show t1 ++ " but received " ++ show t2 ++ "."
  show (EIfMismatch t1 t2)    =
    "Type mismatch in the branches of an if or match: " ++ show t1 ++ " and " ++ show t2 ++ "."
  show (EWrongFuncDef t)      =
    "Wrong function definiton: " ++ show t ++ "."
  show (EUndefinedFunction f) =
    "Undefined function named: " ++ show f ++ "."
  show (EIsNotPair t)         =
    "Type " ++ show t ++ " is not a type of pair."
  show (EIsNotList t)         =
    "Type " ++ show t ++ " is not a type of list."
  show (EListWithoutType)   =
    "Probably you forgot write word 'list' after expression:   []:'type'  '."


-- WIELKIE TYPOWANIE -----------------------------------------------------------

infer_type :: Env_Func (Type, Type) -> Env Type -> Expr p -> Either (Err p) Type

-- ZMIENNE
infer_type _ env (EVar p x) =
    case DM.lookup x env of
        Just t -> Right t
        Nothing -> Left (p, EUndefinedVariable x)

-- STAŁE
infer_type _ _ (ENum _ _) = Right TInt

infer_type _ _ (EBool _ _) = Right TBool

infer_type _ _ (EUnit _) = Right TUnit

-- LISTA PUSTA
infer_type _ _ (ENil p typ) =
    case typ of
        (TList t) -> Right (TList t)
        _ -> Left (p, EListWithoutType)


-- OPERATORY UNARNE
infer_type f_env env (EUnary _ op expr) =
    case check_type f_env env expr typ of
        Just err -> Left err
        Nothing -> Right res_type
        where (typ, res_type) = unaryOpType op

-- OPERATORY BINARNE
infer_type f_env env (EBinary _ op expr1 expr2) =
    case check_type f_env env expr1 typ1 of
        Just err -> Left err
        Nothing ->
            case check_type f_env env expr2 typ2 of
                Just err -> Left err
                Nothing -> Right res_type
    where (typ1, typ2, res_type) = binaryOpType op

-- WYRAŻENIE LET
infer_type f_env env (ELet p x expr1 expr2) =
    case infer_type f_env env expr1 of
        Left err -> Left err
        Right t1 -> infer_type f_env env' expr2
          where
              env' = DM.insert x t1 env

-- WYRAŻENIE WARUNKOWE IF ELSE
infer_type f_env env (EIf p expr1 expr2 expr3) =
    case check_type f_env env expr1 TBool of
        Just err -> Left err
        Nothing ->
            case equal_types p typ1 typ2 of
                Left err -> Left err
                Right t -> Right t
            where
                typ1 = infer_type f_env env expr2
                typ2 = infer_type f_env env expr3

-- APLIKACJA FUNKCJI
infer_type f_env env (EApp p f_name arg) =
    case DM.lookup f_name f_env of
        Nothing -> Left (p, EUndefinedFunction f_name)
        Just (t_arg, t_res) ->
            case check_type f_env env arg t_arg of
                Just err -> Left err
                Nothing -> Right t_res

-- PARA
infer_type f_env env (EPair p expr1 expr2) =
    case infer_type f_env env expr1 of
        Left err -> Left err
        Right t1 ->
            case infer_type f_env env expr2 of
                Left err -> Left err
                Right t2 -> Right (TPair t1 t2)

-- PROJRKCJE PARY
infer_type f_env env (EFst p expr) =
    case infer_type f_env env expr of
        Left err -> Left err
        Right (TPair t1 _) -> Right t1
        Right t -> Left (p, EIsNotPair t)

infer_type f_env env (ESnd p expr) =
    case infer_type f_env env expr of
        Left err -> Left err
        Right (TPair _ t2) -> Right t2
        Right t -> Left (p, EIsNotPair t)

-- TWORZENIE LISTY
infer_type f_env env (ECons p expr1 expr2) =
    case infer_type f_env env expr2 of
        Left err -> Left err
        Right (TList typ) ->
            case check_type f_env env expr1 typ of
                Just err -> Left err
                Nothing -> Right (TList typ)
        Right t -> Left (p, EIsNotList t)

-- WZORZEC MATCH
infer_type f_env env (EMatchL p expr patt1 (var1, var2, patt2)) =
    case infer_type f_env env expr of
        Left err -> Left err
        Right (TList t1) ->
            equal_types p typ1 typ2
            where
                typ1 = infer_type f_env env patt1
                typ2 = infer_type f_env env' patt2
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
check_type :: Env_Func (Type, Type) -> Env Type -> Expr p -> Type -> Maybe (Err p)

check_type f_env env expr typ =
    case infer_type f_env env expr of
        Left err -> Just err
        Right typ2 ->
            if typ == typ2 then Nothing
              else Just (getData expr, ETypeMismatch typ2 typ)

-- TWORZY ŚRODOWISKO POCZĄTKOWE ZE ZMIENNYCH W INPUT
env_init_type :: [Var] -> Env Type -> Env Type

env_init_type [] env_partial = env_partial
env_init_type (h:list) env_partial =
    env_init_type list (DM.insert h TInt env_partial)

-- FUNKCJA POMOCNICZA DO SPRAWDZANIA POPRAWNOŚCI PROGRAMOWYCH FUNKCJI
preprocessor :: [FunctionDef p] -> Env_Func (Type, Type) -> Env_Func (Type, Type)

preprocessor [] env_partial = env_partial
preprocessor (h:list) env_partial =
    preprocessor list (DM.insert func_name func_types env_partial)
    where
        func_name = funcName h
        func_types = (funcArgType h, funcResType h)

-- FUNKCJA SPRAWDZAJĄCA POPRAWNOŚĆ PROGRAMOWYCH FUNKCJI
init_func_check :: [FunctionDef p] -> Env_Func (Type, Type) -> Maybe (Err p)

init_func_check [] _ = Nothing
init_func_check (h:defs) f_env =
    case check_type f_env env expr typ of
        Just err -> Just (p, EWrongFuncDef $ snd err)
        Nothing -> init_func_check defs f_env
    where
      expr = funcBody h
      env = DM.insert (funcArg h) (funcArgType h) DM.empty
      typ = funcResType h
      p = funcPos h


-- TYPECHECK-----------------------------------

typecheck :: [FunctionDef p] -> [Var] -> Expr p -> TypeCheckResult p

typecheck fs vars body =
    case init_func_check fs f_env of
        Just (p, err) -> Error p $ show err
        Nothing ->
            case check_type f_env env body TInt of
                Just (p, err) -> Error p $ show err
                Nothing -> Ok
    where
        f_env = preprocessor fs DM.empty
        env = env_init_type vars DM.empty


-- EVAL ---------------------------------------

eval :: [FunctionDef p] -> [(Var,Integer)] -> Expr p -> EvalResult

eval fs vars body =
    case evaluation f_env env body of
        Just (VNum n) -> Value n
        Nothing -> RuntimeError
    where
        env = env_init_eval vars DM.empty
        f_env = func_init_eval fs DM.empty


-- FUNKCJA INICJUJĄCA ŚRODOWISKO FUNKCJI Z PROGRAMU
func_init_eval :: [FunctionDef p] -> Env_Func (Var, Expr p) -> Env_Func (Var, Expr p)

func_init_eval [] env_partial = env_partial
func_init_eval (h:fs) env_partial =
    func_init_eval fs (DM.insert f_name (var, f_body) env_partial)
    where
        f_name = funcName h
        (var, f_body) = (funcArg h, funcBody h)

-- FUNKCJA INICJUJĄCA ŚRODOWISKO ZMIENNYCH Z INPUT
env_init_eval :: [(Var, Integer)] -> DM.Map Var Val -> DM.Map Var Val

env_init_eval [] env_partial = env_partial
env_init_eval (h:list) env_partial =
    env_init_eval list (DM.insert var (VNum value) env_partial)
    where
        var = fst h
        value = snd h

-- POMOCNICZA FUNKCJA EWALUUJĄCA
evaluation :: Env_Func (Var, Expr p) -> Env Val -> Expr p -> Maybe Val

-- EWALUACJA STAŁYCH

evaluation _ _ (ENum _ n) = Just $ VNum n

evaluation _ _ (EBool _ bool) = Just $ VBool bool

evaluation _ _ (EUnit _) = Just $ VUnit ()

evaluation _ _ (ENil _ _) = Just $ VList []

-- ZMIENNA
evaluation _ env (EVar _ var) = DM.lookup var env

-- OPERATORY UNARNE
evaluation f_env env (EUnary _ op expr) =
  case evaluation f_env env expr of
    Nothing -> Nothing
    Just n -> evalOpUnary op n

-- OPERATORY BINARNE
evaluation f_env env (EBinary _ op expr1 expr2) =
    case evaluation f_env env expr1 of
      Nothing -> Nothing
      Just n1 ->
          case evaluation f_env env expr2 of
              Nothing -> Nothing
              Just n2 -> evalOpBinary op n1 n2

-- WYRAŻENIE LET
evaluation f_env env (ELet _ var expr1 expr2) =
    case evaluation f_env env expr1 of
      Nothing -> Nothing
      Just n ->
          evaluation f_env env' expr2
          where env' = DM.insert var n env

-- WYRAŻENIE WARUNKOWE IF ELSE
evaluation f_env env (EIf _ expr1 expr2 expr3) =
    case evaluation f_env env expr1 of
        Nothing -> Nothing
        Just (VBool True) -> evaluation f_env env expr2
        Just (VBool False) -> evaluation f_env env expr3

-- APLIKACJA FUNKCJI
evaluation f_env env (EApp _ f_name arg) =
    case evaluation f_env env arg of
        Nothing -> Nothing
        Just x ->
            case DM.lookup f_name f_env of
                Nothing -> Nothing     -- CZY TO NA PEWNO POTRZEBNE???
                Just f_body ->
                    evaluation f_env env' (snd f_body)
                    where
                        env' = DM.insert (fst f_body) x DM.empty -- Tu należy zasiorbać Var :: String ze środowiska (argument formalny)

-- PARA
evaluation f_env env (EPair _ expr1 expr2) =
    case (expr1', expr2') of
        (Just v1, Just v2) -> Just $ VPair $ (v1, v2)
        _ -> Nothing
    where
        expr1' = evaluation f_env env expr1
        expr2' = evaluation f_env env expr2

-- PROJEKCJE PARY
evaluation f_env env (EFst _ expr) =
    case evaluation f_env env expr of
        Nothing -> Nothing
        Just (VPair (v1, v2)) -> Just v1

evaluation f_env env (ESnd _ expr) =
    case evaluation f_env env expr of
        Nothing -> Nothing
        Just (VPair (v1, v2)) -> Just v2

-- TWORZENIE LISTY
evaluation f_env env (ECons _ expr1 expr2) =
    case evaluation f_env env expr1 of
        Nothing -> Nothing
        Just h ->
            case evaluation f_env env expr2 of
                Nothing -> Nothing
                Just (VList list) ->
                    consList h list

-- WZORZEC MATCH
evaluation f_env env (EMatchL _ expr1 patt1 (var1, var2, patt2)) =
    case evaluation f_env env expr1 of
        Just (VList []) ->
            evaluation f_env env patt1
        Just (VList (x:xs)) ->
            evaluation f_env env' patt2
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
