{-# LANGUAGE Safe #-}

-- ZADANIE DODATKOWE DO PRACOWNI 5

module FilipMarcinekCompiler(compile) where

import AST
import MacroAsm


type Env = [(Var, Int)]
type FuncEnv = [(FSym, Label)]

compile :: [FunctionDef p] -> [Var] -> Expr p -> [MInstr]
compile funcDefs input expr =
    fst solution ++ [MPopN lenInput, MRet] ++ instrFunc
    where
        solution = comp funcEnv vars lenDefs expr
        instrFunc = makeFuncInstr funcDefs funcEnv (snd solution)
        vars = makeVars input
        funcEnv = makeFuncEnv funcDefs
        lenInput = length input
        lenDefs = length funcDefs

makeFuncInstr :: [FunctionDef p] -> FuncEnv -> Label -> [MInstr]
makeFuncInstr [] _ lab = []
makeFuncInstr (h:list) fEnv lab =
    [MLabel labelNum] ++ instr ++ [MRet] ++ instrNext
    where
        Just labelNum = lookup fName fEnv
        (instr, lab1) = comp fEnv [(fArg, 0)] lab fBody
        (fArg, fName, fBody) = (funcArg h, funcName h, funcBody h)
        instrNext = makeFuncInstr list fEnv lab1

makeFuncEnv :: [FunctionDef p] -> FuncEnv
makeFuncEnv list = zip (map (\x -> funcName x) list) [0..]

makeVars :: [Var] -> Env
makeVars list = zip list [0..]

-- FUNKCJA 'COMP' GENERUJE ISTRUKCJE POTRZEBNE DO OBLICZENIA WYRAŻEŃ
-- I JAKO PARAMETR PRZEKAZUJE JESZCZE NAJMNIEJSZY NIEUŻYTY NUMER ETYKIETY

comp :: FuncEnv -> Env -> Label -> Expr p -> ([MInstr], Label)

-- ZMIENNA
comp fEnv vars lab (EVar _ v) =
    case lookup v vars of
        Just k -> ([MGetLocal k], lab)

-- STAŁE
comp _ _ lab (ENum _ n) = ([MConst n], lab)

comp _ _ lab (EBool _ b) = ([MConst $ evBool b], lab)

-- OPERATORY UNARNE
comp fEnv vars lab (EUnary _ op expr) =
    (instr' ++ [evOpUn op], lab')
    where (instr', lab') = comp fEnv vars lab expr

-- OPERATORY BINARNE
comp fEnv vars lab (EBinary _ op expr1 expr2) =
    case evOpBi op of
        Left cc ->
            (instr1 ++ [MPush] ++ instr2 ++ [MBranch cc lab2, MConst 0,
                MJump $ lab2+1, MLabel lab2, MConst 1, MLabel $ lab2+1], lab2+2)
            where
                (instr1, lab1) = comp fEnv vars lab expr1
                (instr2, lab2) = comp fEnv vars' lab1 expr2
                vars' = vmap vars 1
        Right mInstr ->
            (instr1 ++ [MPush] ++ instr2 ++ [mInstr], lab2)
            where
                (instr1, lab1) = comp fEnv vars lab expr1
                (instr2, lab2) = comp fEnv vars' lab1 expr2
                vars' = vmap vars 1


-- WYRAŻENIE LET
comp fEnv vars lab (ELet _ var value body) =
    (instr1 ++ [MPush] ++ instr2 ++ [MPopN 1], lab2)
    where
        (instr1, lab1) = comp fEnv vars lab value
        (instr2, lab2) = comp fEnv vars' lab1 body
        vars' = (var, 0) : vmap vars 1

-- WYRAŻENIE WARUNKOWE IF... ELSE...
comp fEnv vars lab (EIf _ ifEx thenEx elseEx) =
    (instrIf ++ [MBranch MC_Z lab1] ++ instrThen ++ [MJump lab2] ++
                    [MLabel lab1] ++ instrElse ++ [MLabel lab2], lab3)
    where
        (instrIf, lab1) = comp fEnv vars lab ifEx
        (instrElse, lab2) = comp fEnv vars (lab1+1) elseEx
        (instrThen, lab3) = comp fEnv vars (lab2+1) thenEx


-- APLIKACJA FUNKCJI
comp fEnv vars lab (EApp _ fName fArg) =
    (instrArg ++ [MPush, MCall fLab, MPopN 1], lab1)
    where
        (instrArg, lab1) = comp fEnv vars lab fArg
        Just fLab = lookup fName fEnv

-- UNIT
comp _ _ lab (EUnit _) = ([MConst 0], lab)

-- REPREZENTACJA PARY W PAMIĘCI:
--       -----------------
--       | lewy argument  |
         -----------------
--       | prawy argument |
         -----------------
-- PARA
comp fEnv vars lab (EPair p expr1 expr2) =
    ([MAlloc 2, MPush] ++ instr1 ++ [MSet 0] ++ instr2 ++ [MSet 1, MPopAcc], lab2)
    where
        (instr1, lab1) = comp fEnv vars' lab expr1
        (instr2, lab2) = comp fEnv vars' lab1 expr2
        vars' = vmap vars 1

-- PROJEKCJE PARY
comp fEnv vars lab (EFst _ expr) =
    (instr ++ [MGet 0], lab')
    where
        (instr, lab') = comp fEnv vars lab expr

comp fEnv vars lab (ESnd _ expr) =
    (instr ++ [MGet 1], lab')
    where
        (instr, lab') = comp fEnv vars lab expr

-- REPREZENTACJA NIEPUSTEJ LISTY W PAMIĘCI:
--       --------------------
--       |     wartość       |
         --------------------
--       | adres nast. elem. |
         --------------------

-- LISTA PUSTA
comp fEnv vars lab (ENil _ _) = ([MConst 0], lab)

-- KONSTRUKTOR LISTY NIEPUSTEJ
comp fEnv vars lab (ECons _ expr1 expr2) =
    ([MAlloc 2, MPush] ++ instr1 ++ [MSet 0] ++ instr2
                                                ++ [MSet 1, MPopAcc], lab2)
    where
        (instr1, lab1) = comp fEnv vars' lab expr1
        (instr2, lab2) = comp fEnv vars' lab1 expr2
        vars' = vmap vars 1

-- WZORZEC MATCH
comp fEnv vars lab (EMatchL _ expr patt1 (var1, var2, patt2)) =
    (instrExpr ++ [MBranch MC_Z lab1, MPush, MGetLocal 0, MGet 0, MPush,
        MGetLocal 1, MGet 1, MSetLocal 1] ++ instrPatt2 ++ [MPopN 2, MJump lab2,
        MLabel lab1] ++ instrPatt1 ++ [MLabel lab2], lab3)
    where
        (instrExpr, lab1) = comp fEnv vars lab expr
        (instrPatt2, lab2) = comp fEnv vars' (lab1+1) patt2
        (instrPatt1, lab3) = comp fEnv vars (lab2+1) patt1
        vars' = (var1, 0) : (var2, 1) : vmap vars 2

-- FUNKCJA DO PRZESUWANIA POZYCJI NA STOSIE ZMIENNYCH ZE ŚRODOWISKA
vmap list n = map (\(x,y) -> (x,y + n)) list


-- EWALUUJĄCE FUNKCJE POMOCNICZE
evBool True = 1
evBool False = 0

evOpUn UNot = MNot
evOpUn UNeg = MNeg

evOpBi op =
    case op of
        BAnd -> Right MAnd
        BOr -> Right MOr
        BAdd -> Right MAdd
        BSub -> Right MSub
        BMul -> Right MMul
        BDiv -> Right MDiv
        BMod -> Right MMod

        BEq -> Left MC_EQ
        BNeq -> Left MC_NE
        BLt -> Left MC_LT
        BGt -> Left MC_GT
        BLe -> Left MC_LE
        BGe -> Left MC_GE
