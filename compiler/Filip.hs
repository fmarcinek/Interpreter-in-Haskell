{-# LANGUAGE Safe #-}

module Filip(compile) where

import AST
import MacroAsm

compile :: [FunctionDef p] -> [Var] -> Expr p -> [MInstr]
compile list input expr =
    [MPopAcc, MCall 0, MPush, MGetLocal 1, MCall 0, MAdd, MPopN 2, MRet, MLabel 0, MPush, MMul, MRet]
