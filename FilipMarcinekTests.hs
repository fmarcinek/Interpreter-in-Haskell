-- Wymagamy, by moduł zawierał tylko bezpieczne funkcje
{-# LANGUAGE Safe #-}
-- Definiujemy moduł zawierający testy.
-- Należy zmienić nazwę modułu na {Imie}{Nazwisko}Tests gdzie za {Imie}
-- i {Nazwisko} należy podstawić odpowiednio swoje imię i nazwisko
-- zaczynające się wielką literą oraz bez znaków diakrytycznych.
module FilipMarcinekTests(tests) where

-- Importujemy moduł zawierający typy danych potrzebne w zadaniu
import DataTypes

-- Lista testów do zadania
-- Należy uzupełnić jej definicję swoimi testami
tests :: [Test]
tests =
  [ Test "inc"      (SrcString "input x in x + 1") (Eval [42] (Value 43))
  , Test "undefVar" (SrcString "x")                TypeError
  , Test "fst"      (SrcString "fst(fst(2,3),fst(4,5))") (Eval [] (Value 2))
  , Test "snd"      (SrcString "snd(snd(snd(5,6), 9), 3)") (Eval [] (Value 3))
  , Test "simple"   (SrcString "2+2")  (Eval [] (Value 4))
  , Test "if_else"  (SrcString "if true then 3 else false") TypeError
  , Test "match_list"      (SrcString "match [1,2,3]:int list with [] -> [] : int | x :: xs -> 2") TypeError
  , Test "bad_lambda" (SrcString "fn(x:bool) -> fn(y:bool) -> x + y") TypeError
  , Test "bad_lambda2" (SrcString "fn(x:bool) -> fn(z : int) -> x * y") TypeError
  , Test "bad_lambda3" (SrcString "fn(x : int) -> fn(x : bool) -> true") TypeError
  , Test "bool_asignment" (SrcString "input x in let y = true in if y then x else 0") (Eval [1] (Value 1))
  , Test "double_if" (SrcString "if (if 1 = 1 then false else true) and (if 1 = 1 then false else true) then 1 else 0") (Eval [] (Value 0))
  , Test "no_lazyness1" (SrcString "input x in fst (x, 1 div 0)") (Eval [42] (RuntimeError))
  , Test "no_lazyness2" (SrcString "input x in snd (5 div 0, x)") (Eval [3] (RuntimeError))
  , Test "wrong_result" (SrcString "input x y in if x <> y then true else false") TypeError
  , Test "many_lets"      (SrcFile "many_lets.pp6") (Eval [2,7] (Value 170))
  , Test "unused_wrong_functions" (SrcFile "unused_wrong_func.pp6") TypeError
  , Test "map_function" (SrcFile "map.pp6") (Eval [] (Value 55))
  , Test "length"      (SrcFile "length.pp6") (Eval [] (Value 10))
  , Test "quicksort"      (SrcFile "quicksort.pp6") (Eval [4,7,3,1,9] (Value 13479))
  , Test "variables_outside_lambda"      (SrcFile "var_lambda.pp6") (Eval [5,2] (Value 18))
  , Test "fibb"      (SrcFile "fibb.pp6") (Eval [12] (Value 144))
  , Test "func_var_conflict" (SrcFile "func_var_conflict.pp6") TypeError
  , Test "take"      (SrcFile "take.pp6") (Eval [] (Value 124566))
  , Test "tail"      (SrcFile "tail.pp6") (Eval [3] (Value 64))
  , Test "concat"      (SrcFile "concat.pp6") (Eval [7,3,5,8,9] (Value 73589))
  , Test "swap"      (SrcFile "swap.pp6") (Eval [5,8,4,2,9,6,4] (Value 5862944))
  , Test "reverse"      (SrcFile "reverse.pp6") (Eval [] (Value 525986575))
  ]
