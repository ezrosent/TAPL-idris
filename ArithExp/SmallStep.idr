module ArithExp.SmallStep
import ArithExp.AST

||| Definition of a relation, adapted from *Software Foundations*
Relation : Type -> Type
Relation a = a -> a -> Type

deterministic : Relation a -> Type
deterministic {a=a} Ra = {x, y, z : a} -> Ra x y -> Ra x z -> y = z

||| Used or defining the "transitive closure" used in TAPL. 
|||
||| This is also taken from *Software Foundations*
data MultiStep : Relation a -> Relation a where
  Reflexive   : MultiStep r x x
  Transitive  : r x y -> MultiStep r y z -> MultiStep r x z

syntax [x] THEN   [y] = x `Transitive` (y)
syntax [a] "=>>"  [b]  = SmallStep a b
syntax [a] "=>>*" [b]  = MultiStep SmallStep a b

||| 'SmallStep' is the small step OS relation
data SmallStep : ArithBool -> ArithBool -> Type where

  IfTrue     : (IF Tru a b)  =>> a

  IfFalse    : (IF Fals a b) =>> b

  IfStep     : (t =>> t')
            -> (IF t a b) =>> (IF t' a b)

  SuccStep   : (t =>> t')
            -> (Succ t) =>> (Succ t')

  IsZeroStep : (t =>> t')
            -> (IsZero t) =>> (IsZero t')

  IsZeroZero : (IsZero Zero) =>> Tru

  IsZeroSucc : {auto prf : NV n} -> (IsZero (Succ n)) =>> Fals

  PredStep   : (t =>> t')
            -> (Pred t) =>> (Pred t')

  PredZero   : (Pred Zero) =>> Zero

  PredSucc   : {prf : NV n} -> (Pred (Succ n)) =>> n


test1 : (IF (IF Tru Fals Fals) Tru (IsZero (Succ (Succ Zero)))) =>>* Fals
test1 = (IfStep IfTrue)   THEN
        IfFalse           THEN
        IsZeroSucc        THEN
        Reflexive
