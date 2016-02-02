module ArithExp.AST
%default total

||| Desugaring levels for the language.
data Sugar = Core | Surface

||| ADT for the language itself + syntactic sugar
|||
||| This is all done in "Curry style". To do this in Church style, the type of
||| AST could be `AST : Sugar -> SimpleType -> Type` where each variant has the
||| type per the typing rules in `Types.idr`. This could make some of the type
||| soundness proof easier to write.
data AST : Sugar -> Type where
  Zero   : AST a
  Tru    : AST a
  Fals   : AST a
  IF     : AST a -> AST a -> AST a -> AST a
  Succ   : AST a -> AST a
  Pred   : AST a -> AST a
  IsZero : AST a -> AST a
  Num    : Nat   -> AST Surface
  AND    : AST a -> AST a -> AST Surface
  OR     : AST a -> AST a -> AST Surface

ArithBool : Type
ArithBool = AST Core

||| desguar away 'Num' 'And' and 'OR', could add extra operators too!
desugar : AST a -> AST Core
desugar Zero        = Zero
desugar Tru         = Tru
desugar Fals        = Fals
desugar (IF x y z)  = IF (desugar x) (desugar y) (desugar z)
desugar (Succ x)    = Succ (desugar x)
desugar (Pred x)    = Pred (desugar x)
desugar (IsZero x)  = IsZero (desugar x)
desugar (AND a b)   = IF (desugar a) (desugar b) Fals
desugar (OR a b)    = IF (desugar a) Tru (desugar b)
desugar (Num r)     = unroll r
  where unroll : Nat -> AST Core
        unroll Z     = Zero
        unroll (S k) = Succ (unroll k)

||| Type-level predicate describing fully-reduced numeric values
data NV : ArithBool -> Type where
  NvZero : NV Zero
  NvSucc : NV n -> NV (Succ n)
