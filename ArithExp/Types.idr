module ArithExp.Types

import ArithExp.AST
import ArithExp.SmallStep

||| Types for the ArithBool language
data SimpleType = TBool | TNum

-- syntax to make writing out types more natural.
syntax "[" [x] ":" [t] "]" = TypeOf x t

||| The ArithBool typing relation. There is no need to include a `gamma`-like
||| parameter here, as we don't have any variables.
data TypeOf : ArithBool -> SimpleType -> Type where
  ZeroT   : [ Zero : TNum ]
  SuccT   : [ n : TNum ] -> [ (Succ n) : TNum ]
  PredT   : [ n : TNum ] -> [ (Pred n) : TNum ]
  TruT    : [ Tru  : TBool ]
  FalsT   : [ Fals : TBool ]
  IfT     : [ c : TBool ] -> [ tcase : a ] -> [ fcase : a ]
         -> [ (IF c tcase fcase) : a ]
  IsZeroT : [ n : TNum ] -> [ (IsZero n) : TBool ]

||| Predicate for values in the language. Needed for defining progress
data IsValue : ArithBool -> Type where
  NumsValues : NV s -> IsValue s
  TruValue   : IsValue Tru
  FalsValue  : IsValue Fals

-- Boilerplate uninhabitted instances needed below.
--
-- These were all generated automatically with the idris-specific commands in
-- my editor, so the compiler should be able to infer it in principle. These
-- first two instances are just proofs that booleans cannot be typed as numbers.
Uninhabited [Fals : TNum] where
  uninhabited ZeroT impossible
  uninhabited (SuccT _) impossible
  uninhabited (PredT _) impossible
  uninhabited TruT impossible
  uninhabited FalsT impossible
  uninhabited (IfT _ _ _) impossible
  uninhabited (IsZeroT _) impossible

Uninhabited [Tru : TNum] where
  uninhabited ZeroT impossible
  uninhabited (SuccT _) impossible
  uninhabited (PredT _) impossible
  uninhabited TruT impossible
  uninhabited FalsT impossible
  uninhabited (IfT _ _ _) impossible
  uninhabited (IsZeroT _) impossible

||| Numbers are not booleans
boolNotNum : [c : TBool] -> NV c -> Void
boolNotNum TruT NvZero impossible
boolNotNum TruT (NvSucc _) impossible
boolNotNum FalsT NvZero impossible
boolNotNum FalsT (NvSucc _) impossible
boolNotNum (IfT _ _ _) NvZero impossible
boolNotNum (IfT _ _ _) (NvSucc _) impossible
boolNotNum (IsZeroT _) NvZero impossible
boolNotNum (IsZeroT _) (NvSucc _) impossible

||| Preservation lemma for type soundness
preservation : (a =>> b) -> [a : t] -> [b : t]
preservation IfTrue (IfT x y z) = y
preservation IfFalse (IfT x y z) = z
preservation (IfStep x) (IfT y z w) = IfT (preservation x y) z w
preservation (SuccStep x) (SuccT y) = SuccT (preservation x y)
preservation (IsZeroStep x) (IsZeroT y) = IsZeroT (preservation x y)
preservation IsZeroZero (IsZeroT x) = TruT
preservation IsZeroSucc (IsZeroT x) = FalsT
preservation (PredStep x) (PredT y) = PredT (preservation x y)
preservation PredZero (PredT x) = ZeroT
preservation PredSucc (PredT (SuccT x)) = x

||| Progress lemma for type soundness.
|||
||| This was more difficult to write, mostly because there are more cases
||| to consider. Each individual case is fairly straight-forward, so some
||| elaborator reflection should be able to automate this.
progress : [a : t] -> Either (IsValue a) (b ** (a =>> b))
progress ZeroT = Left (NumsValues NvZero)
progress (SuccT x) = case progress x of
                          Left  (NumsValues nv) => Left $ NumsValues (NvSucc nv)
                          -- booleans are not numbers
                          Left  TruValue        => absurd x
                          Left  FalsValue       => absurd x
                          Right (red ** step)   => Right ((Succ red) ** (SuccStep step))
progress (PredT x) =
  case progress x of
       Left (NumsValues NvZero)           => Right (Zero ** PredZero)
       Left (NumsValues (NvSucc k {n=n})) => Right (n ** PredSucc {prf=k})
       Left  TruValue                     => absurd x
       Left  FalsValue                    => absurd x
       Right (red ** step)                => Right ((Pred red) ** (PredStep step))
progress TruT   = Left TruValue
progress FalsT  = Left FalsValue
progress (IfT {tcase=tcase} {fcase=fcase} x y z) =
  case progress x of
       Left TruValue        => Right $ (tcase ** IfTrue)
       Left FalsValue       => Right $ (fcase ** IfFalse)
       Left (NumsValues nv) => absurd (boolNotNum x nv)
       Right (red ** step)  => Right  ((IF red tcase fcase) ** IfStep step)
progress (IsZeroT x) =
  case progress x of
       Left TruValue                => absurd x
       Left FalsValue               => absurd x
       Left (NumsValues NvZero)     => Right (Tru ** IsZeroZero)
       Left (NumsValues (NvSucc k)) => Right (Fals ** IsZeroSucc)
       Right (red ** step)          => Right (IsZero red ** IsZeroStep step)
