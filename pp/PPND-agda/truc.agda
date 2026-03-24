open import Agda.Primitive
open import Data.Bool using ( Bool ; true ; false)


if_then_else_ : {X : Bool → Set} → (b : Bool) → X true → X false → X b
if false then x else y = y
if true then x else y = x
