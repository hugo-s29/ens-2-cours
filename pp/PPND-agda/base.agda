open import Agda.Primitive
open import Data.Bool using (if_then_else_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum
open import Data.String using (String)
open import Data.List renaming (length to len)
open import Data.Fin using (Fin ; suc ; zero ; toℕ)
open import Data.Maybe
open import Function.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

record Variable : Set where
  constructor var
  field
    ident : String

data GenContext {A : Set} : Set where
  ． : GenContext
  _⨾_ : GenContext {A} → A → GenContext


_⨾⨾_ : ∀ {A} → GenContext {A} → GenContext → GenContext
Γ ⨾⨾ ． = Γ
Γ ⨾⨾ Δ ⨾ ϕ = (Γ ⨾⨾ Δ) ⨾ ϕ

length : ∀ {A} → GenContext {A} → ℕ
length ． = 0
length (Γ ⨾ ϕ) = 1 + length Γ

at : ∀ {A} → (Γ : GenContext {A}) → Fin (length Γ) → A
at ． ()
at (Γ ⨾ ϕ) zero = ϕ
at (Γ ⨾ x) (suc n) = at Γ n

at-opt : ∀ {A} → GenContext {A} → ℕ → Maybe A
at-opt ． i = nothing
at-opt (Γ ⨾ ϕ) zero = just ϕ
at-opt (Γ ⨾ ϕ) (suc i) = at-opt Γ i

at-opt-correct : ∀ {A} Γ i → (x : A) → at-opt Γ i ≡ just x → Σ (Fin (length Γ)) λ j → (x ≡ at Γ j × i ≡ toℕ j)
at-opt-correct (Γ ⨾ x) zero x refl = zero , refl , refl
at-opt-correct (Γ ⨾ y) (suc i) x p rewrite at-opt-correct Γ i x p .proj₂ .proj₁
    = suc (at-opt-correct Γ i x p .proj₁) , refl , cong suc (at-opt-correct Γ i x p .proj₂ .proj₂)

infixl 11 _⨾_
infixl 10 _⨾⨾_
