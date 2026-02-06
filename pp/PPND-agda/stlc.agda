open import Agda.Primitive
open import Data.Bool using (if_then_else_ ; Bool ; true ; false)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum
open import Data.String using (String)
open import Data.List renaming (length to len) hiding (fromMaybe ; [_]) 
open import Data.Maybe
open import Data.Fin using (Fin ; suc ; zero ; toℕ ; _≟_)
open import Function.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary.Decidable hiding (False)

open import base
open import NJ-impl renaming (Formula to Type)

infix  5 _⊢_∶_
infix  5 _→β_
infixl 15 _·_

data Term (n : ℕ) : Set where
  ⦅_⦆ : Fin n → Term n
  λ[_]_ : Type → Term (suc n) → Term n
  _·_ : Term n → Term n → Term n

·-test : ∀ {n} → {M N P : Term n} → M · N · P ≡ (M · N) · P
·-test = refl

data _⊢_∶_ : (Γ : Context) → Term (length Γ) → Type → Set where
  type-var : ∀ {Γ} (i : Fin _) → Γ ⊢ ⦅ i ⦆ ∶ at Γ i
  type-lam : ∀ {Γ A B M} → Γ ⨾ A ⊢ M ∶ B → Γ ⊢ λ[ A ] M ∶ A ⇒ B
  type-app : ∀ {Γ A B M N} → Γ ⊢ M ∶ A ⇒ B → Γ ⊢ N ∶ A → Γ ⊢ M · N ∶ B

Infer : (Γ : Context) → (M : Term (length Γ)) → Maybe (Σ Type λ A → Γ ⊢ M ∶ A)
Infer Γ ⦅ i ⦆ = just (at Γ i , type-var i)
Infer Γ (λ[ A ] M) with Infer (Γ ⨾ A) M
... | nothing = nothing
... | just (B , p) = just (A ⇒ B , type-lam p)
Infer Γ (M · N) with Infer Γ M , Infer Γ N
... | nothing , _ = nothing
... | just _ , nothing = nothing
... | just (⦅ _ ⦆ , p) , just (C , q) = nothing
... | just (B ⇒ D , p) , just (C , q) with B NJ-impl.≟ C
... | yes refl = just (D , type-app p q)
... | no _ = nothing

infer : ∀ Γ → Term (length Γ) → Maybe Type
infer Γ M with Infer Γ M
... | nothing = nothing
... | just (A , _) = just A

infer-correct : ∀ Γ M A → infer Γ M ≡ just A → Γ ⊢ M ∶ A
infer-correct Γ M A p with Infer Γ M
infer-correct Γ M A () | nothing
infer-correct Γ M A refl | just (.A , p) = p

private
  exfalso : {X : Set} → False → X
  exfalso ()

Infer-complete : ∀ Γ M A → (Π : Γ ⊢ M ∶ A) → Infer Γ M ≡ just (A , Π)
Infer-complete Γ M A (type-var i) = refl
Infer-complete Γ (λ[ A ] M) (A ⇒ B) (type-lam Π) rewrite Infer-complete (Γ ⨾ A) M B Π = refl
Infer-complete Γ (M · N) A (type-app {A = B} Π Π₁) rewrite Infer-complete Γ M (B ⇒ A) Π rewrite Infer-complete Γ N B Π₁ with B NJ-impl.≟ B
... | yes refl = refl
... | no ¬B≡B = exfalso (¬B≡B refl)

STLC[_] : Sequent → Set
STLC[ Γ ⊢ A ] = Σ (Term (length Γ)) (λ M → Γ ⊢ M ∶ A)

CHλ→ϕ : ∀ Γ A → STLC[ Γ ⊢ A ] → NJ[ Γ ⊢ A ]
CHλ→ϕ Γ A (⦅ i ⦆ , type-var i) = ax i
CHλ→ϕ Γ (A ⇒ B) (λ[ A ] M , type-lam Π) = ⇒I (CHλ→ϕ (Γ ⨾ A) B (M , Π))
CHλ→ϕ Γ A (M · N , type-app {A = B} Π Π₁) = ⇒E (CHλ→ϕ Γ (B ⇒ A) (M , Π)) (CHλ→ϕ Γ B (N , Π₁))

CHϕ→λ : ∀ Γ A → NJ[ Γ ⊢ A ] → STLC[ Γ ⊢ A ]
CHϕ→λ Γ A (ax i) = ⦅ i ⦆ , type-var i
CHϕ→λ Γ (A ⇒ B) (⇒I Π) with CHϕ→λ (Γ ⨾ A) B Π
... | M , Π' = λ[ A ] M , type-lam Π'
CHϕ→λ Γ A (⇒E {B = B} Π Π₁) with CHϕ→λ Γ (B ⇒ A) Π , CHϕ→λ Γ B Π₁
... | (M , Π') , (N , Π'') = M · N , type-app Π' Π''

CHϕ→ϕ : ∀ Γ A Π → CHλ→ϕ Γ A (CHϕ→λ Γ A Π) ≡ Π
CHϕ→ϕ Γ A (ax i) = refl
CHϕ→ϕ Γ (A ⇒ B) (⇒I Π) rewrite CHϕ→ϕ (Γ ⨾ A) B Π = refl
CHϕ→ϕ Γ A (⇒E {B = B} Π Π₁) rewrite CHϕ→ϕ Γ (B ⇒ A) Π rewrite CHϕ→ϕ Γ B Π₁ = refl

CHλ→λ : ∀ Γ A M Π → CHϕ→λ Γ A (CHλ→ϕ Γ A (M , Π)) ≡ (M , Π)
CHλ→λ Γ A ⦅ i ⦆ (type-var i) = refl
CHλ→λ Γ (A ⇒ B) (λ[ A ] M) (type-lam Π) rewrite CHλ→λ (Γ ⨾ A) B M Π = refl
CHλ→λ Γ B (M · N) (type-app {A = A} Π Π₁) rewrite CHλ→λ Γ A N Π₁ rewrite CHλ→λ Γ (A ⇒ B) M Π = refl

private
  ⟦_⟧-inside : ℕ → Term (2+ zero)
  ⟦ zero ⟧-inside  = ⦅ zero ⦆
  ⟦ suc n ⟧-inside = ⦅ suc zero ⦆ · ⟦ n ⟧-inside

⟦_⟧ : ℕ → Type → Term zero
⟦ n ⟧ A = λ[ A ⇒ A ] λ[ A ] ⟦ n ⟧-inside

⟦n⟧-typed : ∀ n A → ． ⊢ ⟦ n ⟧ A ∶ (A ⇒ A) ⇒ (A ⇒ A)
⟦n⟧-typed n A = type-lam (type-lam (lem n))
  where
  lem : ∀ n → ． ⨾ A ⇒ A ⨾ A ⊢ ⟦ n ⟧-inside ∶ A
  lem zero = type-var zero
  lem (suc n) = type-app (type-var (suc zero)) (lem n)


data Ctx (n : ℕ) : Set where
  C□ : Ctx n
  Cλ[_]_ : Type → Ctx (suc n) → Ctx n
  _C·_ : Ctx n → Term n → Ctx n
  _·C_ : Term n → Ctx n → Ctx n


private
  fin-inj : ∀ {n} → Fin n → Fin (suc n)
  fin-inj zero = zero
  fin-inj (suc i) = suc (fin-inj i)

  fin-pred : ∀ {n} → Fin (2+ n) → Fin (suc n)
  fin-pred zero = zero
  fin-pred (suc i) = i

bump : ∀ {n} → Fin n → ℕ → Fin (suc n)
bump i h with h ≤ᵇ toℕ i
bump i h | true = suc i
bump i h | false = fin-inj i

unbump : ∀ {n} → Fin (2+ n) → ℕ → Fin (2+ n)
unbump i h with h <ᵇ toℕ i
unbump i h | true = fin-inj (fin-pred i)
unbump i h | false = i

lift : ∀ {n} → ℕ → Term n → Term (suc n)
lift k ⦅ i ⦆ = ⦅ (bump i k) ⦆
lift k (λ[ A ] M) = λ[ A ] lift (suc k) M
lift k (M · N) = lift k M · lift k N

lift₀ : ∀ {n} → Term n → Term (suc n)
lift₀ = lift 0

_[_／_] : ∀ {n} → Term (2+ n) → Fin (2+ n) → Term (2+ n) → Term (2+ n)
⦅ j ⦆ [ i ／ N ] with i Data.Fin.≟ j
... | yes i≡j = N
... | no ¬i≡j = ⦅ unbump j {!!} ⦆
(λ[ A ] M) [ i ／ N ] = {!!}
(M · M') [ i ／ N ] = {!!}


data _→β_ : ∀ {n} → Term n → Term n → Set where
  step : ∀ {n A n} → {M : Term (suc n)} → {N : Term n} → (λ[ A ] M) · N →β {!!}
