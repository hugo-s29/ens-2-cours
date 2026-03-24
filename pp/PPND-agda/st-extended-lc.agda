open import Agda.Primitive
open import Data.Bool using (if_then_else_ ; Bool ; true ; false)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum hiding ([_,_])
open import Data.String using (String)
open import Data.List renaming (length to len) hiding (fromMaybe ; [_]) 
open import Data.Maybe
open import Data.Fin using (Fin ; suc ; zero ; toℕ ; _≟_)
open import Function.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ( [_] ; subst )
open import Relation.Nullary.Decidable hiding (False)

open import base

data Type : Set where
  ⦅_⦆ : Variable → Type
  ⊥ : Type
  ⊤ : Type
  _⇒_ : Type → Type → Type
  _∧_ : Type → Type → Type
  _∨_ : Type → Type → Type

x y z a b c : Type
x = ⦅ var "x" ⦆
y = ⦅ var "y" ⦆
z = ⦅ var "z" ⦆
a = ⦅ var "a" ⦆
b = ⦅ var "b" ⦆
c = ⦅ var "c" ⦆

Context : Set
Context = GenContext {Type}

infix 5 _⊢_
infixr 15 _⇒_
infixr 15 _⇔_
infixr 20 _∨_
infixr 30 _∧_

_⇔_ : Type → Type → Type
f ⇔ g = (f ⇒ g) ∧ (g ⇒ f)


data Sequent : Set where
  _⊢_ : Context → Type → Sequent

data NJ⟨_⟩[_] : List Sequent → Sequent → Set where
  prem : ∀ {Γ p A} → (i : Fin (len p)) → Γ ⊢ A ≡ lookup p i → NJ⟨ p ⟩[ Γ ⊢ A ]
  ax : ∀ {Γ p} → (i : Fin (length Γ)) → NJ⟨ p ⟩[ Γ ⊢ at Γ i ]
  ⊥E : ∀ {Γ p A} → NJ⟨ p ⟩[ Γ ⊢ ⊥ ] → NJ⟨ p ⟩[ Γ ⊢ A ]
  ⊤I : ∀ {Γ p} → NJ⟨ p ⟩[ Γ ⊢ ⊤ ]
  ⇒I : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⨾ B ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ B ⇒ A ]
  ⇒E : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ B ⇒ A ] → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ]
  ∧I : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ∧ B ]
  ∧El : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ∧ B ] → NJ⟨ p ⟩[ Γ ⊢ A ]
  ∧Er : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ∧ B ] → NJ⟨ p ⟩[ Γ ⊢ B ]
  ∨Il : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ A ∨ B ]
  ∨Ir : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ∨ B ]
  ∨E : ∀ {Γ p A B C} → NJ⟨ p ⟩[ Γ ⊢ A ∨ B ] → NJ⟨ p ⟩[ Γ ⨾ A ⊢ C ] → NJ⟨ p ⟩[ Γ ⨾ B ⊢ C ] → NJ⟨ p ⟩[ Γ ⊢ C ]

NJ[_] : Sequent → Set
NJ[ Γ ⊢ ϕ ] = NJ⟨ [] ⟩[ Γ ⊢ ϕ ]

NJ[_]⋆ : List Sequent → Set
NJ[ [] ]⋆ = Unit
NJ[ s ∷ l ]⋆ = NJ[ s ] × NJ[ l ]⋆

infix  5 _⊢_∶_
infixl 15 _·_
infixl 15 case_[ι₁→_,ι₂→_]

data Term (n : ℕ) : Set where
  ⋆ : Term n
  ⦅_⦆ : Fin n → Term n
  λ[_]_ : Type → Term (suc n) → Term n
  _·_ : Term n → Term n → Term n
  case[_]_ : Type → Term n → Term n
  [_,_] : Term n → Term n → Term n
  π₁_ : Term n → Term n
  π₂_ : Term n → Term n
  ι₁[_∨_]_ : Type → Type → Term n → Term n
  ι₂[_∨_]_ : Type → Type → Term n → Term n
  case_[ι₁→_,ι₂→_] : Term n → Term (suc n) → Term (suc n) → Term n

data _⊢_∶_ : (Γ : Context) → Term (length Γ) → Type → Set where
  type-var : ∀ {Γ} (i : Fin _) → Γ ⊢ ⦅ i ⦆ ∶ at Γ i
  type-lam : ∀ {Γ A B M} → Γ ⨾ A ⊢ M ∶ B → Γ ⊢ λ[ A ] M ∶ A ⇒ B
  type-app : ∀ {Γ A B M N} → Γ ⊢ M ∶ A ⇒ B → Γ ⊢ N ∶ A → Γ ⊢ M · N ∶ B
  type-unt : ∀ {Γ} → Γ ⊢ ⋆ ∶ ⊤
  type-bot : ∀ {Γ M A} → Γ ⊢ M ∶ ⊥ → Γ ⊢ case[ A ] M ∶ A
  type-pai : ∀ {Γ M N A B} → Γ ⊢ M ∶ A → Γ ⊢ N ∶ B → Γ ⊢ [ M , N ] ∶ A ∧ B
  type-pr1 : ∀ {Γ M A B} → Γ ⊢ M ∶ A ∧ B → Γ ⊢ π₁ M ∶ A
  type-pr2 : ∀ {Γ M A B} → Γ ⊢ M ∶ A ∧ B → Γ ⊢ π₂ M ∶ B
  type-in1 : ∀ {Γ M A B} → Γ ⊢ M ∶ A → Γ ⊢ ι₁[ A ∨ B ] M ∶ A ∨ B
  type-in2 : ∀ {Γ M A B} → Γ ⊢ M ∶ B → Γ ⊢ ι₂[ A ∨ B ] M ∶ A ∨ B
  type-sum : ∀ {Γ M N P A B C} → Γ ⊢ M ∶ A ∨ B → Γ ⨾ A ⊢ N ∶ C → Γ ⨾ B ⊢ P ∶ C → Γ ⊢ case M [ι₁→ N ,ι₂→ P ] ∶ C


ELC[_] : Sequent → Set
ELC[ Γ ⊢ A ] = Σ (Term (length Γ)) (λ M → Γ ⊢ M ∶ A)

CHλ→ϕ : ∀ Γ A → ELC[ Γ ⊢ A ] → NJ[ Γ ⊢ A ]
CHλ→ϕ Γ A (⋆ , type-unt) = ⊤I
CHλ→ϕ Γ A (⦅ i ⦆ , type-var i) = ax i
CHλ→ϕ Γ (A ⇒ B) ((λ[ A ] M) , type-lam Π) = ⇒I (CHλ→ϕ (Γ ⨾ A) B (M , Π))
CHλ→ϕ Γ A (M · N , type-app {A = B} Π Π₁) = ⇒E (CHλ→ϕ Γ (B ⇒ A) (M , Π)) (CHλ→ϕ Γ B (N , Π₁))
CHλ→ϕ Γ A ((case[ _ ] M) , type-bot Π) = ⊥E (CHλ→ϕ Γ ⊥ (M , Π))
CHλ→ϕ Γ (A ∧ B) ([ M , N ] , type-pai Π Π₁) = ∧I (CHλ→ϕ Γ A (M , Π)) (CHλ→ϕ Γ B (N , Π₁))
CHλ→ϕ Γ A ((π₁ M) , type-pr1 {B = B} Π) = ∧El (CHλ→ϕ Γ (A ∧ B) (M , Π))
CHλ→ϕ Γ A ((π₂ M) , type-pr2 {A = B} Π) = ∧Er (CHλ→ϕ Γ (B ∧ A) (M , Π))
CHλ→ϕ Γ (A ∨ B) ((ι₁[ A ∨ B ] M) , type-in1 Π) = ∨Il (CHλ→ϕ Γ A (M , Π))
CHλ→ϕ Γ (A ∨ B) ((ι₂[ A ∨ B ] M) , type-in2 Π) = ∨Ir (CHλ→ϕ Γ B (M , Π))
CHλ→ϕ Γ C (case M [ι₁→ N ,ι₂→ P ] , type-sum {A = A} {B = B} Π Π₁ Π₂) = ∨E (CHλ→ϕ Γ (A ∨ B) (M , Π)) (CHλ→ϕ (Γ ⨾ A) C (N , Π₁)) (CHλ→ϕ (Γ ⨾ B) C (P , Π₂))


CHϕ→λ : ∀ Γ A → NJ[ Γ ⊢ A ] → ELC[ Γ ⊢ A ]
CHϕ→λ Γ A (ax i) = ⦅ i ⦆ , type-var i
CHϕ→λ Γ A (⊥E Π) = (case[ A ] CHϕ→λ Γ ⊥ Π .proj₁) , type-bot (CHϕ→λ Γ ⊥ Π .proj₂)
CHϕ→λ Γ A ⊤I = ⋆ , type-unt
CHϕ→λ Γ A (⇒I Π) = (λ[ _ ] CHϕ→λ (Γ ⨾ _) _ Π .proj₁) , type-lam (CHϕ→λ (Γ ⨾ _) _ Π .proj₂)
CHϕ→λ Γ A (⇒E Π Π₁) = CHϕ→λ Γ (_ ⇒ A) Π .proj₁ · CHϕ→λ Γ _ Π₁ .proj₁ , type-app (CHϕ→λ Γ (_ ⇒ A) Π .proj₂) (CHϕ→λ Γ _ Π₁ .proj₂)
CHϕ→λ Γ A (∧I Π Π₁) = [ CHϕ→λ Γ _ Π .proj₁ , CHϕ→λ Γ _ Π₁ .proj₁ ] , type-pai (CHϕ→λ Γ _ Π .proj₂) (CHϕ→λ Γ _ Π₁ .proj₂)
CHϕ→λ Γ A (∧El Π) = (π₁ CHϕ→λ Γ (A ∧ _) Π .proj₁) , type-pr1 (CHϕ→λ Γ (A ∧ _) Π .proj₂)
CHϕ→λ Γ A (∧Er Π) = (π₂ CHϕ→λ Γ (_ ∧ A) Π .proj₁) , type-pr2 (CHϕ→λ Γ (_ ∧ A) Π .proj₂)
CHϕ→λ Γ A (∨Il Π) = (ι₁[ _ ∨ _ ] CHϕ→λ Γ _ Π .proj₁) , type-in1 (CHϕ→λ Γ _ Π .proj₂)
CHϕ→λ Γ A (∨Ir Π) = (ι₂[ _ ∨ _ ] CHϕ→λ Γ _ Π .proj₁) , type-in2 (CHϕ→λ Γ _ Π .proj₂)
CHϕ→λ Γ C (∨E {A = A} {B = B} Π Π₁ Π₂) = case (CHϕ→λ Γ (A ∨ B) Π .proj₁) [ι₁→ (CHϕ→λ (Γ ⨾ A) C Π₁ .proj₁) ,ι₂→ (CHϕ→λ (Γ ⨾ B) C Π₂ .proj₁) ] , type-sum (CHϕ→λ Γ (A ∨ B) Π .proj₂) (CHϕ→λ (Γ ⨾ A) C Π₁ .proj₂) (CHϕ→λ (Γ ⨾ B) C Π₂ .proj₂)


CHϕ→ϕ : ∀ {Γ A} Π → CHλ→ϕ Γ A (CHϕ→λ Γ A Π) ≡ Π
CHϕ→ϕ (ax i) = refl
CHϕ→ϕ (⊥E Π) rewrite CHϕ→ϕ Π = refl
CHϕ→ϕ ⊤I = refl
CHϕ→ϕ (⇒I Π) rewrite CHϕ→ϕ Π = refl
CHϕ→ϕ (⇒E Π Π₁) rewrite CHϕ→ϕ Π rewrite CHϕ→ϕ Π₁ = refl
CHϕ→ϕ (∧I Π Π₁) rewrite CHϕ→ϕ Π rewrite CHϕ→ϕ Π₁ = refl
CHϕ→ϕ (∧El Π) rewrite CHϕ→ϕ Π = refl
CHϕ→ϕ (∧Er Π) rewrite CHϕ→ϕ Π = refl
CHϕ→ϕ (∨Il Π) rewrite CHϕ→ϕ Π = refl
CHϕ→ϕ (∨Ir Π) rewrite CHϕ→ϕ Π = refl
CHϕ→ϕ (∨E Π Π₁ Π₂) rewrite CHϕ→ϕ Π rewrite CHϕ→ϕ Π₁ rewrite CHϕ→ϕ Π₂ = refl

CHλ→λ : ∀ {Γ A} M Π → CHϕ→λ Γ A (CHλ→ϕ Γ A (M , Π)) ≡ (M , Π)
CHλ→λ ⋆ type-unt = refl
CHλ→λ ⦅ x₁ ⦆ (type-var i) = refl
CHλ→λ (λ[ A ] M) (type-lam Π) rewrite CHλ→λ M Π = refl
CHλ→λ (M · N) (type-app Π Π₁) rewrite CHλ→λ M Π rewrite CHλ→λ N Π₁ = refl
CHλ→λ (case[ A ] M) (type-bot Π) rewrite CHλ→λ M Π = refl
CHλ→λ [ M , N ] (type-pai Π Π₁) rewrite CHλ→λ M Π rewrite CHλ→λ N Π₁ = refl
CHλ→λ (π₁ M) (type-pr1 Π) rewrite CHλ→λ M Π = refl
CHλ→λ (π₂ M) (type-pr2 Π) rewrite CHλ→λ M Π = refl
CHλ→λ (ι₁[ A ∨ B ] M) (type-in1 Π) rewrite CHλ→λ M Π = refl
CHλ→λ (ι₂[ A ∨ B ] M) (type-in2 Π) rewrite CHλ→λ M Π = refl
CHλ→λ case M [ι₁→ N ,ι₂→ P ] (type-sum Π Π₁ Π₂) rewrite CHλ→λ M Π rewrite CHλ→λ N Π₁ rewrite CHλ→λ P Π₂ = refl

Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

liftRen : ∀ {n m} → Ren n m → Ren (suc n) (suc m)
liftRen ρ zero    = zero
liftRen ρ (suc x) = suc (ρ x)

rename : ∀ {n m} → Ren n m → Term n → Term m
rename ρ ⋆ = ⋆
rename ρ ⦅ x ⦆ = ⦅ ρ x ⦆
rename ρ (λ[ A ] t) = λ[ A ] rename (liftRen ρ) t
rename ρ (t · u) = rename ρ t · rename ρ u
rename ρ (case[ A ] t) = case[ A ] rename ρ t
rename ρ [ t , u ] = [ rename ρ t , rename ρ u ]
rename ρ (π₁ t) = π₁ rename ρ t
rename ρ (π₂ t) = π₂ rename ρ t
rename ρ (ι₁[ A ∨ B ] t) = ι₁[ A ∨ B ] rename ρ t
rename ρ (ι₂[ A ∨ B ] t) = ι₂[ A ∨ B ] rename ρ t
rename ρ (case t [ι₁→ u ,ι₂→ v ]) =
  case rename ρ t
       [ι₁→ rename (liftRen ρ) u
       ,ι₂→ rename (liftRen ρ) v ]


Sub : ℕ → ℕ → Set
Sub n m = Fin n → Term m

liftSub : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
liftSub σ zero    = ⦅ zero ⦆
liftSub σ (suc x) = rename suc (σ x)

subst : ∀ {n m} → Sub n m → Term n → Term m
subst σ ⋆ = ⋆
subst σ ⦅ x ⦆ = σ x
subst σ (λ[ A ] t) = λ[ A ] subst (liftSub σ) t
subst σ (t · u) = subst σ t · subst σ u
subst σ (case[ A ] t) = case[ A ] subst σ t
subst σ [ t , u ] = [ subst σ t , subst σ u ]
subst σ (π₁ t) = π₁ subst σ t
subst σ (π₂ t) = π₂ subst σ t
subst σ (ι₁[ A ∨ B ] t) = ι₁[ A ∨ B ] subst σ t
subst σ (ι₂[ A ∨ B ] t) = ι₂[ A ∨ B ] subst σ t
subst σ (case t [ι₁→ u ,ι₂→ v ]) =
  case subst σ t
       [ι₁→ subst (liftSub σ) u
       ,ι₂→ subst (liftSub σ) v ]

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
_[_] {n} t u = subst σ t
  where
    σ : Fin (suc n) → Term n
    σ zero    = u
    σ (suc x) = ⦅ x ⦆

infix 5 _[_]
infixr 1 _→β_

data _→β_ : ∀ {n} → Term n → Term n → Set where
  β-step : ∀ {n A} → {M : Term (suc n)} { N : Term n} → (λ[ A ] M) · N →β M [ N ]
  β-prj₁ : ∀ {n} → {M N : Term n} → π₁ [ M , N ] →β M
  β-prj₂ : ∀ {n} → {M N : Term n} → π₂ [ M , N ] →β N
  β-inj₁ : ∀ {n A B} → {M : Term n} {N P : Term (suc n)} → case ι₁[ A ∨ B ] M [ι₁→ N ,ι₂→ P ] →β N [ M ]
  β-inj₂ : ∀ {n A B} → {M : Term n} {N P : Term (suc n)} → case ι₂[ A ∨ B ] M [ι₁→ N ,ι₂→ P ] →β P [ M ]
  β-inλ : ∀ {n A} → {M N : Term (suc n)} → M →β N → λ[ A ] M →β λ[ A ] N
  β-appl : ∀ {n} → {M N P : Term n} → M →β N → M · P →β N · P
  β-appr : ∀ {n} → {M N P : Term n} → N →β P → M · N →β M · P
  β-in⊥ : ∀ {n A} → {M N : Term n} → M →β N → case[ A ] M →β case[ A ] N
