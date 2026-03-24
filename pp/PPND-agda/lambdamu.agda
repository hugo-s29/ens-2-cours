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

infixl 15 _·_

data Term (n : ℕ) : Set where
  ⦅_⦆ : Fin n → Term n
  λ[_]_ : Type → Term (suc n) → Term n
  _·_ : Term n → Term n → Term n
  C : Term n → Term n
  cc : Term n → Term n

data Value (n : ℕ) : Set where
  v⦅_⦆ : Fin n → Value n
  vλ[_]_ : Type → Term (suc n) → Value n

data CBV-context (n : ℕ) : Set where
  ？ : CBV-context n
  _·l_ : CBV-context n → Term n → CBV-context n
  _·r_ : Value n → CBV-context n → CBV-context n

Value→Term : ∀ {n} → Value n → Term n
Value→Term v⦅ i ⦆ = ⦅ i ⦆
Value→Term (vλ[ A ] M) = λ[ A ] M

_[CBV？／_] : ∀ {n} → CBV-context n → Term n → Term n
？ [CBV？／ M ] = M
(E ·l P) [CBV？／ M ] = E [CBV？／ M ] · P
(V ·r E) [CBV？／ M ] = Value→Term V · E [CBV？／ M ]


lift : ∀ {n} → Term n → Term (suc n)
lift ⦅ i ⦆ = ⦅ suc i ⦆
lift (λ[ A ] M) = λ[ A ] (lift M)
lift (M · N) = lift M · lift N
lift (C M) = C (lift M)
lift (cc M) = cc (lift M)

_[_] : ∀ {n} → Term (suc n) → Term n → Term n
⦅ zero ⦆ [ N ] = N
⦅ suc i ⦆ [ N ] = ⦅ i ⦆
(λ[ A ] M) [ N ] = λ[ A ] (M [ lift N ])
(M · N) [ P ] = M [ P ] · N [ P ]
C M [ N ] = C (M [ N ])
cc M [ N ] = cc (M [ N ])

data _βv_ : {n : ℕ} → Term n → Term n → Set where
  do-it-v : ∀ {n A} → (M : Term (suc n)) (V : Value n) → ((λ[ A ] M) · Value→Term V) βv (M [ Value→Term V ])

lift-Value : ∀ {n} → Value n → Value (suc n)
lift-Value v⦅ i ⦆ = v⦅ suc i ⦆
lift-Value (vλ[ A ] M) = vλ[ A ] lift M

lift-CBV-context : ∀ {n} → CBV-context n → CBV-context (suc n)
lift-CBV-context ？ = ？
lift-CBV-context (E ·l M) = lift-CBV-context E ·l lift M
lift-CBV-context (V ·r E) = lift-Value V ·r lift-CBV-context E

data _→CBV_ : {n : ℕ} → Term n → Term n → Set where
  do-it-cbvβ : ∀ {n} → (E : CBV-context n) (R P : Term n) → R βv P → (E [CBV？／ R ]) →CBV (E [CBV？／ P ])
  do-it-cbvC : ∀ {n A} → (E : CBV-context n) (M : Term n) → (E [CBV？／ C M ]) →CBV (M · (λ[ A ] (lift-CBV-context E [CBV？／ ⦅ zero ⦆ ])))
  do-it-cbvcc : ∀ {n A} → (E : CBV-context n) (M : Term n) → (E [CBV？／ cc M ]) →CBV (E [CBV？／ M · (λ[ A ] (lift-CBV-context E [CBV？／ ⦅ zero ⦆ ])) ])

Code : ∀ {n} → Term n → Term n → Set
Code ⦅ i ⦆ ⦅ j ⦆ = i ≡ j
Code (λ[ A ] M) (λ[ B ] N) = A ≡ B × M ≡ N
Code (M · N) (M' · N') = M ≡ M' × N ≡ N'
Code (C M) (C N) = M ≡ N
Code (cc M) (cc N) = M ≡ N
Code _ _ = False

encode : ∀ {n} → (M N : Term n) → M ≡ N → Code M N
encode ⦅ i ⦆ .(⦅ i ⦆) refl = refl
encode (λ[ A ] M) .(λ[ A ] M) refl = refl , refl
encode (M · N) .(M · N) refl = refl , refl
encode (C M) .(C M) refl = refl
encode (cc M) .(cc M) refl = refl

decode : ∀ {n} → (M N : Term n) → Code M N → M ≡ N
decode ⦅ i ⦆ ⦅ i ⦆ refl = refl
decode (λ[ A ] M) (λ[ A ] M) (refl , refl) = refl
decode (M · N) (M · N) (refl , refl) = refl
decode (C M) (C M) refl = refl
decode (cc M) (cc M) refl = refl

Value→Term-inj : ∀ {n} → (V V' : Value n) → Value→Term V ≡ Value→Term V' → V ≡ V'
Value→Term-inj v⦅ i ⦆ v⦅ j ⦆ refl = refl
Value→Term-inj (vλ[ A ] M) (vλ[ B ] N) refl = refl

lemma : ∀ {n} → (E F : CBV-context n) (R P : Term n) {R' P' : Term n} → (R →CBV R') → (P →CBV P') → Code (E [CBV？／ R ]) (F [CBV？／ P ]) → R ≡ P × E ≡ F
lemma ？ ？ R P h₁ h₂ eq = decode _ _ eq , refl
lemma ？ (F ·l M) (⦅ x₁ ⦆ · R') P {R''} () h₂ eq
lemma ？ (F ·l M) ((λ[ A ] R) · R') P {R''} h₁ h₂ eq = {!!}
lemma ？ (F ·l M) (R · R₁ · R') P {R''} h₁ h₂ eq = {!!}
lemma ？ (F ·l M) (C R · R') P {R''} h₁ h₂ eq = {!!}
lemma ？ (F ·l M) (cc R · R') P {R''} h₁ h₂ eq = {!!}
lemma ？ (M ·r F) R P h₁ h₂ eq = {!!}
lemma (E ·l M) ？ R P h₁ h₂ eq = {!!}
lemma (E ·l M) (F ·l M) R P h₁ h₂ (eq , refl) = lem .proj₁ , cong (_·l M) (lem .proj₂)
  where lem = lemma E F R P h₁ h₂ (encode _ _ eq)
lemma (E ·l M) (N ·r F) R P h₁ h₂ eq = {!!}
lemma (M ·r E) ？ R P h₁ h₂ eq = {!!}
lemma (M ·r E) (F ·l N) R P h₁ h₂ eq = {!!}
lemma (M ·r E) (N ·r F) R P h₁ h₂ (fst , eq) = (lem .proj₁) , (cong₂ _·r_ (Value→Term-inj M N fst) (lem .proj₂))
  where lem = lemma E F R P h₁ h₂ (encode _ _ eq)
