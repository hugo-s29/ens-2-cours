open import Agda.Primitive
open import Data.Bool using (if_then_else_)
open import Data.Nat hiding (_≟_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum
open import Data.String using (String)
open import Data.List renaming (length to len) hiding (_∷_ ; _++_)
open import Data.Fin using (Fin ; suc ; zero ; _↑ʳ_)
open import Function.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary.Decidable

open import NJ hiding (Sequent ; Rule ; admissible ; derivable ; reversible)

open import base

infix 5 _⟝_

_∷_ : Formula → List Formula → List Formula
_∷_ = Data.List._∷_

_++_ : List Formula → List Formula → List Formula
_++_ = Data.List._++_

infixr 8 _∷_
infixr 7 _++_

data Sequent : Set where
  _⟝_ : Context → List Formula → Sequent


data NC⟨_⟩[_] : List Sequent → Sequent → Set where
  prem : ∀ {Γ p Δ} → (i : Fin (len p)) → Γ ⟝ Δ ≡ lookup p i → NC⟨ p ⟩[ Γ ⟝ Δ ]
  ax : ∀ {Γ Δ p} → (i : Fin (length Γ)) → NC⟨ p ⟩[ Γ ⟝ at Γ i ∷ Δ ]
  ⊤I : ∀ {Γ Δ p} → NC⟨ p ⟩[ Γ ⟝ ⊤ ∷ Δ ]
  ⊥E : ∀ {Γ Δ p A} → NC⟨ p ⟩[ Γ ⟝ ⊥ ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∷ Δ ]
  ¬I : ∀ {Γ Δ p A} → NC⟨ p ⟩[ Γ ⨾ A ⟝ ⊥ ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ ¬ A ∷ Δ ]
  ¬E : ∀ {Γ Δ p A} → NC⟨ p ⟩[ Γ ⟝ ¬ A ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ ⊥ ∷ Δ ]
  ∧I : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∧ B ∷ Δ ]
  ∧El : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ∧ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∷ Δ ]
  ∧Er : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ∧ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ B ∷ Δ ]
  ∨I : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ∷ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∨ B ∷ Δ ]
  ∨E : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ∨ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∷ B ∷ Δ ]
  ⇒I : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⨾ A ⟝ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ⇒ B ∷ Δ ]
  ⇒E : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ⇒ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ B ∷ Δ ]
  exch : ∀ {Γ Δ p A B} → NC⟨ p ⟩[ Γ ⟝ A ∷ B ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ B ∷ A ∷ Δ ]
  contr : ∀ {Γ Δ p A} → NC⟨ p ⟩[ Γ ⟝ A ∷ A ∷ Δ ] → NC⟨ p ⟩[ Γ ⟝ A ∷ Δ ]

NC[_] : Sequent → Set
NC[ Γ ⟝ ϕ ] = NC⟨ [] ⟩[ Γ ⟝ ϕ ]

NC[_]⋆ : List Sequent → Set
NC[ [] ]⋆ = Unit
NC[ s List.∷ l ]⋆ = NC[ s ] × NC[ l ]⋆

record Rule : Set where
  constructor rule
  field
    premisses : List Sequent
    conclusion : Sequent

derivable : Rule → Set
derivable (rule premisses conclusion) = NC⟨ premisses ⟩[ conclusion ]

admissible : Rule → Set
admissible (rule premisses conclusion) = NC[ premisses ]⋆ → NC[ conclusion ]

reversible : Rule → Set
reversible (rule premisses conclusion) = NC[ conclusion ] → NC[ premisses ]⋆

EM : ∀ A → NC[ ． ⟝ [ A ∨ ¬ A ] ]
EM A = ∨I (exch (¬I (exch (ax zero))))

ex30 : ∀ A B → NC[ ． ⟝ [ ¬ (A ∧ B) ⇔ ¬ A ∨ ¬ B ] ]
ex30 A B = ∧I (⇒I (∨I (¬I (exch (¬I (¬E (ax ((suc (suc zero)))) (∧I (ax (suc zero)) (ax zero))))))))
         (⇒I (¬I ?))

NJ⊆NC : ∀ Γ {Δ} A → NJ[ Γ ⊢ A ] → NC[ Γ ⟝ A ∷ Δ ]
NJ⊆NC Γ A (ax i) = ax i
NJ⊆NC Γ A (⊥E Π) = ⊥E (NJ⊆NC Γ ⊥ Π)
NJ⊆NC Γ A ⊤I = ⊤I
NJ⊆NC Γ A (⇒I Π) = ⇒I (NJ⊆NC (Γ ⨾ _) _ Π)
NJ⊆NC Γ A (⇒E Π Π₁) = ⇒E (NJ⊆NC Γ (_ ⇒ A) Π) (NJ⊆NC Γ _ Π₁)
NJ⊆NC Γ A (¬I Π) = ¬I (NJ⊆NC (Γ ⨾ _) ⊥ Π)
NJ⊆NC Γ A (¬E Π Π₁) = ¬E (NJ⊆NC Γ (¬ _) Π) (NJ⊆NC Γ _ Π₁)
NJ⊆NC Γ A (∧I Π Π₁) = ∧I (NJ⊆NC Γ _ Π) (NJ⊆NC Γ _ Π₁)
NJ⊆NC Γ A (∧El Π) = ∧El (NJ⊆NC Γ (A ∧ _) Π)
NJ⊆NC Γ A (∧Er Π) = ∧Er (NJ⊆NC Γ (_ ∧ A) Π)
NJ⊆NC Γ A (∨Il Π) = ∨I (NJ⊆NC Γ _ Π)
NJ⊆NC Γ A (∨Ir Π) = ∨I (exch (NJ⊆NC Γ _ Π))
NJ⊆NC Γ A (∨E Π Π₁ Π₂) = {!∨E!}


