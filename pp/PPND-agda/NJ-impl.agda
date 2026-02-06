open import Agda.Primitive
open import Data.Bool using (if_then_else_)
open import Data.Nat hiding (_≟_)
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum
open import Data.String using (String)
open import Data.List renaming (length to len)
open import Data.Fin using (Fin ; suc ; zero ; _↑ʳ_)
open import Function.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import base

data Formula : Set where
  ⦅_⦆ : Variable → Formula
  _⇒_ : Formula → Formula → Formula

x y z a b c : Formula
x = ⦅ var "x" ⦆
y = ⦅ var "y" ⦆
z = ⦅ var "z" ⦆
a = ⦅ var "a" ⦆
b = ⦅ var "b" ⦆
c = ⦅ var "c" ⦆

Context : Set
Context = GenContext {Formula}

infix 5 _⊢_
infixr 15 _⇒_

data Sequent : Set where
  _⊢_ : Context → Formula → Sequent

data NJ⟨_⟩[_] : List Sequent → Sequent → Set where
  prem : ∀ {Γ p A} → (i : Fin (len p)) → Γ ⊢ A ≡ lookup p i → NJ⟨ p ⟩[ Γ ⊢ A ]
  ax : ∀ {Γ p} → (i : Fin (length Γ)) → NJ⟨ p ⟩[ Γ ⊢ at Γ i ]
  ⇒I : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⨾ B ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ B ⇒ A ]
  ⇒E : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ B ⇒ A ] → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ]

private
  extract-var : String → Formula → String
  extract-var i ⦅ var j ⦆ = j
  extract-var i _ = i

  extract-head : Formula → Formula → Formula
  extract-head ϕ (ψ ⇒ _) = ψ
  extract-head ϕ _ = ϕ

  extract-tail : Formula → Formula → Formula
  extract-tail ϕ (_ ⇒ ψ) = ψ
  extract-tail ϕ _ = ϕ

_≟_ : DecidableEquality Formula
⦅ var i ⦆ ≟ ⦅ var j ⦆ with i Data.String.≟ j
... | yes i≡j rewrite i≡j = yes refl
... | no ¬i≡j = no (¬i≡j ∘ cong (extract-var i))

⦅ i ⦆ ≟ (ϕ ⇒ ψ) = no (λ ())
(ϕ ⇒ ψ) ≟ ⦅ i ⦆ = no (λ ())
(ϕ ⇒ γ) ≟ (ψ ⇒ δ) with (ϕ ≟ ψ) , (γ ≟ δ)
... | yes ϕ≡ψ , yes γ≡δ rewrite ϕ≡ψ rewrite γ≡δ = yes refl
... | no ¬ϕ≡ψ , _ = no (¬ϕ≡ψ ∘ cong (extract-head ϕ))
... | _ , no ¬γ≡δ = no (¬γ≡δ ∘ cong (extract-tail δ))

NJ[_] : Sequent → Set
NJ[ Γ ⊢ ϕ ] = NJ⟨ [] ⟩[ Γ ⊢ ϕ ]
