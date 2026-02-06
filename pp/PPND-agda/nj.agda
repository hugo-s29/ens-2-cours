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
  ⊥ : Formula
  ⊤ : Formula
  _⇒_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  ¬_ : Formula → Formula

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
infixr 15 _⇔_
infixr 20 _∨_
infixr 30 _∧_
infix  40 ¬_

_⇔_ : Formula → Formula → Formula
f ⇔ g = (f ⇒ g) ∧ (g ⇒ f)


data Sequent : Set where
  _⊢_ : Context → Formula → Sequent

data NJ⟨_⟩[_] : List Sequent → Sequent → Set where
  prem : ∀ {Γ p A} → (i : Fin (len p)) → Γ ⊢ A ≡ lookup p i → NJ⟨ p ⟩[ Γ ⊢ A ]
  ax : ∀ {Γ p} → (i : Fin (length Γ)) → NJ⟨ p ⟩[ Γ ⊢ at Γ i ]
  ⊥E : ∀ {Γ p A} → NJ⟨ p ⟩[ Γ ⊢ ⊥ ] → NJ⟨ p ⟩[ Γ ⊢ A ]
  ⊤I : ∀ {Γ p} → NJ⟨ p ⟩[ Γ ⊢ ⊤ ]
  ⇒I : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⨾ B ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ B ⇒ A ]
  ⇒E : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ B ⇒ A ] → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ]
  ¬I : ∀ {Γ p A} → NJ⟨ p ⟩[ Γ ⨾ A ⊢ ⊥ ] → NJ⟨ p ⟩[ Γ ⊢ ¬ A ]
  ¬E : ∀ {Γ p A} → NJ⟨ p ⟩[ Γ ⊢ ¬ A ] → NJ⟨ p ⟩[ Γ ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ ⊥ ]
  ∧I : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ∧ B ]
  ∧El : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ∧ B ] → NJ⟨ p ⟩[ Γ ⊢ A ]
  ∧Er : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ∧ B ] → NJ⟨ p ⟩[ Γ ⊢ B ]
  ∨Il : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ A ] → NJ⟨ p ⟩[ Γ ⊢ A ∨ B ]
  ∨Ir : ∀ {Γ p A B} → NJ⟨ p ⟩[ Γ ⊢ B ] → NJ⟨ p ⟩[ Γ ⊢ A ∨ B ]
  ∨E : ∀ {Γ p A B C} → NJ⟨ p ⟩[ Γ ⊢ A ∨ B ] → NJ⟨ p ⟩[ Γ ⨾ A ⊢ C ] → NJ⟨ p ⟩[ Γ ⨾ B ⊢ C ] → NJ⟨ p ⟩[ Γ ⊢ C ]

record Rule : Set where
  constructor rule
  field
    premisses : List Sequent
    conclusion : Sequent

NJ[_] : Sequent → Set
NJ[ Γ ⊢ ϕ ] = NJ⟨ [] ⟩[ Γ ⊢ ϕ ]

NJ[_]⋆ : List Sequent → Set
NJ[ [] ]⋆ = Unit
NJ[ s ∷ l ]⋆ = NJ[ s ] × NJ[ l ]⋆

derivable : Rule → Set
derivable (rule premisses conclusion) = NJ⟨ premisses ⟩[ conclusion ]

admissible : Rule → Set
admissible (rule premisses conclusion) = NJ[ premisses ]⋆ → NJ[ conclusion ]

reversible : Rule → Set
reversible (rule premisses conclusion) = NJ[ conclusion ] → NJ[ premisses ]⋆

replace-proofs : ∀ Γ ϕ L → NJ[ L ]⋆ → NJ⟨ L ⟩[ Γ ⊢ ϕ ] → NJ[ Γ ⊢ ϕ ]
replace-proofs Γ ϕ (s ∷ p) (Π , _) (prem zero refl) = Π
replace-proofs Γ ϕ (s ∷ p) (_ , p-pr) (prem (suc i) x) = replace-proofs Γ ϕ p p-pr (prem i x)
replace-proofs Γ ϕ p p-pr (ax i) = ax i
replace-proofs Γ ϕ p p-pr (⊥E Π) = ⊥E (replace-proofs Γ ⊥ p p-pr Π)
replace-proofs Γ ϕ p p-pr ⊤I = ⊤I
replace-proofs Γ ϕ p p-pr (⇒I Π) = ⇒I (replace-proofs (Γ ⨾ _) _ p p-pr Π)
replace-proofs Γ ϕ p p-pr (⇒E Π Π₁) = ⇒E (replace-proofs Γ (_ ⇒ ϕ) p p-pr Π) (replace-proofs Γ _ p p-pr Π₁)
replace-proofs Γ ϕ p p-pr (¬I Π) = ¬I (replace-proofs (Γ ⨾ _) _ p p-pr Π)
replace-proofs Γ ϕ p p-pr (¬E Π Π₁) = ¬E (replace-proofs Γ (¬ _) p p-pr Π) (replace-proofs Γ _ p p-pr Π₁)
replace-proofs Γ ϕ p p-pr (∧I Π Π₁) = ∧I (replace-proofs Γ _ p p-pr Π) (replace-proofs Γ _ p p-pr Π₁)
replace-proofs Γ ϕ p p-pr (∧El Π) = ∧El (replace-proofs Γ (ϕ ∧ _) p p-pr Π)
replace-proofs Γ ϕ p p-pr (∧Er Π) = ∧Er (replace-proofs Γ (_ ∧ ϕ) p p-pr Π)
replace-proofs Γ ϕ p p-pr (∨Il Π) = ∨Il (replace-proofs Γ _ p p-pr Π)
replace-proofs Γ ϕ p p-pr (∨Ir Π) = ∨Ir (replace-proofs Γ _ p p-pr Π)
replace-proofs Γ ϕ p p-pr (∨E Π Π₁ Π₂) = ∨E (replace-proofs Γ (_ ∨ _) p p-pr Π) (replace-proofs (Γ ⨾ _) ϕ p p-pr Π₁) (replace-proofs (Γ ⨾ _) ϕ p p-pr Π₂)

derivable→admissible : (R : Rule) → derivable R → admissible R
derivable→admissible (rule premisses (Γ ⊢ ϕ)) p pr = replace-proofs Γ ϕ premisses pr p

_⊆_ : Context → Context → Set
Δ ⊆ Γ = (i : Fin (length Δ)) → Σ (Fin (length Γ)) λ j → at Δ i ≡ at Γ j

infix  4 _⊆_

⨾⊆⨾ : ∀ {Γ Δ ϕ} → Δ ⊆ Γ → (Δ ⨾ ϕ) ⊆ (Γ ⨾ ϕ)
⨾⊆⨾ Δ⊆Γ zero = zero , refl
⨾⊆⨾ Δ⊆Γ (suc i) = suc (Δ⊆Γ i .proj₁) , Δ⊆Γ i .proj₂

op : ∀ Γ Δ → Δ ⊆ Γ → Formula → Rule
op Γ Δ Δ⊆Γ ϕ = rule ((Δ ⊢ ϕ) ∷ []) (Γ ⊢ ϕ)

op-admissible : ∀ Γ Δ Δ⊆Γ {ϕ} → admissible (op Γ Δ Δ⊆Γ ϕ)
op-admissible Γ Δ Δ⊆Γ (ax i , tt) rewrite Δ⊆Γ i .proj₂ = ax (Δ⊆Γ i .proj₁)
op-admissible Γ Δ Δ⊆Γ (⊥E Π , tt) = ⊥E (op-admissible Γ Δ Δ⊆Γ (Π , tt))
op-admissible Γ Δ Δ⊆Γ (⊤I , tt) = ⊤I
op-admissible Γ Δ Δ⊆Γ (⇒I {B = ϕ} Π , tt) = ⇒I (op-admissible (Γ ⨾ ϕ) (Δ ⨾ ϕ) (⨾⊆⨾ Δ⊆Γ) (Π , tt))
op-admissible Γ Δ Δ⊆Γ (⇒E Π Π₁ , tt) = ⇒E (op-admissible Γ Δ Δ⊆Γ (Π , tt)) (op-admissible Γ Δ Δ⊆Γ (Π₁ , tt))
op-admissible Γ Δ Δ⊆Γ (¬I {A = ϕ} Π , tt) = ¬I (op-admissible (Γ ⨾ ϕ) (Δ ⨾ ϕ) (⨾⊆⨾ Δ⊆Γ) (Π , tt))
op-admissible Γ Δ Δ⊆Γ (¬E Π Π₁ , tt) = ¬E (op-admissible Γ Δ Δ⊆Γ (Π , tt)) (op-admissible Γ Δ Δ⊆Γ (Π₁ , tt))
op-admissible Γ Δ Δ⊆Γ (∧I Π Π₁ , tt) = ∧I (op-admissible Γ Δ Δ⊆Γ (Π , tt)) (op-admissible Γ Δ Δ⊆Γ (Π₁ , tt))
op-admissible Γ Δ Δ⊆Γ (∧El Π , tt) = ∧El (op-admissible Γ Δ Δ⊆Γ (Π , tt))
op-admissible Γ Δ Δ⊆Γ (∧Er Π , tt) = ∧Er (op-admissible Γ Δ Δ⊆Γ (Π , tt))
op-admissible Γ Δ Δ⊆Γ (∨Il Π , tt) = ∨Il (op-admissible Γ Δ Δ⊆Γ (Π , tt))
op-admissible Γ Δ Δ⊆Γ (∨Ir Π , tt) = ∨Ir (op-admissible Γ Δ Δ⊆Γ (Π , tt))
op-admissible Γ Δ Δ⊆Γ (∨E {A = A} {B = B} Π Π₁ Π₂ , tt) = ∨E (op-admissible Γ Δ Δ⊆Γ (Π , tt)) (op-admissible (Γ ⨾ A) (Δ ⨾ A) (⨾⊆⨾ Δ⊆Γ) (Π₁ , tt)) (op-admissible (Γ ⨾ B) (Δ ⨾ B) (⨾⊆⨾ Δ⊆Γ) (Π₂ , tt))

wk : Context → Formula → Formula → Rule
wk Γ ϕ ψ = rule ((Γ ⊢ ψ) ∷ []) (Γ ⨾ ϕ ⊢ ψ)

wk-admissible : ∀ Γ ϕ ψ → admissible (wk Γ ϕ ψ)
wk-admissible Γ ϕ ψ = op-admissible (Γ ⨾ ϕ) Γ λ i → suc i , refl

⊆⨾⨾-1 : ∀ Γ Δ → Γ ⊆ Γ ⨾⨾ Δ
⊆⨾⨾-1 Γ ． i = i , refl
⊆⨾⨾-1 Γ (Δ ⨾ ψ) i rewrite ⊆⨾⨾-1 Γ Δ i .proj₂ = suc (⊆⨾⨾-1 Γ Δ i .proj₁) , refl

⊆⨾⨾-2 : ∀ Γ Δ → Γ ⊆ Δ ⨾⨾ Γ
⊆⨾⨾-2 (Γ ⨾ ϕ) Δ zero = zero , refl
⊆⨾⨾-2 (Γ ⨾ ϕ) Δ (suc i) rewrite ⊆⨾⨾-2 Γ Δ i .proj₂ = suc (⊆⨾⨾-2 Γ Δ i .proj₁) , refl

wk⋆ : Context → Context → Formula → Rule
wk⋆ Γ Δ ϕ = rule ((Γ ⊢ ϕ) ∷ []) (Γ ⨾⨾ Δ ⊢ ϕ)

wk⋆-admissible : ∀ Γ Δ ϕ → admissible (wk⋆ Γ Δ ϕ)
wk⋆-admissible Γ Δ ϕ = op-admissible (Γ ⨾⨾ Δ) Γ (⊆⨾⨾-1 Γ Δ)

wk⋆' : Context → Context → Formula → Rule
wk⋆' Γ Δ ϕ = rule ((Γ ⊢ ϕ) ∷ []) (Δ ⨾⨾ Γ ⊢ ϕ)

wk⋆'-admissible : ∀ Γ Δ ϕ → admissible (wk⋆' Γ Δ ϕ)
wk⋆'-admissible Γ Δ ϕ = op-admissible (Δ ⨾⨾ Γ) Γ (⊆⨾⨾-2 Γ Δ)

⇒I-reversible : ∀ Γ ϕ ψ → reversible (rule ((Γ ⨾ ϕ ⊢ ψ) ∷ []) (Γ ⊢ ϕ ⇒ ψ))
⇒I-reversible Γ ϕ ψ Π = ⇒E (wk-admissible Γ ϕ (ϕ ⇒ ψ) (Π , tt)) (ax zero) , tt


xch : Context → Context → Formula → Formula → Formula → Rule
xch Γ Δ A B C = rule ((Γ ⨾ B ⨾ A ⨾⨾ Δ ⊢ C) ∷ []) (Γ ⨾ A ⨾ B ⨾⨾ Δ ⊢ C)

xch-admissible : ∀ Γ Δ A B C → admissible (xch Γ Δ A B C)
xch-admissible Γ Δ A B C = op-admissible (Γ ⨾ A ⨾ B ⨾⨾ Δ) (Γ ⨾ B ⨾ A ⨾⨾ Δ) (lem Δ)
  where
  lem : ∀ Δ → (Γ ⨾ B ⨾ A ⨾⨾ Δ) ⊆ (Γ ⨾ A ⨾ B ⨾⨾ Δ)
  lem ． zero = suc zero , refl
  lem ． (suc zero) = zero , refl
  lem ． (suc (suc i)) = suc (suc i) , refl
  lem (Δ ⨾ ϕ) zero = zero , refl
  lem (Δ ⨾ ϕ) (suc i) rewrite lem Δ i .proj₂ = suc (lem Δ i .proj₁) , refl

ct : Context → Formula → Formula → Rule
ct Γ ϕ ψ = rule ((Γ ⨾ ϕ ⨾ ϕ ⊢ ψ) ∷ []) (Γ ⨾ ϕ ⊢ ψ)

ct-admissible : ∀ Γ ϕ ψ → admissible (ct Γ ϕ ψ)
ct-admissible Γ ϕ ψ = op-admissible (Γ ⨾ ϕ) (Γ ⨾ ϕ ⨾ ϕ) lem
  where
  lem : (Γ ⨾ ϕ ⨾ ϕ) ⊆ (Γ ⨾ ϕ)
  lem zero = zero , refl
  lem (suc zero) = zero , refl
  lem (suc (suc i)) = (suc i) , refl

wk-non-derivable : (∀ Γ A B → derivable (wk Γ A B)) → NJ[ ． ⊢ ⊥ ]
wk-non-derivable h = {!!}


_[_／_] : Formula → Variable → Formula → Formula
⦅ var y ⦆ [ var x ／ ψ ] = if ⌊ x Data.String.≟ y ⌋ then ψ else ⦅ var y ⦆
⊥ [ x ／ ψ ] = ⊥
⊤ [ x ／ ψ ] = ⊤
(ϕ ⇒ ϕ₁) [ x ／ ψ ] = (ϕ [ x ／ ψ ]) ⇒ (ϕ₁ [ x ／ ψ ])
(ϕ ∧ ϕ₁) [ x ／ ψ ] = (ϕ [ x ／ ψ ]) ∧ (ϕ₁ [ x ／ ψ ])
(ϕ ∨ ϕ₁) [ x ／ ψ ] = (ϕ [ x ／ ψ ]) ∨ (ϕ₁ [ x ／ ψ ])
(¬ ϕ) [ x ／ ψ ] = ¬ (ϕ [ x ／ ψ ])

_[_／_]⋆ : Context → Variable → Formula → Context
． [ x ／ ψ ]⋆ = ．
(Γ ⨾ ϕ) [ x ／ ψ ]⋆ = Γ [ x ／ ψ ]⋆ ⨾ ϕ [ x ／ ψ ]

subst-provable : ∀ {Γ ϕ} x ψ → NJ[ Γ ⊢ ϕ ] → NJ[ Γ [ x ／ ψ ]⋆ ⊢ ϕ [ x ／ ψ ] ]
subst-provable x ψ (⊥E Π) = ⊥E (subst-provable x ψ Π)
subst-provable x ψ ⊤I = ⊤I
subst-provable x ψ (⇒I Π) = ⇒I (subst-provable x ψ Π)
subst-provable x ψ (⇒E Π Π₁) = ⇒E (subst-provable x ψ Π) (subst-provable x ψ Π₁)
subst-provable x ψ (¬I Π) = ¬I (subst-provable x ψ Π)
subst-provable x ψ (¬E Π Π₁) = ¬E (subst-provable x ψ Π) (subst-provable x ψ Π₁)
subst-provable x ψ (∧I Π Π₁) = ∧I (subst-provable x ψ Π) (subst-provable x ψ Π₁)
subst-provable x ψ (∧El Π) = ∧El (subst-provable x ψ Π)
subst-provable x ψ (∧Er Π) = ∧Er (subst-provable x ψ Π)
subst-provable x ψ (∨Il Π) = ∨Il (subst-provable x ψ Π)
subst-provable x ψ (∨Ir Π) = ∨Ir (subst-provable x ψ Π)
subst-provable x ψ (∨E Π Π₁ Π₂) = ∨E (subst-provable x ψ Π) (subst-provable x ψ Π₁) (subst-provable x ψ Π₂)
subst-provable {Γ} x ψ (ax i) = res
  where
  lem : ∀ Γ i → Σ _ λ j → at Γ i [ x ／ ψ ] ≡ at (Γ [ x ／ ψ ]⋆) j
  lem ． ()
  lem (Γ ⨾ _) zero = zero , refl
  lem (Γ ⨾ x₁) (suc i) rewrite lem Γ i .proj₂ = suc (lem Γ i .proj₁) , refl

  res : NJ[ Γ [ x ／ ψ ]⋆ ⊢ at Γ i [ x ／ ψ ] ]
  res rewrite lem Γ i .proj₂ = ax (lem Γ i .proj₁)

_⇒⋆_ : Context → Formula → Formula
． ⇒⋆ ϕ = ϕ
(Γ ⨾ ψ) ⇒⋆ ϕ = ψ ⇒ Γ ⇒⋆ ϕ

∧⋆ : Context → Formula
∧⋆ ． = ⊤
∧⋆ (Γ ⨾ ϕ) = ∧⋆ Γ ∧ ϕ

_↔_ : Set → Set → Set
P ↔ Q = (P → Q) × (Q → P)

module TD1 where
  ex1-a : NJ[ ． ⊢ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c ]
  ex1-a = ⇒I (⇒I (⇒I (⇒E (⇒E (ax (suc (suc zero))) (ax zero)) (⇒E (ax (suc zero)) (ax zero)))))

  ex1-b : NJ[ ． ⊢ (a ∧ b) ∨ (a ∧ c) ⇒ a ∧ (b ∨ c) ]
  ex1-b = ⇒I (∨E (ax zero) (∧I (∧El (ax zero)) (∨Il (∧Er (ax zero)))) (∧I (∧El (ax zero)) (∨Ir (∧Er (ax zero)))))

  ex2 : NJ[ ． ⨾ ¬ (a ∨ b) ⊢ ¬ a ∧ ¬ b ]
  ex2 = ∧I (¬I (¬E (ax (suc zero)) (∨Il (ax zero)))) (¬I (¬E (ax (suc zero)) (∨Ir (ax zero))))


  ex4aI : ∀ {Γ Δ A B C} → admissible (rule ((Γ ⨾ A ⨾ B ⨾⨾ Δ ⊢ C) ∷ []) (Γ ⨾ A ∧ B ⨾⨾ Δ ⊢ C))
  ex4aI {Δ = ．} (ax zero , tt) = ∧Er (ax zero)
  ex4aI {Δ = ．} (ax (suc zero) , tt) = ∧El (ax zero)
  ex4aI {Δ = ．} (ax (suc (suc i)) , tt) = ax (suc i)
  ex4aI {Δ = Δ ⨾ ϕ} (ax zero , tt) = ax zero
  ex4aI {Γ} {Δ ⨾ ϕ} {A} {B} {C} (ax (suc i) , tt) = wk-admissible _ _ _ (ex4aI (ax i , tt) , tt)
  ex4aI (⊥E Π , tt) = ⊥E (ex4aI (Π , tt))
  ex4aI (⊤I , tt) = ⊤I
  ex4aI {Δ = Δ} {C = C ⇒ D} (⇒I Π , tt) = ⇒I (ex4aI {Δ = Δ ⨾ C} (Π , tt))
  ex4aI (⇒E {B = D} Π Π₁ , tt) = ⇒E {B = D} (ex4aI (Π , tt)) (ex4aI (Π₁ , tt))
  ex4aI {Δ = Δ} {C = ¬ C} (¬I Π , tt) = ¬I (ex4aI {Δ = Δ ⨾ C} (Π , tt))
  ex4aI (¬E {A = D} Π Π₁ , tt) = ¬E (ex4aI (Π , tt)) (ex4aI (Π₁ , tt))
  ex4aI (∧I Π Π₁ , tt) = ∧I (ex4aI (Π , tt)) (ex4aI (Π₁ , tt))
  ex4aI (∧El Π , tt) = ∧El (ex4aI (Π , tt))
  ex4aI (∧Er Π , tt) = ∧Er (ex4aI (Π , tt))
  ex4aI (∨Il Π , tt) = ∨Il (ex4aI (Π , tt))
  ex4aI (∨Ir Π , tt) = ∨Ir (ex4aI (Π , tt))
  ex4aI {Δ = Δ} (∨E {A = D} {B = E} Π Π₁ Π₂ , tt) = ∨E {A = D} {B = E} (ex4aI (Π , tt)) (ex4aI {Δ = Δ ⨾ D} (Π₁ , tt)) (ex4aI {Δ = Δ ⨾ E} (Π₂ , tt))

  ex4aE : ∀ {Γ Δ A B C} → admissible (rule ((Γ ⨾ A ∧ B ⨾⨾ Δ ⊢ C) ∷ []) (Γ ⨾ A ⨾ B ⨾⨾ Δ ⊢ C))
  ex4aE {Δ = ．} (ax zero , tt) = ∧I (ax (suc zero)) (ax zero)
  ex4aE {Δ = ．} (ax (suc i) , tt) = ax (suc (suc i))
  ex4aE {Δ = Δ ⨾ ϕ} (ax zero , tt) = ax zero
  ex4aE {Δ = Δ ⨾ ϕ} (ax (suc i) , tt) = wk-admissible _ _ _ (ex4aE (ax i , tt) , tt)
  ex4aE (⊥E Π , tt) = ⊥E (ex4aE (Π , tt))
  ex4aE (⊤I , tt) = ⊤I
  ex4aE {Δ = Δ} {C = C ⇒ D} (⇒I Π , tt) = ⇒I (ex4aE {Δ = Δ ⨾ C} (Π , tt))
  ex4aE (⇒E Π Π₁ , tt) = ⇒E (ex4aE (Π , tt)) (ex4aE (Π₁ , tt))
  ex4aE {Δ = Δ} {C = ¬ C} (¬I Π , tt) = ¬I (ex4aE {Δ = Δ ⨾ C} (Π , tt))
  ex4aE (¬E Π Π₁ , tt) = ¬E (ex4aE (Π , tt)) (ex4aE (Π₁ , tt))
  ex4aE (∧I Π Π₁ , tt) = ∧I (ex4aE (Π , tt)) (ex4aE (Π₁ , tt))
  ex4aE (∧El Π , tt) = ∧El (ex4aE (Π , tt))
  ex4aE (∧Er Π , tt) = ∧Er (ex4aE (Π , tt))
  ex4aE (∨Il Π , tt) = ∨Il (ex4aE (Π , tt))
  ex4aE (∨Ir Π , tt) = ∨Ir (ex4aE (Π , tt))
  ex4aE {Δ = Δ} (∨E {A = D} {B = E} Π Π₁ Π₂ , tt) = ∨E {A = D} {B = E} (ex4aE (Π , tt)) (ex4aE {Δ = Δ ⨾ D} (Π₁ , tt)) (ex4aE {Δ = Δ ⨾ E} (Π₂ , tt))

  ex4b-lem : ∀ {Ξ} Γ → NJ[ Ξ ⨾⨾ Γ ⊢ ∧⋆ Γ ]
  ex4b-lem ． = ⊤I
  ex4b-lem (Γ ⨾ ϕ) = ∧I (wk-admissible _ _ _ (ex4b-lem Γ , tt)) (ax zero)

  ex4b : ∀ Γ Δ A → NJ[ Γ ⨾⨾ Δ ⊢ A ] ↔ NJ[ Γ ⊢ ∧⋆ Δ ⇒ A ]
  ex4b Γ ． A .proj₁ Π = ⇒I (wk-admissible Γ ⊤ A (Π , tt))
  ex4b Γ (Δ ⨾ ϕ) A .proj₁ Π = ⇒I (ex4aI {Δ = ．} (⇒E (wk-admissible _ _ _ (⇒E (wk-admissible _ _ _ (ex4b Γ Δ (ϕ ⇒ A) .proj₁ (⇒I Π) , tt)) (ax zero) , tt)) (ax zero) , tt))
  ex4b Γ ． A .proj₂ Π = ⇒E Π ⊤I
  ex4b Γ (Δ ⨾ ϕ) A .proj₂ Π = ⇒E (wk⋆-admissible Γ (Δ ⨾ ϕ) _ (Π , tt)) (∧I (op-admissible (Γ ⨾⨾ Δ ⨾ ϕ) Δ (lem Γ Δ ϕ) (lem' Δ , tt)) (ax zero))
    where

    lem : ∀ Γ Δ ϕ → Δ ⊆ ((Γ ⨾⨾ Δ) ⨾ ϕ)
    lem Γ (Δ ⨾ ψ) ϕ zero = suc zero , refl
    lem Γ (Δ ⨾ ψ) ϕ (suc i) rewrite lem Γ Δ ψ i .proj₂ = suc (lem Γ Δ ψ i .proj₁) , refl

    lem' : ∀ Γ → NJ[ Γ ⊢ ∧⋆ Γ ]
    lem' ． = ⊤I
    lem' (Γ ⨾ ϕ) = ∧I (wk-admissible _ _ _ (lem' Γ , tt)) (ax zero)

  ex5a : ∀ Γ Δ A B → (∀ Ξ → admissible (rule ((Ξ ⨾⨾ Γ ⊢ A) ∷ []) (Ξ ⨾⨾ Δ ⊢ B))) ↔ (∀ Ξ → NJ[ Ξ ⊢ (∧⋆ Γ ⇒ A) ∧ ∧⋆ Δ ⇒ B ])
  ex5a Γ Δ A B .proj₁ h Ξ = ⇒I (ex4aI {Δ = ．} ((⇒E (ex4b (Ξ ⨾ ∧⋆ Γ ⇒ A ⨾ ∧⋆ Δ) Δ B .proj₁ (h _ ((⇒E lem (ex4b-lem Γ)) , tt))) (ax zero)) , tt))
    where

    lem : NJ[ Ξ ⨾ ∧⋆ Γ ⇒ A ⨾ ∧⋆ Δ ⨾⨾ Γ ⊢ ∧⋆ Γ ⇒ A ]
    lem = wk⋆-admissible _ Γ _ (ax (suc zero) , tt)

  ex5a Γ Δ A B .proj₂ h Ξ (Π , tt) = ⇒E (h (Ξ ⨾⨾ Δ)) (∧I (⇒I (op-admissible _ _ (lem Ξ Δ _) ((⇒E (wk-admissible _ _ _ (ex4b Ξ Γ A .proj₁ Π , tt)) (ax zero)) , tt))) (ex4b-lem Δ))
    where

    lem : ∀ Ξ Δ ϕ → Ξ ⨾ ϕ ⊆ (Ξ ⨾⨾ Δ) ⨾ ϕ
    lem Ξ Δ ϕ zero = zero , refl
    lem Ξ ． ϕ (suc i) = suc i , refl
    lem Ξ (Δ ⨾ ψ) ϕ (suc i) rewrite lem Ξ Δ ψ (suc i) .proj₂ = suc (lem Ξ Δ ψ (suc i) .proj₁) , refl


  curry : ∀ Γ A B C → NJ[ Γ ⊢ A ∧ B ⇒ C ] ↔ NJ[ Γ ⊢ A ⇒ B ⇒ C ]
  curry Γ A B C .proj₁ Π = ⇒I (⇒I (⇒E (wk⋆-admissible Γ (． ⨾ A ⨾ B) (A ∧ B ⇒ C) (Π , tt)) (∧I (ax (suc zero)) (ax zero))))
  curry Γ A B C .proj₂ Π = ⇒I (⇒E (⇒E (wk-admissible Γ (A ∧ B) (A ⇒ B ⇒ C) (Π , tt)) (∧El (ax zero))) (∧Er (ax zero)))

  curry⋆ : ∀ Γ Δ ϕ → NJ[ Γ ⊢ ∧⋆ Δ ⇒ ϕ ] ↔ NJ[ Γ ⊢ Δ ⇒⋆ ϕ ]
  curry⋆ Γ ． ϕ .proj₁ Π = ⇒E Π ⊤I
  curry⋆ Γ ． ϕ .proj₂ Π = ⇒I (wk-admissible _ _ _ (Π , tt))
  curry⋆ Γ (Δ ⨾ ψ) ϕ .proj₁ Π = ⇒I (curry⋆ (Γ ⨾ ψ) Δ ϕ .proj₁ (⇒I (⇒E (⇒E (wk⋆-admissible _ (． ⨾ _ ⨾ _) _ (curry _ _ _ _ .proj₁ Π , tt)) (ax zero)) (ax (suc zero)))))
  curry⋆ Γ (Δ ⨾ ψ) ϕ .proj₂ Π = ⇒I (⇒E (curry⋆ _ _ _ .proj₂ (⇒E (wk-admissible _ _ _ (Π , tt)) (∧Er (ax zero)))) (∧El (ax zero)))

  ex6-∧I : ∀ Γ Δ A B → admissible (rule ((Γ ⊢ A) ∷ (Δ ⊢ B) ∷ []) (Γ ⨾⨾ Δ ⊢ A ∧ B))
  ex6-∧I Γ Δ A B (Π , Π₁ , tt) = ∧I (wk⋆-admissible Γ Δ _ (Π , tt)) (wk⋆'-admissible Δ Γ _ (Π₁ , tt))

  ex6-¬E : ∀ Γ Δ A → admissible (rule ((Γ ⊢ ¬ A) ∷ (Δ ⊢ A) ∷ []) (Γ ⨾⨾ Δ ⊢ ⊥))
  ex6-¬E Γ Δ A (Π , Π₁ , tt) = ¬E (wk⋆-admissible Γ Δ _ (Π , tt)) (wk⋆'-admissible Δ Γ _ (Π₁ , tt))

  ex6-⇒E : ∀ Γ Δ A B → admissible (rule ((Γ ⊢ A ⇒ B) ∷ (Δ ⊢ A) ∷ []) (Γ ⨾⨾ Δ ⊢ B))
  ex6-⇒E Γ Δ A B (Π , Π₁ , tt) = ⇒E (wk⋆-admissible Γ Δ _ (Π , tt)) (wk⋆'-admissible Δ Γ _ (Π₁ , tt))

  ex6-∨E : ∀ Γ Δ Σ A B C → admissible (rule ((Γ ⊢ A ∨ B) ∷ (Δ ⨾ A ⊢ C) ∷ (Σ ⨾ B ⊢ C) ∷ []) (Γ ⨾⨾ Δ ⨾⨾ Σ ⊢ C))
  ex6-∨E Γ Δ Σ A B C (Π , Π₁ , Π₂ , tt) = ∨E part-a part-b part-c
    where
    part-a : NJ[ Γ ⨾⨾ Δ ⨾⨾ Σ ⊢ A ∨ B ]
    part-a = wk⋆-admissible (Γ ⨾⨾ Δ) Σ _ ((wk⋆-admissible Γ Δ _ (Π , tt)) , tt)

    part-b : NJ[ Γ ⨾⨾ Δ ⨾⨾ Σ ⨾ A ⊢ C ]
    part-b = op-admissible (Γ ⨾⨾ Δ ⨾⨾ Σ ⨾ A) (Γ ⨾⨾ Δ ⨾ A) (⨾⊆⨾ (⊆⨾⨾-1 (Γ ⨾⨾ Δ) Σ))
            (op-admissible (Γ ⨾⨾ Δ ⨾ A) (Δ ⨾ A) (⨾⊆⨾ (⊆⨾⨾-2 Δ Γ)) (Π₁ , tt) , tt)

    part-c : NJ[ Γ ⨾⨾ Δ ⨾⨾ Σ ⨾ B ⊢ C ]
    part-c = op-admissible (Γ ⨾⨾ Δ ⨾⨾ Σ ⨾ B) (Σ ⨾ B) (⨾⊆⨾ (⊆⨾⨾-2 Σ (Γ ⨾⨾ Δ))) (Π₂ , tt)


  ex7-⊤ : Formula
  ex7-⊤ = ⊥ ⇒ ⊥

  ex7-⊤I-derivable : ∀ Γ → derivable (rule [] (Γ ⊢ ex7-⊤))
  ex7-⊤I-derivable Γ = ⇒I (ax zero)


  ex7-¬_ : Formula → Formula
  ex7-¬ ϕ = ϕ ⇒ ⊥

  ex7-¬I-derivable : ∀ Γ A → derivable (rule ((Γ ⨾ A ⊢ ⊥) ∷ []) (Γ ⊢ ex7-¬ A))
  ex7-¬I-derivable Γ A = ⇒I (prem zero refl)

  ex7-¬E-derivable : ∀ Γ A → derivable (rule ((Γ ⊢ A) ∷ (Γ ⊢ ex7-¬ A) ∷ []) (Γ ⊢ ⊥))
  ex7-¬E-derivable Γ A = ⇒E (prem (suc zero) refl) (prem zero refl)

  ex8a : NJ[ ． ⊢ a ⇒ ¬ ¬ a ]
  ex8a = ⇒I (¬I (¬E (ax zero) (ax (suc zero))))

  ex8b : NJ[ ． ⊢ ¬ (a ∧ ¬ a) ]
  ex8b = ¬I (¬E (∧Er (ax zero)) (∧El (ax zero)))

  ex8c : NJ[ ． ⊢ ¬ ¬ ¬ a ⇒ ¬ a ]
  ex8c = ⇒I (¬I (¬E (ax (suc (zero))) (¬I (¬E (ax zero) (ax (suc zero))))))

  ex8d : NJ[ ． ⊢ ¬ ¬ (a ∨ ¬ a) ]
  ex8d = ¬I (¬E (¬I (¬E (ax (suc zero)) (∨Ir (ax zero)))) (¬I (¬E (ax (suc zero)) (∨Il (ax zero)))))

  ¬[_]_ : Formula → Formula → Formula
  ¬[ R ] A = A ⇒ R


  ex9 : ∀ R → (∀ Γ A → NJ[ Γ ⊢ ¬[ R ] A ] ↔ NJ[ Γ ⊢ ¬ A ]) ↔ ∀ Γ → NJ[ Γ ⊢ ¬ R ]
  ex9 R .proj₁ h Γ = h Γ R .proj₁ (⇒I (ax zero))
  ex9 R .proj₂ ¬R Γ A .proj₁ Π = ¬I (¬E (¬R (Γ ⨾ A)) (⇒E (wk-admissible _ _ _ (Π , tt)) (ax zero)))
  ex9 R .proj₂ ¬R Γ A .proj₂ Π = ⇒I (⊥E (¬E (wk-admissible _ _ _ (Π , tt)) (ax zero)))


module CourseExercises where
  ex1-a : NJ[ ． ⊢ a ⇒ a ⇒ a ]
  ex1-a = ⇒I (⇒I (ax zero))

  ex1-b : NJ[ ． ⊢ ((a ⇒ a) ⇒ b) ⇒ b ]
  ex1-b = ⇒I (⇒E (ax zero) (⇒I (ax zero)))

  ex2 : NJ[ ． ⨾ ¬ a ∨ ¬ b ⊢ ¬ (a ∧ b) ]
  ex2 = ¬I (∨E (ax (suc zero)) (¬E (ax zero) (∧El (ax (suc zero)))) (¬E (ax zero) (∧Er (ax (suc zero)))))

  ex7-a : ∀ Γ A B → derivable (rule ((Γ ⨾ A ⊢ B) ∷ (Γ ⨾ B ⊢ A) ∷ []) (Γ ⊢ A ⇔ B))
  ex7-a Γ A B = ∧I (⇒I (prem zero refl)) (⇒I (prem (suc zero) refl))

  ex7-b : ∀ Γ A B → derivable (rule ((Γ ⊢ A ⇔ B) ∷ (Γ ⊢ B) ∷ []) (Γ ⊢ A))
  ex7-b Γ A B = ⇒E (∧Er (prem zero refl)) (prem (suc zero) refl)

  ex7-c : ∀ Γ A B → derivable (rule ((Γ ⊢ A ⇔ B) ∷ (Γ ⊢ A) ∷ []) (Γ ⊢ B))
  ex7-c Γ A B = ⇒E (∧El (prem zero refl)) (prem (suc zero) refl)

  ex10 : ∀ Γ A B → NJ[ Γ ⨾ A ⊢ B ] → NJ[ Γ ⨾ ¬ B ⊢ ¬ A ]
  ex10 Γ A B Π = ¬I (¬E (ax (suc zero)) (op-admissible (Γ ⨾ ¬ B ⨾ A) (Γ ⨾ A) lem (Π , tt)))
    where
    lem : ∀ {Γ} → Γ ⨾ A ⊆ Γ ⨾ ¬ B ⨾ A
    lem zero = zero , refl
    lem (suc i) = (suc (suc i)) , refl


  _↔_↔_ : Set → Set → Set → Set
  p ↔ q ↔ r = (p → q) × (q → r) × (r → p)

  ex12 : (∀ A → NJ[ ． ⊢ A ]) ↔ (∀ A → NJ[ ． ⊢ A ∧ ¬ A ]) ↔ NJ[ ． ⊢ ⊥ ]
  ex12 .proj₁ ⊢A A = ⊢A (A ∧ ¬ A)
  ex12 .proj₂ .proj₁ ⊢A∧¬A = ¬E (∧Er (⊢A∧¬A ⊤)) ⊤I
  ex12 .proj₂ .proj₂ ⊢⊥ A = ⊥E ⊢⊥


