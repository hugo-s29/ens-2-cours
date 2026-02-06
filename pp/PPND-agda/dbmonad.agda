open import Agda.Primitive
open import Data.Bool using (if_then_else_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver
open import Tactic.Cong
open import Data.Unit using (tt) renaming (⊤ to Unit)
open import Data.Empty renaming (⊥ to False)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂ ; Σ)
open import Data.Sum hiding (map)
open import Data.String using (String)
open import Data.List renaming (length to len) hiding (fromMaybe ; [_] ; map) 
open import Data.Maybe renaming (map to omap)
open import Data.Fin using (Fin ; suc ; zero ; toℕ ; compare ; less ; equal ; greater ; _↑ˡ_)
open import Function.Base
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Relation.Nullary.Decidable hiding (False ; map)

open ≡-Reasoning

open import base
open import NJ-impl renaming (Formula to Type)

infixl 15 _·_
infixl 10 _∘F_
infix 5 _≈_
infix 5 _⇒-nat_

data Term (X : Set) : Set where
  ⦅_⦆ : X → Term X
  λ[_]_ : Type → Term (Maybe X) → Term X
  _·_ : Term X → Term X → Term X

map : ∀ {X Y} → (X → Y) → Term X → Term Y
map f ⦅ x ⦆ = ⦅ f x ⦆
map f (λ[ A ] M) = λ[ A ] map (omap f) M
map f (M · N) = map f M · map f N

_≈_ : {X Y : Set} → (X → Y) → (X → Y) → Set
f ≈ g = ∀ x → f x ≡ g x

cong' : {X Y Z : Set} (f : Y → Z) {g h : X → Y} → g ≈ h → f ∘ g ≈ f ∘ h
cong' f p = cong f ∘ p

sym' : {X Y : Set} {f g : X → Y} → f ≈ g → g ≈ f
sym' p = sym ∘ p

private
  map-≡-lem : {X Y : Set} → {f g : X → Y} → f ≈ g → omap f ≈ omap g
  map-≡-lem p (just x) rewrite p x = refl
  map-≡-lem p nothing = refl

map-≡ : ∀ {X Y} → (f g : X → Y) → f ≈ g → map f ≈ map g
map-≡ f g p ⦅ x ⦆ rewrite p x = refl
map-≡ f g p (λ[ A ] M) rewrite map-≡ (omap f) (omap g) (map-≡-lem p) M = refl
map-≡ f g p (M · N) rewrite map-≡ f g p M rewrite map-≡ f g p N = refl

private
  map-id-lem : {X : Set} → (x : Maybe X) → omap id x ≡ id x
  map-id-lem (just x) = refl
  map-id-lem nothing = refl

map-id : {X : Set} → (M : Term X) → map id M ≡ M
map-id ⦅ x ⦆ = refl
map-id (λ[ A ] M) rewrite map-≡ (omap id) id map-id-lem M rewrite map-id M = refl
map-id (M · N) rewrite map-id M rewrite map-id N = refl


private
  map-∘-lem : {X Y Z : Set} {f : X → Y} {g : Y → Z} → omap (g ∘ f) ≈ omap g ∘ omap f
  map-∘-lem (just x) = refl
  map-∘-lem nothing = refl

map-∘ : {X Y Z : Set} (f : X → Y) (g : Y → Z) → map (g ∘ f) ≈ map g ∘ map f
map-∘ f g ⦅ x ⦆ = refl
map-∘ f g (λ[ A ] M) rewrite map-≡ (omap (g ∘ f)) (omap g ∘ omap f) map-∘-lem M rewrite map-∘ (omap f) (omap g) M = refl
map-∘ f g (M · N) rewrite map-∘ f g M rewrite map-∘ f g N = refl


map-opt : ∀ {X} → (Term (Maybe X)) → Maybe (Term X)
map-opt ⦅ just x ⦆ = just ⦅ x ⦆
map-opt ⦅ nothing ⦆ = nothing
map-opt (λ[ A ] M) with map-opt M
... | nothing = nothing
... | just M = just (λ[ A ] M)
map-opt (M · N) with map-opt M
... | nothing = nothing
... | just M with map-opt N
... | nothing = nothing
... | just N = just (M · N)

map-opt' : ∀ {X} → Maybe (Term X) → Term (Maybe X)
map-opt' (just ⦅ x ⦆) = ⦅ just x ⦆
map-opt' (just (λ[ A ] M)) = λ[ A ] map-opt' (just M)
map-opt' (just (M · N)) = map-opt' (just M) · map-opt' (just N)
map-opt' nothing = ⦅ nothing ⦆

bind : ∀ {X Y} → (X → Term Y) → Term X → Term Y
bind f ⦅ x ⦆ = f x
bind f (λ[ A ] M) = λ[ A ] bind (map-opt' ∘ omap f) M
bind f (M · N) = bind f M · bind f N

μ : ∀ {X} → Term (Term X) → Term X
μ = bind id

η : ∀ {X} → X → Term X
η = ⦅_⦆

private
  bind-≡-lem : ∀ {X Y} → {f g : X → Term Y} → f ≈ g → map-opt' ∘ (omap f) ≈ map-opt' ∘ (omap g)
  bind-≡-lem p (just x) = cong (map-opt' ∘ just) (p x)
  bind-≡-lem p nothing = refl

bind-≡ : ∀ {X Y} → {f g : X → Term Y} → f ≈ g → bind f ≈ bind g
bind-≡ p ⦅ x ⦆ = p x
bind-≡ p (λ[ A ] M) rewrite bind-≡ (bind-≡-lem p) M = refl
bind-≡ p (M · N) rewrite bind-≡ p M rewrite bind-≡ p N = refl


record Functor : Set₁ where
  field
    func : Set → Set
    fmap : ∀ {A B} → (A → B) → func A → func B
    fmap-≈ : ∀ {A B} {f g : A → B} → f ≈ g → fmap f ≈ fmap g
    fmap-id : ∀ {A} → fmap id ≈ (id {A = func A})
    fmap-∘ : ∀ {A B C} (f : A → B) (g : B → C) → fmap (g ∘ f) ≈ fmap g ∘ fmap f

open Functor

_∘F_ : Functor → Functor → Functor
(F ∘F G) .func = func F ∘ func G
(F ∘F G) .fmap = fmap F ∘ fmap G
(F ∘F G) .fmap-≈ = fmap-≈ F ∘ fmap-≈ G
(F ∘F G) .fmap-id x rewrite fmap-≈ F (fmap-id G) x = fmap-id F x
(F ∘F G) .fmap-∘ f g x rewrite fmap-≈ F (fmap-∘ G f g) x = fmap-∘ F (fmap G f) (fmap G g) x

_⇒-nat_ : Functor → Functor → Set₁
F ⇒-nat G = Σ (∀ x → func F x → func G x) λ η → ∀ x y → (f : x → y) → fmap G f ∘ η x ≈ η y ∘ fmap F f

TermF : Functor
TermF = record { func = Term ; fmap = map ; fmap-id = map-id ; fmap-∘ = map-∘ ; fmap-≈ = map-≡ _ _ }

{-
private
  bind-η-lem : ∀ {X} (M : Term (Maybe X)) → bind (map-opt' ∘ omap η) M ≡ M
  bind-η-lem ⦅ just x₁ ⦆ = refl
  bind-η-lem ⦅ nothing ⦆ = refl
  bind-η-lem (λ[ A ] M) = {!!}
  bind-η-lem (M · M₁) = {!!}

bind-η : ∀ {X} → bind η ≈ id {A = Term X}
bind-η ⦅ x ⦆ = refl
bind-η (λ[ A ] M) = cong (λ[ A ]_) {!(λ x₁ → map-opt' (omap η x₁))!}
bind-η (M · N) = {!!}


μ-nat : TermF ∘F TermF ⇒-nat TermF
μ-nat = (λ X → μ {X}) , {!!}
  where

  map² : ∀ {X Y} → (X → Y) → Term (Term X) → Term (Term Y)
  map² = map ∘ map

  lem : ∀ {X Y : Set} → (f : X → Y) → μ ∘ map² f ≈ map f ∘ μ
  lem f ⦅ x ⦆ = refl
  lem f (λ[ A ] M) = {!!}
  lem f (M · N) rewrite lem f M rewrite lem f N = refl



μ-natural : ∀ {X Y} → (f : X → Y) → μ ∘ map² f ≈ map f ∘ μ
μ-natural f ⦅ M ⦆ = refl
μ-natural f (λ[ A ] M) =
  λ[ A ] bind (map-opt' ∘ omap id) (map (omap (map f)) M)
  ≡⟨ {!!} ⟩
  {!!}
  ≡⟨ {!!} ⟩
  (λ[ A ] map (omap f) (bind map-opt' M))
  ≡⟨ cong (λ[ A ]_ ∘ map (omap f)) (bind-≡ (cong map-opt' ∘ sym ∘ map-id-lem) M) ⟩
  (λ[ A ] map (omap f) (bind (map-opt' ∘ omap id) M)) ∎
μ-natural f (M · M₁) = {!!}

-- Monad laws

-}
