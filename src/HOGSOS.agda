open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core
open import Categories.Functor hiding (id)

open import Categories.Monad hiding (id)
open import Categories.Category.Construction.Functors
open import Category.Construction.Monads
open import Categories.NaturalTransformation.Dinatural
open import Categories.Functor.Bifunctor
open import Categories.FreeObjects.Free

open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian

module HOGSOS {o ℓ e} (C : Category o ℓ e) (cartesian : Cartesian C) (cocartesian : Cocartesian C) (Σ : Endofunctor C) (B : Bifunctor C (Category.op C) C) where
  open Category C
  open Equiv
  open Cartesian cartesian
  open BinaryProducts products
  open Cocartesian cocartesian

  module Σ = Functor Σ
  module B = Bifunctor B

  monadForgetfulF : Functor (Monads C) (Functors C C)
  monadForgetfulF = record
    { F₀ = λ M → Monad.F M
    ; F₁ = λ α → Monad⇒.α α
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ eq → eq
    }

  module _ {freeMonad : FreeObject {C = Functors C C} {D = Monads C} monadForgetfulF Σ} where
    open FreeObject freeMonad using () renaming (FX to Σ*)
    module Σ* = Monad Σ*

    record law : Set (o ⊔ ℓ ⊔ e) where
      field
        ρ : ∀ X Y → Σ.F₀ (X × B.F₀ (X , Y)) ⇒ B.F₀ (X , Σ*.F.F₀ (X + Y))
        natural : ∀ {X} {Y} {Z} (f : Y ⇒ Z) → ρ X Y ∘ Σ.F₁ (Functor.₁ (X ×-) (B.F₁ (id , f))) ≈ B.F₁ (id , (Σ*.F.₁ (Functor.₁ (X +-) f))) ∘ ρ X Z
        dinatural : ∀ {X} {Y} {Z} (f : X ⇒ Z) → {!   !} ≈ {!   !}