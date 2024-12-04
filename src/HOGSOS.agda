{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import Level
open import Data.Product using (_,_)

open import Categories.Category.Core
open import Categories.Functor hiding (id)

open import Categories.NaturalTransformation.Dinatural
open import Categories.Functor.Bifunctor
open import Categories.FreeObjects.Free
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Algebra

open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Category.Cocartesian

module HOGSOS {o ℓ e} (C : Category o ℓ e) (cartesian : Cartesian C) (cocartesian : Cocartesian C) (Σ : Endofunctor C) (B : Bifunctor (Category.op C) C C) where
  open Category C
  open Equiv
  open Cartesian cartesian
  open BinaryProducts products
  open Cocartesian cocartesian

  module Σ = Functor Σ
  module B = Bifunctor B

  algebraForgetfulF : Functor (F-Algebras Σ) C
  algebraForgetfulF = record
    { F₀ = λ X → F-Algebra.A X
    ; F₁ = λ h → F-Algebra-Morphism.f h
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ eq → eq
    }

  module _ {freeAlgebras : ∀ X → FreeObject {C = C} {D = F-Algebras Σ} algebraForgetfulF X} where
    Σ* : Functor C (F-Algebras Σ)
    Σ* = FO⇒Functor algebraForgetfulF freeAlgebras
    module Σ* = Functor Σ*

    open F-Algebra using () renaming (A to ⟦_⟧)
    open F-Algebra-Morphism using () renaming (f to ⟪_⟫)

    record law : Set (o ⊔ ℓ ⊔ e) where
      field
        ρ : ∀ X Y → Σ.F₀ (X × B.F₀ (X , Y)) ⇒ B.F₀ (X , ⟦ Σ*.F₀ (X + Y) ⟧)
        natural : ∀ {X} {Y} {Y'} (f : Y ⇒ Y') → B.F₁ (id , (⟪ Σ*.₁ (id +₁ f)⟫)) ∘ ρ X Y ≈ ρ X Y' ∘ Σ.F₁ (id ⁂ (B.F₁ (id , f)))
        dinatural : ∀ {X} {Y} {X'} (f : X ⇒ X') → B.F₁ (id , ⟪ Σ*.₁ (f +₁ id) ⟫) ∘ ρ X Y ∘ Σ.F₁ (id ⁂ B.F₁ (f , id)) ≈ B.F₁ (f , ⟪ Σ*.₁ (id +₁ id) ⟫) ∘ ρ X' Y ∘ Σ.F₁ (f ⁂ B.₁ (id , id))