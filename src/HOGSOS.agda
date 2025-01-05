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

open import Categories.Object.Initial

import Categories.Morphism.Reasoning as MR

module HOGSOS {o ℓ e} (C : Category o ℓ e) (cartesian : Cartesian C) (cocartesian : Cocartesian C) (Σ : Endofunctor C) (B : Bifunctor (Category.op C) C C) where
  open Category C
  open Equiv
  open Cartesian cartesian
  open BinaryProducts products
  open Cocartesian cocartesian
  open HomReasoning
  open MR C

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

    record Law : Set (o ⊔ ℓ ⊔ e) where
      field
        ρ : ∀ X Y → Σ.F₀ (X × B.F₀ (X , Y)) ⇒ B.F₀ (X , ⟦ Σ*.F₀ (X + Y) ⟧)
        natural : ∀ {X} {Y} {Y'} (f : Y ⇒ Y') → B.F₁ (id , (⟪ Σ*.₁ (id +₁ f)⟫)) ∘ ρ X Y ≈ ρ X Y' ∘ Σ.F₁ (id ⁂ (B.F₁ (id , f)))
        dinatural : ∀ {X} {Y} {X'} (f : X ⇒ X') → B.F₁ (id , ⟪ Σ*.₁ (f +₁ id) ⟫) ∘ ρ X Y ∘ Σ.F₁ (id ⁂ B.F₁ (f , id)) ≈ B.F₁ (f , ⟪ Σ*.₁ (id +₁ id) ⟫) ∘ ρ X' Y ∘ Σ.F₁ (f ⁂ B.₁ (id , id))

    module _ (law : Law) (ini : Initial (F-Algebras Σ)) (A : F-Algebra Σ) (â : ⟦ Σ*.₀ ⟦ A ⟧ ⟧ ⇒ ⟦ A ⟧) where
      open Initial ini renaming (⊥ to μΣ)
      open F-Algebra μΣ using () renaming (α to ι)
      open F-Algebra A using () renaming (α to a)
      open Law law
      ∇ : ∀ {A} → A + A ⇒ A
      ∇ {A} = [ id , id ]

      private
        spade'-alg : F-Algebra Σ
        spade'-alg = record { A = ⟦ A ⟧ × B.₀ (⟦ A ⟧ , ⟦ A ⟧) ; α = (id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩ }

        spade' : ⟦ μΣ ⟧ ⇒ (⟦ A ⟧ × B.₀ (⟦ A ⟧ , ⟦ A ⟧))
        spade' = ⟪ ! {spade'-alg} ⟫


      spade : ⟦ μΣ ⟧ ⇒ B.₀ (⟦ A ⟧ , ⟦ A ⟧)
      spade = π₂ ∘ spade'
      
      private
        w : ⟦ μΣ ⟧ ⇒ ⟦ A ⟧
        w = π₁ ∘ spade'
        w-it : ⟪ ! {A} ⟫ ≈ w
        w-it = !-unique (record { f = w ; commutes = begin 
          (π₁ ∘ ⟪ ! {spade'-alg} ⟫) ∘ ι ≈⟨ pullʳ (F-Algebra-Morphism.commutes (! {spade'-alg})) ⟩
          π₁ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.F₁ ⟪ ! {spade'-alg} ⟫ ≈⟨ pullˡ (pullˡ project₁) ⟩
          ((id ∘ π₁) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.F₁ ⟪ ! {spade'-alg} ⟫ ≈⟨ (∘-resp-≈ˡ identityˡ ○ project₁) ⟩∘⟨refl ⟩
          (a ∘ Σ.₁ π₁) ∘ Σ.F₁ ⟪ ! {spade'-alg} ⟫ ≈⟨ pullʳ (sym Σ.homomorphism) ⟩
          a ∘ Σ.₁ (π₁ ∘ ⟪ ! {spade'-alg} ⟫) ∎ })

        spade'≈w-spade : spade' ≈ ⟨ w , spade ⟩
        spade'≈w-spade = {!   !}

        spade'-comm : ⟨ w , spade ⟩ ∘ ι ≈ {!   !}
        spade'-comm = {!   !} 

      -- TODO do directly, spade'-comm not needed.
      spade-comm : spade ∘ ι ≈ B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , spade ⟩
      spade-comm = {!   !}

      spade-unique : ∀ (f : ⟦ μΣ ⟧ ⇒ B.₀ (⟦ A ⟧ , ⟦ A ⟧)) 
        → f ∘ ι ≈ B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩
        → f ≈ spade
      spade-unique f f-comm = {!   !}