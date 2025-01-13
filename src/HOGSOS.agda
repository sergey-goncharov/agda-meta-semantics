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
        natural : ∀ {X} {Y} {Y'} (f : Y ⇒ Y') → B.₁ (id , ⟪ Σ*.₁ (id +₁ f)⟫) ∘ ρ X Y ≈ ρ X Y' ∘ Σ.₁ (id ⁂ B.₁ (id , f))
        dinatural : ∀ {X} {Y} {X'} (f : X ⇒ X') → B.₁ (id , ⟪ Σ*.₁ (f +₁ id) ⟫) ∘ ρ X Y ∘ Σ.₁ (id ⁂ B.₁ (f , id)) ≈ B.₁ (f , ⟪ Σ*.₁ (id +₁ id) ⟫) ∘ ρ X' Y ∘ Σ.₁ (f ⁂ B.₁ (id , id))

    module Clubsuit (law : Law) (ini : Initial (F-Algebras Σ)) where
      open Initial ini renaming (⊥ to μΣ)
      open F-Algebra μΣ using () renaming (α to ι)
      open Law law

      module _ (A : F-Algebra Σ) where
        open F-Algebra A using () renaming (α to a)
      
        ∇ : ∀ {A} → A + A ⇒ A
        ∇ {A} = [ id , id ]

        private
          â : ⟦ Σ*.₀ ⟦ A ⟧ ⟧ ⇒ ⟦ A ⟧
          â = ⟪ FreeObject._* {X = ⟦ A ⟧} (freeAlgebras ⟦ A ⟧) {A = A} (id {⟦ A ⟧}) ⟫

          club'-alg : F-Algebra Σ
          club'-alg = record { A = ⟦ A ⟧ × B.₀ (⟦ A ⟧ , ⟦ A ⟧) ; α = (id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩ }

          club' : ⟦ μΣ ⟧ ⇒ (⟦ A ⟧ × B.₀ (⟦ A ⟧ , ⟦ A ⟧))
          club' = ⟪ ! {club'-alg} ⟫

          club'-commutes : club' ∘ ι ≈ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ club'
          club'-commutes = F-Algebra-Morphism.commutes (! {club'-alg})

        _♣ : ⟦ μΣ ⟧ ⇒ B.₀ (⟦ A ⟧ , ⟦ A ⟧)
        _♣ = π₂ ∘ club'

        private
          w : ⟦ μΣ ⟧ ⇒ ⟦ A ⟧
          w = π₁ ∘ club'
          w-comm : w ∘ ι ≈ a ∘ Σ.₁ w
          w-comm = begin 
            w ∘ ι                                                                                ≈⟨ pullʳ club'-commutes ⟩ 
            π₁ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫ ≈⟨ pullˡ (pullˡ (project₁ ○ identityˡ)) ⟩ 
            (π₁ ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫                                    ≈⟨ project₁ ⟩∘⟨refl ⟩ 
            (a ∘ Σ.₁ π₁) ∘ Σ.₁ ⟪ ! ⟫                                                             ≈⟨ pullʳ (sym Σ.homomorphism) ⟩ 
            a ∘ Σ.₁ w                                                                            ∎
          w-it : ⟪ ! {A} ⟫ ≈ w
          w-it = !-unique (record { f = w ; commutes = begin 
            (π₁ ∘ ⟪ ! {club'-alg} ⟫) ∘ ι                                                                     ≈⟨ pullʳ (F-Algebra-Morphism.commutes (! {club'-alg})) ⟩
            π₁ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! {club'-alg} ⟫ ≈⟨ pullˡ (pullˡ project₁) ⟩
            ((id ∘ π₁) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! {club'-alg} ⟫                             ≈⟨ (∘-resp-≈ˡ identityˡ ○ project₁) ⟩∘⟨refl ⟩
            (a ∘ Σ.₁ π₁) ∘ Σ.₁ ⟪ ! {club'-alg} ⟫                                                             ≈⟨ pullʳ (sym Σ.homomorphism) ⟩
            a ∘ Σ.₁ (π₁ ∘ ⟪ ! {club'-alg} ⟫)                                                                 ∎ })

          club'≈w-club : club' ≈ ⟨ w , _♣ ⟩
          club'≈w-club = sym g-η

        ♣-comm : _♣ ∘ ι ≈ B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩
        ♣-comm = begin 
          (π₂ ∘ club') ∘ ι                                                                    ≈⟨ pullʳ club'-commutes ⟩ 
          π₂ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫ ≈⟨ pullˡ (pullˡ project₂) ⟩ 
          ((B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ π₂) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫      ≈⟨ pullʳ project₂ ⟩∘⟨refl ⟩ 
          (B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧) ∘ Σ.₁ club'                             ≈⟨ refl⟩∘⟨ Σ.F-resp-≈ club'≈w-club ⟩ 
          (B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧) ∘ Σ.₁ ⟨ w , _♣ ⟩                      ≈⟨ refl⟩∘⟨ Σ.F-resp-≈ (⟨⟩-cong₂ (sym w-it) refl)⟩ 
          (B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧) ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩              ≈⟨ assoc ⟩
          B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩                ≈˘⟨ pullˡ (sym B.homomorphism) ○ ∘-resp-≈ˡ (B.F-resp-≈ (identity² , refl)) ⟩
          B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩     ∎

        ♣-unique : ∀ (f : ⟦ μΣ ⟧ ⇒ B.₀ (⟦ A ⟧ , ⟦ A ⟧)) 
          → f ∘ ι ≈ B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩
          → f ≈ _♣
        ♣-unique f f-comm = begin 
          f              ≈˘⟨ project₂ ⟩ 
          π₂ ∘ ⟨ w , f ⟩ ≈˘⟨ refl⟩∘⟨ !-unique (record { f = ⟨ w , f ⟩ ; commutes = helper }) ⟩ 
          π₂ ∘ club'    ∎
          where
          helper : ⟨ w , f ⟩ ∘ ι ≈ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟨ w , f ⟩
          helper = begin 
            ⟨ w , f ⟩ ∘ ι                                                                                ≈⟨ ⟨⟩∘ ⟩ 
            ⟨ w ∘ ι , f ∘ ι ⟩                                                                            ≈⟨ ⟨⟩-cong₂ w-comm f-comm ⟩ 
            ⟨ a ∘ Σ.₁ w , B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ refl (pullˡ (sym B.homomorphism ○ B.F-resp-≈ (identity² , refl))) ⟩ 
            ⟨ a ∘ Σ.₁ w , B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩ ⟩            ≈⟨ ⟨⟩-cong₂ refl (∘-resp-≈ʳ (∘-resp-≈ʳ (Σ.F-resp-≈ (⟨⟩-cong₂ w-it refl)))) ⟩ 
            ⟨ a ∘ Σ.₁ w , B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ w , f ⟩ ⟩                    ≈˘⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ (pullʳ (sym Σ.homomorphism ○ Σ.F-resp-≈ project₁)) assoc ⟩ 
            ⟨ a ∘ Σ.₁ π₁ , B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ⟩ ∘ Σ.₁ ⟨ w , f ⟩                   ≈˘⟨ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ refl) ⟩∘⟨refl ⟩ 
            ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟨ w , f ⟩          ∎
