{-# OPTIONS --without-K --allow-unsolved-metas #-}

open import Level
open import Data.Product using (_,_)

open import Categories.Category
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

  ∇ : ∀ {A} → A + A ⇒ A
  ∇ {A} = [ id , id ]

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

  module Laws (freeAlgebras : ∀ X → FreeObject {C = C} {D = F-Algebras Σ} algebraForgetfulF X) where
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

        δ : ⟦ μΣ ⟧ ⇒ ⟦ A ⟧
        δ = π₁ ∘ club'
        
        δ-comm : δ ∘ ι ≈ a ∘ Σ.₁ δ
        δ-comm = begin 
          δ ∘ ι
            ≈⟨ pullʳ club'-commutes ⟩ 
          π₁ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫
            ≈⟨ pullˡ (pullˡ (project₁ ○ identityˡ)) ⟩ 
          (π₁ ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫
            ≈⟨ project₁ ⟩∘⟨refl ⟩ 
          (a ∘ Σ.₁ π₁) ∘ Σ.₁ ⟪ ! ⟫
            ≈⟨ pullʳ (sym Σ.homomorphism) ⟩ 
          a ∘ Σ.₁ δ
          ∎
          
        δ-it : ⟪ ! {A} ⟫ ≈ δ
        δ-it = !-unique (record { f = δ ; commutes = begin 
          (π₁ ∘ ⟪ ! {club'-alg} ⟫) ∘ ι
            ≈⟨ pullʳ (F-Algebra-Morphism.commutes (! {club'-alg})) ⟩
          π₁ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! {club'-alg} ⟫
            ≈⟨ pullˡ (pullˡ project₁) ⟩
          ((id ∘ π₁) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! {club'-alg} ⟫
            ≈⟨ (∘-resp-≈ˡ identityˡ ○ project₁) ⟩∘⟨refl ⟩
          (a ∘ Σ.₁ π₁) ∘ Σ.₁ ⟪ ! {club'-alg} ⟫
            ≈⟨ pullʳ (sym Σ.homomorphism) ⟩
          a ∘ Σ.₁ (π₁ ∘ ⟪ ! {club'-alg} ⟫)
          ∎ })

        club'≈δ-club : club' ≈ ⟨ δ , _♣ ⟩
        club'≈δ-club = sym g-η

        ♣-comm : _♣ ∘ ι ≈ B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩
        ♣-comm = begin 
          (π₂ ∘ club') ∘ ι
            ≈⟨ pullʳ club'-commutes ⟩ 
          π₂ ∘ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫
            ≈⟨ pullˡ (pullˡ project₂) ⟩ 
          ((B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ π₂) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟪ ! ⟫
            ≈⟨ pullʳ project₂ ⟩∘⟨refl ⟩ 
          (B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧) ∘ Σ.₁ club'
            ≈⟨ refl⟩∘⟨ Σ.F-resp-≈ club'≈δ-club ⟩ 
          (B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧) ∘ Σ.₁ ⟨ δ , _♣ ⟩
            ≈⟨ refl⟩∘⟨ Σ.F-resp-≈ (⟨⟩-cong₂ (sym δ-it) refl)⟩ 
          (B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧) ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩
            ≈⟨ assoc ⟩
          B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩
            ≈˘⟨ pullˡ (sym B.homomorphism) ○ ∘-resp-≈ˡ (B.F-resp-≈ (identity² , refl)) ⟩
          B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , _♣ ⟩
         ∎

        ♣-unique : ∀ (f : ⟦ μΣ ⟧ ⇒ B.₀ (⟦ A ⟧ , ⟦ A ⟧)) 
          → f ∘ ι ≈ B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩
          → f ≈ _♣
        ♣-unique f f-comm = begin 
          f              ≈˘⟨ project₂ ⟩ 
          π₂ ∘ ⟨ δ , f ⟩ ≈˘⟨ refl⟩∘⟨ !-unique (record { f = ⟨ δ , f ⟩ ; commutes = helper }) ⟩ 
          π₂ ∘ club'
         ∎
          where
          helper : ⟨ δ , f ⟩ ∘ ι ≈ ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟨ δ , f ⟩
          helper = begin 
            ⟨ δ , f ⟩ ∘ ι
              ≈⟨ ⟨⟩∘ ⟩ 
            ⟨ δ ∘ ι , f ∘ ι ⟩
              ≈⟨ ⟨⟩-cong₂ δ-comm f-comm ⟩ 
            ⟨ a ∘ Σ.₁ δ , B.₁ (id , â) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩ ⟩
              ≈⟨ ⟨⟩-cong₂ refl (pullˡ (sym B.homomorphism ○ B.F-resp-≈ (identity² , refl))) ⟩ 
            ⟨ a ∘ Σ.₁ δ , B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ ⟪ ! {A} ⟫ , f ⟩ ⟩
              ≈⟨ ⟨⟩-cong₂ refl (∘-resp-≈ʳ (∘-resp-≈ʳ (Σ.F-resp-≈ (⟨⟩-cong₂ δ-it refl)))) ⟩ 
            ⟨ a ∘ Σ.₁ δ , B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ∘ Σ.₁ ⟨ δ , f ⟩ ⟩
              ≈˘⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ (pullʳ (sym Σ.homomorphism ○ Σ.F-resp-≈ project₁)) assoc ⟩ 
            ⟨ a ∘ Σ.₁ π₁ , B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ A ⟧ ⟦ A ⟧ ⟩ ∘ Σ.₁ ⟨ δ , f ⟩
              ≈˘⟨ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ identityˡ refl) ⟩∘⟨refl ⟩ 
            ((id ⁂ B.₁ (id , â ∘ ⟪ Σ*.₁ ∇ ⟫)) ∘ ⟨ a ∘ Σ.₁ π₁ , ρ ⟦ A ⟧ ⟦ A ⟧ ⟩) ∘ Σ.₁ ⟨ δ , f ⟩
           ∎

      γ : ⟦ μΣ ⟧ ⇒ B.₀ (⟦ μΣ ⟧ , ⟦ μΣ ⟧)
      γ = (Initial.⊥ ini) ♣

      δ-id : δ μΣ ≈ id
      δ-id = begin 
        δ μΣ 
          ≈˘⟨ δ-it μΣ ⟩ 
        ⟪ ! {μΣ} ⟫ 
          ≈⟨ IsInitial.!-unique (Initial.⊥-is-initial ini) (record { f = id ; commutes = identityˡ ○ introʳ (Functor.identity Σ) }) ⟩ 
        id ∎

      γ-rec : γ ∘ ι ≈ B.₁ (id ,  ⟪ FreeObject._* {X = ⟦ μΣ ⟧ + ⟦ μΣ ⟧} (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) {A = μΣ} ∇ ⟫) ∘ ρ ⟦ μΣ ⟧ ⟦ μΣ ⟧ ∘ Σ.₁ ⟨ id , γ ⟩ 
      γ-rec = begin 
        γ ∘ ι ≈⟨ ♣-comm μΣ ⟩ 
        B.₁ (id , ah) ∘ B.₁ (id , ⟪ Σ*.₁ ∇ ⟫) ∘ ρ ⟦ μΣ ⟧ ⟦ μΣ ⟧ ∘ Σ.₁ ⟨ ⟪ ! {μΣ} ⟫ , γ ⟩ 
          ≈⟨ pullˡ (sym (Functor.homomorphism B) ○ Functor.F-resp-≈ B (identity² , eq)) ⟩ 
        B.₁ (id ,  ⟪ FreeObject._* {X = ⟦ μΣ ⟧ + ⟦ μΣ ⟧} (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) {A = μΣ} ∇ ⟫)  ∘ ρ ⟦ μΣ ⟧ ⟦ μΣ ⟧ ∘ Σ.₁ ⟨ ⟪ ! {μΣ} ⟫ , γ ⟩ 
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (Functor.F-resp-≈ Σ (⟨⟩-cong₂ (δ-it μΣ ○ δ-id) refl))) ⟩
        B.₁ (id ,  ⟪ FreeObject._* {X = ⟦ μΣ ⟧ + ⟦ μΣ ⟧} (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) {A = μΣ} ∇ ⟫)  ∘ ρ ⟦ μΣ ⟧ ⟦ μΣ ⟧ ∘ Σ.₁ ⟨ id , γ ⟩ ∎
        where
        ah = ⟪ FreeObject._* {X = ⟦ μΣ ⟧} (freeAlgebras ⟦ μΣ ⟧) {A = μΣ} (id {⟦ μΣ ⟧}) ⟫
        eq : ah ∘ ⟪ Σ*.₁ ∇ ⟫ ≈ ⟪ FreeObject._* {X = ⟦ μΣ ⟧ + ⟦ μΣ ⟧} (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) {A = μΣ} ∇ ⟫
        eq = FreeObject.*-uniq (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) ∇ ((F-Algebras Σ) [ FreeObject._* {X = ⟦ μΣ ⟧} (freeAlgebras ⟦ μΣ ⟧) {A = μΣ} (id {⟦ μΣ ⟧}) ∘ Σ*.₁ ∇ ]) helper
          where
          helper : (ah ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ FreeObject.η (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) ≈ ∇
          helper = begin 
            (ah ∘ ⟪ Σ*.₁ ∇ ⟫) ∘ FreeObject.η (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) 
              ≈⟨ pullʳ (FreeObject.*-lift (freeAlgebras (⟦ μΣ ⟧ + ⟦ μΣ ⟧)) (FreeObject.η (freeAlgebras ⟦ μΣ ⟧) ∘ ∇)) ⟩ 
            ⟪ FreeObject._* {X = ⟦ μΣ ⟧} (freeAlgebras ⟦ μΣ ⟧) {A = μΣ} (id {⟦ μΣ ⟧}) ⟫ ∘ FreeObject.η (freeAlgebras ⟦ μΣ ⟧) ∘ ∇ 
              ≈⟨ cancelˡ (FreeObject.*-lift (freeAlgebras ⟦ μΣ ⟧) id) ⟩ 
            ∇ ∎

