{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import Level

-- The category of agda types and terminating functions.
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Category
open import Data.Product using (_,_)

open import Categories.Category.Construction.F-Algebras
open import Categories.FreeObjects.Free
open import Categories.Object.Initial

open import Axiom.Extensionality.Propositional using (Extensionality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_) renaming (refl to ≡-refl)

open import Data.Sum

open import Data.Vec using (_∷_; [])

module Example.Combinatory (o : Level) (ext : Extensionality o o) where
  open Category (Agda o)
  open HomReasoning
  open Equiv
  open import Example.Signature o

  xCL : Signature
  xCL = record { ops = 7 ; arts = 0 ∷ 0 ∷ 0 ∷ 1 ∷ 1 ∷ 2 ∷ 2 ∷ [] }

  Σ : Endofunctor (Agda o)
  Σ = Sig-Functor xCL

  B : Bifunctor (Category.op (Agda o)) (Agda o) (Agda o)
  B .Functor.F₀ (X , Y) = Y ⊎ (X → Y)
  B .Functor.F₁ {A , B} {C , D} (f , g) (inj₁ x) = inj₁ (g x)
  B .Functor.F₁ {A , B} {C , D} (f , g) (inj₂ h) = inj₂ λ x → g (h (f x))
  B .Functor.identity (inj₁ x) = ≡-refl
  B .Functor.identity (inj₂ y) = ≡-refl
  B .Functor.homomorphism (inj₁ x) = ≡-refl
  B .Functor.homomorphism (inj₂ y) = ≡-refl
  B .Functor.F-resp-≈ {A , B} {C , D} {f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) (inj₁ x) = Eq.cong inj₁ (f₂≈g₂ x)
  -- TODO: possible without extensionality??
  B .Functor.F-resp-≈ {A , B} {C , D} {f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) (inj₂ h) = Eq.cong inj₂ (ext helper)
    where
    helper : ∀ (x : C) → f₂ (h (f₁ x)) ≡ g₂ (h (g₁ x))
    helper x rewrite (f₁≈g₁ x) = f₂≈g₂ (h (g₁ x))


  open import HOGSOS (Agda o) (Agda-Cartesian o) (Agda-Cocartesian o) Σ B

  freeAlgebras : ∀ X → FreeObject {C = Agda o} {D = F-Algebras Σ} algebraForgetfulF X
  freeAlgebras X = Σ-free xCL X

  open Laws freeAlgebras

  law : Law
  law = record 
    { ρ = {!   !} 
    ; natural = {!   !} 
    ; dinatural = {!   !} 
    }

  ini : Initial (F-Algebras Σ)
  ini = {!   !}
