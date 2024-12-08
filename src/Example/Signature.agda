{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import Data.Nat using (ℕ)
open import Data.Vec as V using (Vec ; lookup ; foldr ; [] ; _∷_ ; updateAt; removeAt)
import Data.Vec.Properties as VP
open import Data.Fin.Base using (fromℕ; Fin)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_) renaming (refl to ≡-refl)

open import Categories.Functor
-- The category of agda types and terminating functions.
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Categories.Category.Cartesian 
open import Categories.Object.Terminal 
open import Categories.Object.Initial 
open import Categories.Category.Cocartesian 
open import Categories.Category.BinaryProducts 
open import Categories.Category.Core
open import Categories.Functor.Algebra
open import Categories.FreeObjects.Free
open import Categories.Category.Construction.F-Algebras

open import Data.Sum
import Data.List as List
open List using ([]; _∷_; List)
open import Data.Unit.Polymorphic using (tt)
open import Data.Product using (Σ; _,_)

open import Level using (Level)

module Example.Signature (o : Level) where
  open Category (Agda o)
  open Equiv
  open HomReasoning
  open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
  open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)

  open Cartesian (Agda-Cartesian o)
  open Cocartesian (Agda-Cocartesian o) renaming (+-unique to []-unique)
  open BinaryProducts products renaming (unique to ⟨⟩-unique)
  open Terminal terminal

  record Signature : Set where
    field
      -- operations
      ops : ℕ

      -- arities
      arts : Vec ℕ ops 
  open Signature

  open ℕ

  Sig-Functor : Signature → Endofunctor (Agda o)
  Sig-Functor record { ops = ops ; arts = arts } .Functor.F₀ X                                                                                  = Σ (Fin ops) (λ op → Vec X (lookup arts op))
  Sig-Functor record { ops = ops ; arts = arts } .Functor.F₁ f (op , args)                                                                      = op , V.map f args
  Sig-Functor record { ops = ops ; arts = arts } .Functor.identity {A} (op , args) rewrite VP.map-id args                                       = ≡-refl
  Sig-Functor record { ops = ops ; arts = arts } .Functor.homomorphism {f = f} {g = g} (op , args) rewrite VP.map-∘ g f args                    = ≡-refl
  Sig-Functor record { ops = ops ; arts = arts } .Functor.F-resp-≈ {f = f} {g = g} f≈g (op , args) rewrite VP.map-cong {f = f} {g = g} f≈g args = ≡-refl

  Σₘₒₙ : Signature
  Σₘₒₙ = record { ops = 2 ; arts = 0 ∷ 2 ∷ [] }

  -- Terms with variables
  data _*_ (Σ : Signature) (X : Set o) : Set o where
    Var : X → Σ * X
    App : (f : Fin(ops Σ)) → Vec (Σ * X) (lookup (arts Σ) f)  → Σ * X

  Mon-Algebra : (V : Set o) → F-Algebra (Sig-Functor Σₘₒₙ)
  Mon-Algebra V .F-Algebra.A = Σₘₒₙ * V 
  Mon-Algebra V .F-Algebra.α (op , args) = App op args

  Σ-Algebra : (V : Set o) → (Σ : Signature) → F-Algebra (Sig-Functor Σ)
  Σ-Algebra V Σ@record { ops = ops ; arts = arts } = record 
    { A = Σ * V 
    ; α = λ (op , args) → App op args 
    }

  AlgebraForgetfulF : ∀ (F : Endofunctor (Agda o)) → Functor (F-Algebras F) (Agda o)
  AlgebraForgetfulF F = record
    { F₀ = λ A → F-Algebra.A A
    ; F₁ = λ f → F-Algebra-Morphism.f f
    ; identity = λ _ → ≡-refl
    ; homomorphism = λ _ → ≡-refl
    ; F-resp-≈ = λ eq → eq
    }


  Σ-free : ∀ (Σ : Signature) (V : Set o) → FreeObject (AlgebraForgetfulF (Sig-Functor Σ)) V
  Σ-free Σ V .FreeObject.FX = Σ-Algebra V Σ
  Σ-free Σ V .FreeObject.η = Var
  (Σ-free Σ V FreeObject.*) {A} f .F-Algebra-Morphism.f (Var v) = f v
  (Σ-free Σ V FreeObject.*) {A} f .F-Algebra-Morphism.f (App op args) = F-Algebra.α A (op , (V.map {! (Σ-free Σ V FreeObject.*) {A} f .F-Algebra-Morphism.f  !} args))
  Σ-free Σ V .FreeObject._* {A} f .F-Algebra-Morphism.commutes = {!   !}
  Σ-free Σ V .FreeObject.*-lift = {!   !}
  Σ-free Σ V .FreeObject.*-uniq = {!   !}
