{-# OPTIONS --safe --without-K #-}

open import Data.Nat using (ℕ)
open import Data.Vec as V using (Vec ; foldr ; [] ; _∷_ ; updateAt; removeAt) renaming (lookup to _!!_)
import Data.Vec.Properties as VP
open import Data.Vec.Relation.Binary.Equality.Propositional using (≋⇒≡; ≡⇒≋)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (_∷_)
open import Data.Fin.Base using (fromℕ; Fin)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_) renaming (refl to ≡-refl)

open import Categories.Functor hiding (id)
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

open F-Algebra-Morphism renaming (f to ⟪_⟫)

open import Data.Sum
import Data.List as List
open List using ([]; _∷_; List)
open import Data.Unit.Polymorphic using (tt)
open import Data.Product using (Σ; _,_)
open import Data.Product.Properties using (Σ-≡,≡→≡)

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

  record Signature : Set where
    field
      -- operations
      ops : ℕ

      -- arities
      arts : Vec ℕ ops
  open Signature

  open ℕ

  Sig-Functor : Signature → Endofunctor (Agda o)
  Sig-Functor record { ops = ops ; arts = arts } .Functor.F₀ X                                                                                  = Σ (Fin ops) (λ op → Vec X (arts !! op))
  Sig-Functor record { ops = ops ; arts = arts } .Functor.F₁ f (op , args)                                                                      = op , V.map f args
  Sig-Functor record { ops = ops ; arts = arts } .Functor.identity {A} (op , args) rewrite VP.map-id args                                       = ≡-refl
  Sig-Functor record { ops = ops ; arts = arts } .Functor.homomorphism {f = f} {g = g} (op , args) rewrite VP.map-∘ g f args                    = ≡-refl
  Sig-Functor record { ops = ops ; arts = arts } .Functor.F-resp-≈ {f = f} {g = g} f≈g (op , args) rewrite VP.map-cong {f = f} {g = g} f≈g args = ≡-refl

  Σₘₒₙ : Signature
  Σₘₒₙ = record { ops = 2 ; arts = 0 ∷ 2 ∷ [] }

  -- Terms with variables
  data _*_ (Σ : Signature) (X : Set o) : Set o where
    Var : X → Σ * X
    App : (f : Fin(ops Σ)) → Vec (Σ * X) (arts Σ !! f) → Σ * X

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
    { F₀ = F-Algebra.A
    ; F₁ = F-Algebra-Morphism.f
    ; identity = λ _ → ≡-refl
    ; homomorphism = λ _ → ≡-refl
    ; F-resp-≈ = λ eq → eq
    }

  module _ (Σ : Signature) (V : Set o) where
    lift : ∀ (A : F-Algebra (Sig-Functor Σ)) (f : V → F-Algebra.A A) → Σ * V → F-Algebra.A A
    lift-vec : ∀ (A : F-Algebra (Sig-Functor Σ)) (f : V → F-Algebra.A A) → (n : ℕ) → (args : Vec (Σ * V) n) → Vec (F-Algebra.A A) n
    
    lift A f (Var v) = f v
    lift A f (App op args) = F-Algebra.α A (op , lift-vec A f (arts Σ !! op) args)
    
    lift-vec A f zero [] = []
    lift-vec A f (suc n) (arg ∷ args) = lift A f arg ∷ lift-vec A f n args
    
    lift-vec-map : ∀ (A : F-Algebra (Sig-Functor Σ)) (f : V → F-Algebra.A A) (n : ℕ) (args : Vec (Σ * V) n) → lift-vec A f n args ≡ V.map (lift A f) args
    lift-vec-map A f zero [] = ≡-refl
    lift-vec-map A f (suc n) (arg ∷ args) = ≋⇒≡ (≡-refl ∷ ≡⇒≋ (lift-vec-map A f n args))

    Σ-free : FreeObject (AlgebraForgetfulF (Sig-Functor Σ)) V
    Σ-free .FreeObject.FX = Σ-Algebra V Σ
    Σ-free .FreeObject.η = Var
    (Σ-free FreeObject.*) {A} f .F-Algebra-Morphism.f = lift A f
    Σ-free .FreeObject._* {A} f .F-Algebra-Morphism.commutes (op , args) = Eq.cong (F-Algebra.α A) (Σ-≡,≡→≡ (≡-refl , lift-vec-map A f (arts Σ !! op) args))
    Σ-free .FreeObject.*-lift f x = ≡-refl
    Σ-free .FreeObject.*-uniq {A} f g eq = uniq
      where
        uniq : ∀ (x : Σ * V) → ⟪ g ⟫ x ≡ ⟪ FreeObject._* Σ-free f ⟫ x
        uniq-vec : (n : ℕ) → (args : Vec (Σ * V) n) → V.map ⟪ g ⟫ args ≡ lift-vec A f n args
        uniq (Var v) = eq v
        uniq (App op args) rewrite F-Algebra-Morphism.commutes g (op , args) = Eq.cong (F-Algebra.α A) (Σ-≡,≡→≡ (≡-refl , uniq-vec (arts Σ !! op) args))
        uniq-vec zero [] = ≡-refl
        uniq-vec (suc n) (arg ∷ args) = ≋⇒≡ ((uniq arg) ∷ ≡⇒≋ (uniq-vec n args))

    -- The general claim should rather be included into the FreeObject module
    lift-var : (lift (Σ-Algebra V Σ) Var) Eq.≗ id
    lift-var t = Eq.sym ((FreeObject.*-uniq Σ-free Var (record { f = id ; commutes = λ x → Eq.cong (App (x .Data.Product.proj₁)) (Eq.sym (VP.map-id (x .Data.Product.proj₂))) }) λ _ → ≡-refl) t)

  μΣ : (Σ : Signature) → Initial (F-Algebras (Sig-Functor Σ))
  μΣ Σ .Initial.⊥ .F-Algebra.A = Σ * ⊥
  μΣ Σ .Initial.⊥ .F-Algebra.α (op , args) = App op args
  μΣ Σ .Initial.⊥-is-initial .IsInitial.! {A} .F-Algebra-Morphism.f = lift Σ ⊥ A (λ ())
  μΣ Σ .Initial.⊥-is-initial .IsInitial.! {A} .commutes (op , args) = Eq.cong (F-Algebra.α A) (Σ-≡,≡→≡ (≡-refl , lift-vec-map Σ ⊥ A (λ ()) (arts Σ !! op) args))
  μΣ Σ .Initial.⊥-is-initial .IsInitial.!-unique {A} f = uniq
    where
      uniq : ∀ (x : Σ * ⊥) → lift Σ ⊥ A (λ ()) x ≡ ⟪ f ⟫ x
      uniq-vec : (n : ℕ) → (args : Vec (Σ * ⊥) n) → lift-vec Σ ⊥ A (λ ()) n args ≡ V.map ⟪ f ⟫ args
      uniq-vec zero [] = ≡-refl
      uniq-vec (suc n) (arg ∷ args) = ≋⇒≡ (uniq arg ∷ ≡⇒≋ (uniq-vec n args))
      uniq (App op args) = Eq.trans (Eq.cong (F-Algebra.α A) (Σ-≡,≡→≡ (≡-refl , uniq-vec (arts Σ !! op) args))) (Eq.sym (F-Algebra-Morphism.commutes f (op , args)))
