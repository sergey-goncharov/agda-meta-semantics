-- Theorem 3.7

open import Level hiding (Lift)
open import Data.Fin.Base
open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Vec as V using (Vec ; foldr ; [] ; _∷_ ; updateAt; removeAt) renaming (lookup to _!!_)
open import Data.Vec.Properties using (lookup-map)
open import Data.Vec.Membership.Propositional hiding (_∈_)
open import Data.Product using (_,_; _×_; Σ-syntax) renaming (Σ to Sigma)
open import Data.Product.Base using (proj₁; proj₂) renaming (_×_ to _×⁰_)
open import Data.Sum renaming (_⊎_ to _+⁰_)
open import Data.Unit.Polymorphic using (tt; ⊤)

open import Categories.Category.Core
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.FreeObjects.Free

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open Eq.≡-Reasoning

module HO-Specification (o : Level) where
  open import Example.Signature o
  open Category renaming (op to _op)

  module _ (Σ : Signature) where
    -- reducing rules
    data HO-reducing (i : Fin (ops Σ)) (W : Subset (arts Σ !! i)) : Set where
        var-orig : Fin (arts Σ !! i) → HO-reducing i W -- proj₁
        var-next : Sigma _ (λ x → W !! x ≡ inside)    → HO-reducing i W -- proj₂ + next TODO error!! ∈ does not do whats expected!
        var-app  : Fin (arts Σ !! i) → Sigma _ (_∉ W) → HO-reducing i W -- proj₂

    -- evaluating rules
    data HO-evaluating (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set where
      var-n-orig : Fin (arts Σ !! f) → HO-evaluating f W
      var-arg    : HO-evaluating f W
      var-n-next : (Sigma _ λ x → x ∈ W) → HO-evaluating f W
      var-n-app  : (Fin (arts Σ !! f) +⁰ ⊤) ×⁰ Fin (arts Σ !! f) ×⁰ (Sigma _ λ x → x ∉ W) → HO-evaluating f W

    data HO-specification-entry (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set o where
      progressing-rule     : Σ * Level.Lift o (HO-reducing f W) → HO-specification-entry f W
      non-progressing-rule : Σ * Level.Lift o (HO-reducing f W) → HO-specification-entry f W

    record HO-specification : Set o where
      field
        rules : ∀ (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) → HO-specification-entry f W
    
    B : Bifunctor ((Agda o) op) (Agda o) (Agda o)
    B .Functor.F₀ (X , Y) = Y +⁰ (X → Y)
    B .Functor.F₁ {A , B} {C , D} (f , g) (inj₁ x) = inj₁ (g x)
    B .Functor.F₁ {A , B} {C , D} (f , g) (inj₂ h) = inj₂ λ x → g (h (f x))
    B .Functor.identity (inj₁ x) = ≡-refl
    B .Functor.identity (inj₂ y) = ≡-refl
    B .Functor.homomorphism (inj₁ x) = ≡-refl
    B .Functor.homomorphism (inj₂ y) = ≡-refl
    B .Functor.F-resp-≈ {A , B} {C , D} {f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) (inj₁ x) = Eq.cong inj₁ (f₂≈g₂ x)
    B .Functor.F-resp-≈ {A , B} {C , D} {f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) (inj₂ h) = Eq.cong inj₂ {!   !} --(ext helper)
      where
      helper : ∀ (x : C) → f₂ (h (f₁ x)) ≡ g₂ (h (g₁ x))
      helper x rewrite (f₁≈g₁ x) = f₂≈g₂ (h (g₁ x))

    open import HOGSOS (Agda o) (Agda-Cartesian o) (Agda-Cocartesian o) (Sig-Functor Σ) B

    freeAlgebras : ∀ X → FreeObject {C = Agda o} {D = F-Algebras (Sig-Functor Σ)} algebraForgetfulF X
    freeAlgebras X = Lift.Σ-free Σ X

    open Laws freeAlgebras
    open Law
    open HO-specification

    open Lift

    makeW : ∀ {X : Set o}{Y : Set o} → X × (Y +⁰ (X → Y)) → Side
    makeW (_ , inj₁ _) = inside
    makeW (_ , inj₂ _) = outside 

    -- W unlabeled
    Spec⇒ρ : HO-specification → Law
    Spec⇒ρ spec .ρ X Y (f , args) with rules spec f (V.map makeW args)
    ...  | progressing-rule x = inj₁ (*-map Σ helper x)
      where

      helper : Level.Lift o (HO-reducing f _) → X +⁰ Y
      helper (Level.lift (var-orig i)) = inj₁ (proj₁ (args !! i))
      helper (Level.lift (var-next (i , i∈W))) with args !! i | ≡-trans (≡-sym (lookup-map i makeW args)) i∈W
      ... | _ , inj₁ y | _ = inj₂ y

      helper (Level.lift (var-app v subs)) = {!   !}
    ...  | non-progressing-rule x = inj₂ {!   !}
    Spec⇒ρ spec .natural = {!   !}
    Spec⇒ρ spec .dinatural = {!   !}
      -- record 
      -- { ρ = λ X Y x → {!   !} 
      -- ; natural = {!   !} 
      -- ; dinatural = {!   !} 
      -- }
    
