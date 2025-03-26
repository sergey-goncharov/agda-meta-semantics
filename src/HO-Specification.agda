{-# OPTIONS --without-K --allow-unsolved-metas #-}
-- Theorem 3.7

open import Level hiding (Lift)
open import Function.Base
open import Data.Fin.Base
open import Data.Fin.Subset using (Subset; Side; inside; outside; _∈_)
open import Data.Vec as V using (Vec ; foldr ; [] ; _∷_ ; updateAt; removeAt) renaming (lookup to _!!_)
open import Data.Vec.Properties using (lookup-map; map-∘)
open import Data.Vec.Membership.Propositional hiding (_∈_)
open import Data.Product using (_,_; _×_; Σ-syntax) renaming (Σ to Sigma)
open import Data.Product.Base using (proj₁; proj₂) renaming (_×_ to _×⁰_)
open import Data.Sum renaming (_⊎_ to _+⁰_; map to _+¹_)
open import Data.Unit.Polymorphic using (tt; ⊤)
open import Data.Nat.Base using (ℕ) renaming (zero to ℕ-zero; suc to ℕ-suc)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import Categories.Category.Core
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.FreeObjects.Free

open import Function.Base using (_$_; id)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; subst) renaming (refl to ≡-refl; sym to ≡-sym; trans to ≡-trans)
open Eq.≡-Reasoning

module HO-Specification (o : Level) (ext : Extensionality o o) where
  open import Example.Signature o
  open Category using () renaming (op to _op) hiding (id)

  module _ (Σ : Signature) where
    -- reducing rules
    data HO-reducing {ℓ} (i : Fin (ops Σ)) (W : Subset (arts Σ !! i)) : Set ℓ where
      var-orig : Fin (arts Σ !! i) → HO-reducing i W
      var-next : Sigma _ (λ x → W !! x ≡ inside) → HO-reducing i W
      var-app  : Fin (arts Σ !! i) → Sigma _ (λ x → W !! x ≡ outside) → HO-reducing i W

    -- evaluating rules
    data HO-evaluating {ℓ} (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set ℓ where
      var-n-orig : Fin (arts Σ !! f) → HO-evaluating f W
      var-arg    : HO-evaluating f W
      var-n-next : Sigma _ (λ x → W !! x ≡ inside) → HO-evaluating f W
      var-n-app  : (Fin (arts Σ !! f) +⁰ ⊤ {ℓ = ℓ}) → Sigma _ (λ x → W !! x ≡ outside) → HO-evaluating f W

    data HO-specification-entry (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set o where
      progressing-rule     : Σ * (HO-reducing f W) → HO-specification-entry f W
      non-progressing-rule : Σ * (HO-evaluating f W) → HO-specification-entry f W

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
    B .Functor.F-resp-≈ {A , B} {C , D} {f₁ , f₂} {g₁ , g₂} (f₁≈g₁ , f₂≈g₂) (inj₂ h) = Eq.cong inj₂ (ext helper)
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

    makeW-helper : ∀ {X} {Y} {Y'} (g : Y → Y') (n : ℕ) (args : Vec (Sigma X (λ _ → Y +⁰ (X → Y))) n) → V.map makeW (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) ≡ V.map makeW args
    makeW-helper g ℕ-zero [] = ≡-refl
    makeW-helper g (ℕ-suc n) ((_ , inj₁ x₁) ∷ args) = Eq.cong (inside ∷_) (makeW-helper g n args)
    makeW-helper g (ℕ-suc n) ((_ , inj₂ y) ∷ args) = Eq.cong (outside ∷_) (makeW-helper g n args) 

    prule→target : ∀ {X} {Y} (f : Fin (ops Σ)) (args : Vec (Sigma X (λ _ → Y +⁰ (X → Y))) (arts Σ !! f)) → (W : Vec Side (V.length args)) → (W ≡ V.map makeW args)
      → HO-reducing {ℓ = o} f W → X +⁰ Y

    -- Original variables
    prule→target f args .(V.map makeW args) ≡-refl (var-orig i) = inj₁ (proj₁ (args !! i))

    -- New variables via unlabelled transitions
    prule→target f args .(V.map makeW args) ≡-refl (var-next (i , i∈W)) with args !! i | V.map makeW args !! i | i∈W | lookup-map i makeW args
    ... | _ , inj₁ y | _ | _ | _ = inj₂ y
    ... | _ , inj₂ _ | _ | () | ≡-refl 

    -- New variables via labelled transitions
    prule→target f args .(V.map makeW args) ≡-refl (var-app v (i , i∈W)) with args !! i | V.map makeW args !! i | i∈W | lookup-map i makeW args | args !! v
    ... | _ , inj₁ _ | _ | ≡-refl | () | _
    ... | _ , inj₂ g | _ | _ | _ | y , _ = inj₂ (g y)


    prule→target-cong : ∀ {X} {Y} {Y'} (g : Y → Y') (f : Fin (ops Σ))
      → (args  : Vec (X × B.F₀ (X , Y))  (arts Σ !! f))
      → (args' : Vec (X × B.F₀ (X , Y')) (arts Σ !! f))
      → args' ≡ V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args
      → (W : Vec Side (V.length args))
      → (eq  : W ≡ V.map makeW args)
      → (eq' : W ≡ V.map makeW args')
      → (rule : HO-reducing f W)
      → (id +¹ g) (prule→target f args W eq rule) ≡ prule→target f args' W eq' rule 

    prule→target-cong g f args args' ≡-refl W eq eq' (var-orig i) = ≡-trans (prule→target-cong-vo₁ eq) (prule→target-cong-vo₂ eq')
      where
        prule→target-cong-vo₁ : (eq : W ≡ V.map makeW args) → (id +¹ g) (prule→target f args W eq (var-orig i)) ≡ inj₁ (proj₁ (args !! i))
        prule→target-cong-vo₁ ≡-refl = ≡-refl

        prule→target-cong-vo₂ : (eq : W ≡ V.map makeW args') → inj₁ (proj₁ (args !! i)) ≡ prule→target f args' W eq (var-orig i)  
        prule→target-cong-vo₂ ≡-refl rewrite lookup-map i (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args = ≡-refl

    prule→target-cong g f args .(V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) ≡-refl W eq eq' (var-next (i , i∈W)) = {!!}
    
      where
        prule→target-cong-vn₁ : (eq : W ≡ V.map makeW args) → (id +¹ g) (prule→target f args W eq (var-next (i , i∈W))) ≡ {!!}
        prule→target-cong-vn₁ ≡-refl = {!!} -- with args !! i
        -- ... | _ , inj₁ _ = {!!}

        prule→target-cong-vn₂ : (eq : W ≡ V.map makeW (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args)) → {!!} ≡ prule→target f (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) W eq (var-next (i , i∈W)) 
        prule→target-cong-vn₂ ≡-refl = {!!}

    prule→target-cong g f args args' ≡-refl .(V.map makeW args) ≡-refl eq' (var-app x x₁) = {!  !}

    -- W unlabeled
    Spec⇒ρ : HO-specification → Law
    Spec⇒ρ spec .ρ X Y (f , args) with rules spec f (V.map makeW args)
    ...  | progressing-rule t = inj₁ (*-map Σ (prule→target f args (V.map makeW args) ≡-refl) t)
        
    ...  | non-progressing-rule t = inj₂ λ x → (*-map Σ (nprule→target x) t)
      where
        nprule→target : X → (HO-evaluating f _) → X +⁰ Y
        nprule→target _ ( (var-n-orig i)) = inj₁ (proj₁ (args !! i))
        nprule→target x ( var-arg) = inj₁ x
        nprule→target _ ( (var-n-next (i , i∈W))) with args !! i | V.map makeW args !! i | i∈W | lookup-map i makeW args
        ... | _ , inj₁ y | _ | _ | _ = inj₂ y
        ... | _ , inj₂ _ | _ | ≡-refl | ()
        nprule→target x ( (var-n-app (inj₁ v) (i , i∈W))) with args !! i | V.map makeW args !! i | i∈W | lookup-map i makeW args | args !! v
        ... | _ , inj₁ _ | _ | ≡-refl | () | _
        ... | _ , inj₂ g | _ | _ | _ | y , _ = inj₂ (g y)
        nprule→target x ( (var-n-app (inj₂ tt) (i , i∈W))) with args !! i | V.map makeW args !! i | i∈W | lookup-map i makeW args
        ... | _ , inj₁ _ | _ | ≡-refl | ()
        ... | _ , inj₂ g | _ | _ | _ = inj₂ (g x)

      -- (V → W) → Σ * V → Σ * W
    -- makeW-helper {X} {Y} {Y'} g (arts Σ !! f) args

--    Spec⇒ρ spec .natural {X} {Y} {Y'} g (f , args) = {!rules!}

    Spec⇒ρ spec .natural {X} {Y} {Y'} g (f , args) with rules spec f (V.map makeW args) in eq₁
                                                      | rules spec f (V.map makeW (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args)) in eq₂
    ... | progressing-rule t | progressing-rule s = Eq.cong inj₁ (begin 
            Lift.lift Σ (X +⁰ Y) (Σ-Algebra (X +⁰ Y') Σ) (λ x → Var ([ inj₁ , (λ x₁ → inj₂ (g x₁)) ] x)) (*-map Σ (prule→target f args (V.map makeW args) ≡-refl) t) 
              ≡⟨ {! !} ⟩ 
            {!   !}
              ≡⟨ {!   !} ⟩ 
            *-map Σ ((id +¹ g) ∘ prule→target f args (V.map makeW args) ≡-refl) t
              ≡⟨ Eq.cong (λ r → *-map Σ r t) (ext (λ r → prule→target-cong g f args (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) ≡-refl (V.map makeW args) ≡-refl (≡-sym (makeW-helper g (V.length args) args)) r)) ⟩ 
            *-map Σ (prule→target f (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) (V.map makeW args) (≡-sym (makeW-helper g (V.length args) args))) t
              ≡⟨ {!   !} ⟩
            *-map Σ (prule→target f (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) (V.map makeW (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args)) ≡-refl)
             s
              ≡⟨ Eq.cong
                  (λ r → *-map Σ (prule→target f ((V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args)) {!r!} ≡-refl) s
                  )
                  {!!} ⟩
            *-map Σ (prule→target f (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args) (V.map makeW (V.map (λ x → proj₁ x , B.F₁ (id , g) (proj₂ x)) args)) ≡-refl) s
            ∎)
      -- where
      -- helper : (v : Level.Lift o (HO-reducing f (V.map makeW (V.map (λ x₁ → proj₁ x₁ , B.F₁ ((λ x₂ → x₂) , g) (proj₂ x₁)) args)))) → _ ≡ _
      -- helper (Level.lift (var-orig x)) = {!   !}
      -- helper (Level.lift (var-next x)) = {!   !}
      -- helper (Level.lift (var-app x x₁)) = {!   !}
    ... | progressing-rule t | non-progressing-rule x = {!   !} -- TODO eq₁ and eq₂ should be contradictory?
    ... | non-progressing-rule t | progressing-rule x = {!   !} -- TODO eq₁ and eq₂ should be contradictory?
    ... | non-progressing-rule t | non-progressing-rule x = {!   !}
    Spec⇒ρ spec .dinatural = {!   !}
