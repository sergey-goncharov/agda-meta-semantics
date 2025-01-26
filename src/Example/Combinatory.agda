{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import Level renaming (suc to ℓ-suc; zero to ℓ-zero)

-- The category of agda types and terminating functions.
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Category
open import Data.Product using (_,_)
open import Data.Fin.Base
open import Categories.Functor.Algebra
open import Data.Empty.Polymorphic
open import Data.Nat.Base using (ℕ)


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

  -- t , s ∷= S | K | I | S'(t) | K'(t) | S''(t,s) | app(t,s)
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
  module _ where
    private
      -- helpers
      S : Fin 7
      K : Fin 7
      I : Fin 7
      S' : Fin 7
      K' : Fin 7
      S'' : Fin 7
      app : Fin 7
      S = zero
      K = suc zero
      I = suc (suc zero)
      S' = suc (suc (suc zero))
      K' = suc (suc (suc (suc zero)))
      S'' = suc (suc (suc (suc (suc zero))))
      app = suc (suc (suc (suc (suc (suc zero)))))

    law : Law
    law .Law.ρ X Y (zero , [])                                                             = inj₂ (λ x → App S' (Var (inj₁ x) ∷ []))
    law .Law.ρ X Y (suc zero , [])                                                         = inj₂ (λ x → App K' (Var (inj₁ x) ∷ []))
    law .Law.ρ X Y (suc (suc zero) , [])                                                   = inj₂ (λ x → Var (inj₁ x))
    law .Law.ρ X Y (suc (suc (suc zero)) , (x , _) ∷ [])                                   = inj₂ (λ x' → App S'' (Var (inj₁ x) ∷ Var (inj₁ x') ∷ []))
    law .Law.ρ X Y (suc (suc (suc (suc zero))) , (x , _) ∷ [])                             = inj₂ (λ _ → Var (inj₁ x))
    law .Law.ρ X Y (suc (suc (suc (suc (suc zero)))) , (x , _) ∷ (x' , _) ∷ [])            = inj₂ (λ x'' → App app (App app (Var (inj₁ x) ∷ Var (inj₁ x'') ∷ []) ∷ App app (Var (inj₁ x') ∷ Var (inj₁ x'') ∷ []) ∷ []))
    law .Law.ρ X Y (suc (suc (suc (suc (suc (suc zero))))) , (_ , inj₁ y) ∷ (x' , _) ∷ []) = inj₁ (App app (Var (inj₂ y) ∷ Var (inj₁ x') ∷ []))
    law .Law.ρ X Y (suc (suc (suc (suc (suc (suc zero))))) , (_ , inj₂ f) ∷ (x' , _) ∷ []) = inj₁ (Var (inj₂ (f x')))

    law .Law.natural f (zero , [])                                                             = ≡-refl
    law .Law.natural f (suc zero , [])                                                         = ≡-refl
    law .Law.natural f (suc (suc zero) , [])                                                   = ≡-refl
    law .Law.natural f (suc (suc (suc zero)) , (x , _) ∷ [])                                   = ≡-refl
    law .Law.natural f (suc (suc (suc (suc zero))) , (x , _) ∷ [])                             = ≡-refl
    law .Law.natural f (suc (suc (suc (suc (suc zero)))) , (x , _) ∷ (x' , _) ∷ [])            = ≡-refl
    law .Law.natural f (suc (suc (suc (suc (suc (suc zero))))) , (_ , inj₁ y) ∷ (x' , _) ∷ []) = ≡-refl
    law .Law.natural f (suc (suc (suc (suc (suc (suc zero))))) , (_ , inj₂ g) ∷ (x' , _) ∷ []) = ≡-refl

    law .Law.dinatural f (zero , [])                                                             = ≡-refl
    law .Law.dinatural f (suc zero , [])                                                         = ≡-refl
    law .Law.dinatural f (suc (suc zero) , [])                                                   = ≡-refl
    law .Law.dinatural f (suc (suc (suc zero)) , (x , _) ∷ [])                                   = ≡-refl
    law .Law.dinatural f (suc (suc (suc (suc zero))) , (x , _) ∷ [])                             = ≡-refl
    law .Law.dinatural f (suc (suc (suc (suc (suc zero)))) , (x , _) ∷ (x' , _) ∷ [])            = ≡-refl
    law .Law.dinatural f (suc (suc (suc (suc (suc (suc zero))))) , (_ , inj₁ y) ∷ (x' , _) ∷ []) = ≡-refl
    law .Law.dinatural f (suc (suc (suc (suc (suc (suc zero))))) , (_ , inj₂ g) ∷ (x' , _) ∷ []) = ≡-refl

  open Clubsuit law (μΣ xCL)

  μΣ₀ : Set o
  μΣ₀ = F-Algebra.A (Initial.⊥ (μΣ xCL))

  γ : μΣ₀ → B.₀ (μΣ₀ , μΣ₀)
  γ = (Initial.⊥ (μΣ xCL)) ♣

  -- NOTE: This is not at all terminating, use at own risk
  {-# TERMINATING #-}
  γ* : μΣ₀ → B.₀ (μΣ₀ , μΣ₀)
  γ* t with γ t 
  ...     | inj₁ t' = γ* t'
  ...     | inj₂ f = inj₂ f

  -- Eval with gas
  γk : ℕ → μΣ₀ → B.₀ (μΣ₀ , μΣ₀)
  γk ℕ.zero t = inj₁ t
  γk (ℕ.suc n) t with γ t
  ...               | inj₁ t' = γk n t'
  ...               | inj₂ f = inj₂ f


  -- helpers
  S : xCL * ⊥
  S = App zero []
  K : xCL * ⊥
  K = App (suc zero) []
  I : xCL * ⊥
  I = App (suc (suc zero)) []
  -- S' : xCL * ⊥
  -- S' = App zero []
  -- K' : xCL * ⊥
  -- K' = App zero []
  -- S'' : xCL * ⊥
  -- S'' = App zero []

  infixl 10 _⁎_
  _⁎_ : xCL * ⊥ → xCL * ⊥ → xCL * ⊥
  t ⁎ s = App (suc (suc (suc (suc (suc (suc zero)))))) (t ∷ s ∷ [])

  ----- I I -> I
  double-I : γ (I ⁎ I) ≡ inj₁ I
  double-I = ≡-refl
  -----

  ----- KIS ->* I
  kis-I : γ* ((K ⁎ I) ⁎ S) ≡ γ I
  kis-I = ≡-refl

  ----- ((SK)I)((KI)S) ->* I
  skikis-I : γ* (((S ⁎ K) ⁎ I) ⁎ ((K ⁎ I) ⁎ S)) ≡ γ I
  skikis-I = ≡-refl
  -----

  ωk : ℕ → xCL * ⊥
  ωk ℕ.zero = S ⁎ I ⁎ I
  ωk (ℕ.suc n) = I ⁎ (ωk n)
  Ωk : ℕ → xCL * ⊥
  Ωk n = ωk n ⁎ ωk n

  -- Ω₀ ->* Ω₁
  Ω₀-Ω₁ : γk 3 (Ωk 0) ≡ inj₁ (Ωk 1)
  Ω₀-Ω₁ = ≡-refl

  -- Ω₁ ->* Ω₂
  Ω₁-Ω₂ : γk 4 (Ωk 1) ≡ inj₁ (Ωk 2)
  Ω₁-Ω₂ = ≡-refl

  -- Ω₂ ->* Ω₃
  Ω₂-Ω₃ : γk 5 (Ωk 2) ≡ inj₁ (Ωk 3)
  Ω₂-Ω₃ = ≡-refl

  -- Ωk ->* Ωk+1
  Ωk-Ωk+1 : ∀ (k : ℕ) → γk (ℕ.suc (ℕ.suc (ℕ.suc k))) (Ωk k) ≡ inj₁ (Ωk (ℕ.suc k))
  Ωk-Ωk+1 k = {! ≡-refl  !}
  -- Ωk-Ωk+1 ℕ.zero = Ω₀-Ω₁
  -- Ωk-Ωk+1 (ℕ.suc k) = {! Ωk-Ωk+1 k  !}
  -- Ωk-Ωk+1 (ℕ.suc k) rewrite Ωk-Ωk+1 k = {! ≡-refl  !}
