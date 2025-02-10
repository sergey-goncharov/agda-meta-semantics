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
open Eq using (_≡_) renaming (refl to ≡-refl; trans to ≡-trans)

open import Data.Sum

open import Data.Vec using (_∷_; [])

module Example.Combinatory (o : Level) (ext : Extensionality o o) where
  open Category (Agda o)
  open HomReasoning
  open Equiv
  open import Example.Signature o renaming (lift to sig-lift)

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

  -- eval (single step reduction as function)
  γ : μΣ₀ → B.₀ (μΣ₀ , μΣ₀)
  γ = (Initial.⊥ (μΣ xCL)) ♣

  -- Eval with fuel
  γk : ℕ → μΣ₀ → B.₀ (μΣ₀ , μΣ₀)
  γk ℕ.zero t = inj₁ t
  γk (ℕ.suc n) t with γ t
  ...               | inj₁ t' = γk n t'
  ...               | inj₂ f  = inj₂ f

  -- Eval with a lot of fuel (should feel like transitive-reflexive closure)
  γ* : μΣ₀ → B.₀ (μΣ₀ , μΣ₀)
  γ* = γk 100000


  -- helpers
  S : xCL * ⊥
  S = App zero []
  K : xCL * ⊥
  K = App (suc zero) []
  I : xCL * ⊥
  I = App (suc (suc zero)) []
  S' : xCL * ⊥ → xCL * ⊥
  S' x = App (suc (suc (suc zero))) (x ∷ [])
  K' : xCL * ⊥ → xCL * ⊥
  K' x = App (suc (suc (suc (suc zero)))) (x ∷ [])
  S'' : xCL * ⊥ → xCL * ⊥ → xCL * ⊥
  S'' x y = App (suc (suc (suc (suc (suc zero))))) (x ∷ y ∷ []) 

  -- application helper
  infixl 10 _⁎_
  _⁎_ : xCL * ⊥ → xCL * ⊥ → xCL * ⊥
  t ⁎ s = App (suc (suc (suc (suc (suc (suc zero)))))) (t ∷ s ∷ [])

  -- single step reduction relation
  infixr 5 _↪_
  _↪_ : xCL * ⊥ → xCL * ⊥ → Set o
  t ↪ s = γ t ≡ inj₁ s

  -- k-step reduction relation
  infixr 5 [_]_↪k_
  [_]_↪k_ : ℕ → xCL * ⊥ → xCL * ⊥ → Set o
  [ n ] t ↪k s = γk (ℕ.suc n) t ≡ γ s
  -- [ ℕ.zero ] t ↪k s = t ≡ s
  -- [ ℕ.suc n ] t ↪k s with γ t 
  -- ...                    | inj₁ t' = [ n ] t' ↪k s
  -- ...                    | inj₂ f = ⊥

  -- multi step reduction relation (only works / makes sense for irreducible terms on the right side)
  infixr 5 _↪*_
  _↪*_ : xCL * ⊥ → xCL * ⊥ → Set o
  t ↪* s = γ* t ≡ γ s

  ----- I I -> I
  double-I : I ⁎ I ↪ I
  double-I = ≡-refl
  -----

  ----- KIS ->* I
  kis-I : K ⁎ I ⁎ S ↪* I
  kis-I = ≡-refl

  ----- ((SK)I)((KI)S) ->* I
  skikis-I : S ⁎ K ⁎ I ⁎ (K ⁎ I ⁎ S) ↪* I
  skikis-I = ≡-refl
  -----

  --- EXAMPLE 3.2
  ----- SKI -> S'(K)I
  skis'ki : ((S ⁎ K) ⁎ I) ↪ (S' K ⁎ I) 
  skis'ki = ≡-refl
  -----

  ----- S'(K)I -> S''(K,I)
  s'kis''ki : (S' (K) ⁎ I) ↪ S'' (K) (I)
  s'kis''ki = ≡-refl
  -----

  ----- SKK -> S'(K)K
  skks'kk : ((S ⁎ K) ⁎ K) ↪ (S' K ⁎ K)
  skks'kk = ≡-refl 
  -----

  ----- S'(K)K -> S''(K,K)
  s'kks''kk : (S' (K) ⁎ K) ↪ S'' (K) (K)
  s'kks''kk = ≡-refl
  -----
  ---

  -- TODO this is the wrong bracketing of t
  _**_ : xCL * ⊥ → ℕ → xCL * ⊥
  t ** ℕ.zero = t
  t ** (ℕ.suc n) = t ⁎ (t ** n)

  ωk : ℕ → xCL * ⊥
  ωk ℕ.zero = S ⁎ I ⁎ I
  ωk (ℕ.suc n) = I ⁎ (ωk n)
  Ωk : ℕ → xCL * ⊥
  Ωk n = ωk n ⁎ ωk n

  Ω₀- : Ωk 0 ↪ S' (I) ⁎ I ⁎ (S ⁎ I ⁎ I)
  Ω₀- = ≡-refl

  Ω₀-- : S' (I) ⁎ I ⁎ (S ⁎ I ⁎ I) ↪ S'' I I ⁎ (S ⁎ I ⁎ I)
  Ω₀-- = ≡-refl

  Ω₀--- : S'' I I ⁎ (S ⁎ I ⁎ I) ↪ Ωk 1
  Ω₀--- = ≡-refl

  -- Ω₀ ->* Ω₁
  Ω₀-Ω₁ : [ 3 ] Ωk 0 ↪k Ωk 1
  Ω₀-Ω₁ = ≡-refl

  Ω₁- : Ωk 1 ↪ S ⁎ I ⁎ I ⁎ (I ⁎ (S ⁎ I ⁎ I))
  Ω₁- = ≡-refl

  Ω₁-- : S ⁎ I ⁎ I ⁎ (I ⁎ (S ⁎ I ⁎ I)) ↪ S' (I) ⁎ I ⁎ (I ⁎ (S ⁎ I ⁎ I))
  Ω₁-- = ≡-refl

  Ω₁--- : S' (I) ⁎ I ⁎ (I ⁎ (S ⁎ I ⁎ I)) ↪ S'' (I) (I) ⁎ (I ⁎ (S ⁎ I ⁎ I))
  Ω₁--- = ≡-refl

  Ω₁---- : S'' (I) (I) ⁎ (I ⁎ (S ⁎ I ⁎ I)) ↪ Ωk 2
  Ω₁---- = ≡-refl

  -- Ω₁ ->* Ω₂
  Ω₁-Ω₂ : [ 4 ] Ωk 1 ↪k Ωk 2
  Ω₁-Ω₂ = ≡-refl

  -- Ω₂ ->* Ω₃
  Ω₂-Ω₃ : [ 5 ] Ωk 2 ↪k Ωk 3
  Ω₂-Ω₃ = ≡-refl

  preI : ℕ → xCL * ⊥ → xCL * ⊥
  preI ℕ.zero t = t
  preI (ℕ.suc n) t = I ⁎ (preI n t)

  It : ∀ (t : xCL * ⊥) → γ (I ⁎ t) ≡ inj₁ t
  It t = ≡-trans {!w!} {!!}
    where
      w : γ (I ⁎ t) ≡ inj₁ (sig-lift xCL Data.Empty.Polymorphic.⊥ (Initial.⊥ (μΣ xCL)) (λ ()) t) 
      w = ♣-comm (Initial.⊥ (μΣ xCL)) (suc (suc (suc (suc (suc (suc zero))))), I ∷ (t ∷ [])) 
    
  
  -- It (App zero []) = ≡-refl
  -- It (App (suc zero) []) = ≡-refl
  -- It (App (suc (suc zero)) []) = ≡-refl
  -- TODO this needs w-comm
  -- It (App (suc (suc (suc zero))) (x ∷ [])) = {!!} -- Eq.cong inj₁ (Eq.sym (w-comm (Initial.⊥ (μΣ xCL)) (suc (suc (suc zero)) , {!   !} ∷ [])))
  -- It (App (suc f) x) = {!   !}

  preI-kstep : ∀ (k : ℕ) (t : xCL * ⊥) → [ k ] preI k t ↪k t
  preI-kstep ℕ.zero t = {!   !} -- ≡-refl
  -- TODO does this also just need w-comm?
  preI-kstep (ℕ.suc k) t = {! preI-kstep k t  !}

  Ωk-kstep : ∀ (k : ℕ) → [ k ] Ωk k ↪k S ⁎ I ⁎ I ⁎ ωk k
  Ωk-kstep ℕ.zero = ≡-refl
  -- TODO and this?
  Ωk-kstep (ℕ.suc k) = {!  Ωk-kstep k !} -- [ suc k ] Ωk (suc k) ↪k S ⁎ I ⁎ I ⁎ ωk (suc k)

  -- Ωk ->* Ωk+1
  Ωk-Ωk+1 : ∀ (k : ℕ) → [ ℕ.suc (ℕ.suc (ℕ.suc k)) ] Ωk k ↪k Ωk (ℕ.suc k)
  Ωk-Ωk+1 ℕ.zero = ≡-refl
  -- TODO and this?
  Ωk-Ωk+1 (ℕ.suc k) rewrite (Ωk-kstep (ℕ.suc (ℕ.suc (ℕ.suc (ℕ.suc k))))) = {!   !}
  -- Ωk-Ωk+1 ℕ.zero = Ω₀-Ω₁
  -- Ωk-Ωk+1 (ℕ.suc k) = {! Ωk-Ωk+1 k  !}
  -- Ωk-Ωk+1 (ℕ.suc k) rewrite Ωk-Ωk+1 k = {! ≡-refl  !}
