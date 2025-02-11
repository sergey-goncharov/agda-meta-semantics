{-# OPTIONS --safe --without-K #-}

open import Level renaming (suc to ℓ-suc; zero to ℓ-zero)

-- The category of agda types and terminating functions.
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Category
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Fin.Base hiding (_+_)
open import Categories.Functor.Algebra
open import Data.Empty.Polymorphic
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm)

open import Categories.Category.Construction.F-Algebras
open import Categories.FreeObjects.Free
open import Categories.Object.Initial

open import Axiom.Extensionality.Propositional using (Extensionality)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_) renaming (refl to ≡-refl; trans to ≡-trans)
open Eq.≡-Reasoning

open import Data.Sum
open import Data.Sum.Properties using (inj₁-injective)

open import Data.Vec using (_∷_; [])
open import Data.Vec.Properties using (map-id)

module Example.Combinatory (o : Level) (ext : Extensionality o o) where
  open Category (Agda o)
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
  data [_]_↪k_ : ℕ → xCL * ⊥ → xCL * ⊥ → Set o where
    base↪ : ∀ {t : xCL * ⊥} → [ ℕ.zero ] t ↪k t
    step↪ : ∀ {k : ℕ} {t t' s : xCL * ⊥} → γ t ≡ inj₁ t' → [ k ] t' ↪k s → [ ℕ.suc k ] t ↪k s

  -- k-step reduction function
  [_]_↪k'_ : ℕ → xCL * ⊥ → xCL * ⊥ → Set o
  [ ℕ.zero ] t ↪k' s = t ≡ s
  [ ℕ.suc n ] t ↪k' s = γk (ℕ.suc n) t ≡ inj₁ s

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

  --- Ωk ->* Ωk+1
  preI : ℕ → xCL * ⊥ → xCL * ⊥
  preI ℕ.zero t = t
  preI (ℕ.suc n) t = I ⁎ (preI n t)

  ωk : ℕ → xCL * ⊥
  ωk n = preI n (S ⁎ I ⁎ I)
  Ωk : ℕ → xCL * ⊥
  Ωk n = ωk n ⁎ ωk n

  -- TODO implement derivation rules
  -- TODO for next week: define record for HO-spec

  It : ∀ (t : xCL * ⊥) → I ⁎ t ↪ t
  It t = begin 
    γ (I ⁎ t) 
      ≡⟨ ♣-comm (Initial.⊥ (μΣ xCL)) (suc (suc (suc (suc (suc (suc zero))))), I ∷ (t ∷ [])) ⟩ 
    inj₁ (sig-lift xCL ⊥ (Initial.⊥ (μΣ xCL)) (λ ()) t) 
      ≡⟨ Eq.cong inj₁ ((IsInitial.!-unique (Initial.⊥-is-initial (μΣ xCL)) (record { f = λ x → x ; commutes = λ (op , args) → Eq.cong (λ z → App op z) (Eq.sym (map-id args)) })) t) ⟩ 
    inj₁ t 
    ∎

  St : ∀ (t : xCL * ⊥) → S ⁎ t ↪ S' t
  St t = begin 
    γ (S ⁎ t) 
      ≡⟨ ♣-comm (Initial.⊥ (μΣ xCL)) (suc (suc (suc (suc (suc (suc zero))))), S ∷ (t ∷ [])) ⟩ 
    inj₁ (sig-lift xCL ⊥ (Initial.⊥ (μΣ xCL)) (λ ()) (S' t)) 
      ≡⟨ Eq.cong (λ x → inj₁ (S' x)) ((IsInitial.!-unique (Initial.⊥-is-initial (μΣ xCL)) (record { f = λ x → x ; commutes = λ (op , args) → Eq.cong (λ z → App op z) (Eq.sym (map-id args)) })) t) ⟩
    inj₁ (S' t) ∎

  -- TODO theorem 3.7
  -- define coproduct as record HO-spec
  -- derive ρ from HO-spec

  preI-kstep : ∀ (k : ℕ) (t : xCL * ⊥) → [ k ] preI k t ↪k t
  preI-kstep ℕ.zero t = base↪
  preI-kstep (ℕ.suc k) t = step↪ (It (preI k t)) (preI-kstep k t)

  preI-kstep2 : ∀ (k : ℕ) (t s : xCL * ⊥) → [ k ] ((preI k t) ⁎ s) ↪k (t ⁎ s)
  preI-kstep2 ℕ.zero t s = base↪
  preI-kstep2 (ℕ.suc k) t s = step↪ (Eq.cong₂
     (λ x y →
        inj₁ (App (suc (suc (suc (suc (suc (suc zero)))))) (x ∷ y ∷ [])))
     (inj₁-injective (It (preI k t))) (inj₁-injective (It s))) (preI-kstep2 k t s) 

  Ωk-kstep : ∀ (k : ℕ) → [ k ] Ωk k ↪k S ⁎ I ⁎ I ⁎ ωk k
  Ωk-kstep k = preI-kstep2 k (S ⁎ I ⁎ I) (ωk k)

  ↪k-trans : ∀ {n m : ℕ} {p q r : xCL * ⊥} → [ n ] p ↪k q → [ m ] q ↪k r → [ n + m ] p ↪k r
  ↪k-trans .{ℕ.zero} {m} {p} .{p} {r} base↪ qr = qr
  ↪k-trans .{ℕ.suc _} .{ℕ.zero} {p} {q} .{q} (step↪ {k} {p} {p'} pp' pq) base↪ rewrite +-identityʳ k = step↪ pp' pq
  ↪k-trans .{ℕ.suc _} .{ℕ.suc _} {p} {q} {r} (step↪ {k} {p} {p'} pp' pq) (step↪ {t} {q} {q'} qq' qr) = step↪ pp' (↪k-trans pq (step↪ qq' qr))

  ↪k-trans' : ∀ {n m : ℕ} {p q r : xCL * ⊥} → [ n ] p ↪k q → [ m ] q ↪k r → [ m + n ] p ↪k r
  ↪k-trans' {n} {m} pq qr rewrite +-comm m n = ↪k-trans pq qr

  -- Ωk ->* Ωk+1
  Ωk-Ωk+1 : ∀ (k : ℕ) → [ ℕ.suc (ℕ.suc (ℕ.suc k)) ] Ωk k ↪k Ωk (ℕ.suc k)
  Ωk-Ωk+1 k = ↪k-trans' {n = k} {m = 3} (Ωk-kstep k) (step↪ step₁ (step↪ step₂ (step↪ step₃ base↪)))
    where
      step₁ : S ⁎ I ⁎ I ⁎ ωk k ↪ S' I ⁎ I ⁎ ωk k
      step₂ : S' I ⁎ I ⁎ ωk k ↪ S'' I I ⁎ ωk k
      step₃ : S'' I I ⁎ ωk k ↪ Ωk (ℕ.suc k)
      step₁ = Eq.cong (λ x → inj₁ (S' I ⁎ I ⁎ x)) (inj₁-injective (It (ωk k))) 
      step₂ = Eq.cong (λ x → inj₁ (S'' I I ⁎ x)) (inj₁-injective (It (ωk k)))
      step₃ = Eq.cong₂ (λ x y → inj₁ ((I ⁎ x) ⁎ (I ⁎ y))) (inj₁-injective (It (ωk k))) (inj₁-injective (It (ωk k)))
  ---
