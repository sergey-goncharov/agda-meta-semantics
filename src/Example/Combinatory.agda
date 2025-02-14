{-# OPTIONS --without-K #-}

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

  -- transitivity
  ↪k-trans : ∀ {n m : ℕ} {p q r : xCL * ⊥} → [ n ] p ↪k q → [ m ] q ↪k r → [ n + m ] p ↪k r
  ↪k-trans .{ℕ.zero} {m} {p} .{p} {r} base↪ qr = qr
  ↪k-trans .{ℕ.suc _} .{ℕ.zero} {p} {q} .{q} (step↪ {k} {p} {p'} pp' pq) base↪ rewrite +-identityʳ k = step↪ pp' pq
  ↪k-trans .{ℕ.suc _} .{ℕ.suc _} {p} {q} {r} (step↪ {k} {p} {p'} pp' pq) (step↪ {t} {q} {q'} qq' qr) = step↪ pp' (↪k-trans pq (step↪ qq' qr))

  ↪k-trans' : ∀ {n m : ℕ} {p q r : xCL * ⊥} → [ n ] p ↪k q → [ m ] q ↪k r → [ m + n ] p ↪k r
  ↪k-trans' {n} {m} pq qr rewrite +-comm m n = ↪k-trans pq qr
  
  -- derivation rules
  I-rule : ∀ (t : xCL * ⊥) → I ⁎ t ↪ t
  I-rule t = γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , I ∷ t ∷ [])

  S-rule : ∀ (t : xCL * ⊥) → S ⁎ t ↪ S' t
  S-rule t = γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , S ∷ t ∷ [])

  K-rule : ∀ (t : xCL * ⊥) → K ⁎ t ↪ K' t
  K-rule t = γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , K ∷ t ∷ [])

  S'-rule : ∀ (p t : xCL * ⊥) → S' p ⁎ t ↪ S'' p t
  S'-rule p t = begin 
    γ (S' p ⁎ t) 
      ≡⟨ γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , S' p ∷ t ∷ []) ⟩ 
    inj₁ (S'' (proj₁ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) p)) t) 
      ≡⟨ Eq.cong (λ x → inj₁ (S'' x t)) (inj₁-injective (I-rule p)) ⟩
    inj₁ (S'' p t) ∎

  K'-rule : ∀ (p t : xCL * ⊥) → K' p ⁎ t ↪ p
  K'-rule p t = begin 
    γ (K' p ⁎ t) 
      ≡⟨ γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , K' p ∷ t ∷ []) ⟩ 
    inj₁ (proj₁ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) p)) 
      ≡⟨ I-rule p ⟩ 
    inj₁ p ∎

  S''-rule : ∀ (p q t : xCL * ⊥) → S'' p q ⁎ t ↪ (p ⁎ t) ⁎ (q ⁎ t)
  S''-rule p q t = begin 
    γ (S'' p q ⁎ t) 
      ≡⟨ γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , S'' p q ∷ t ∷ []) ⟩ 
    inj₁ (proj₁ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) p) ⁎ t ⁎ (proj₁ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) q) ⁎ t)) 
      ≡⟨ Eq.cong₂ (λ x y → inj₁ (x ⁎ t ⁎ (y ⁎ t))) (inj₁-injective (I-rule p)) (inj₁-injective (I-rule q)) ⟩ 
    inj₁ ((p ⁎ t) ⁎ (q ⁎ t)) ∎

  app-rule : ∀ (p p' q : xCL * ⊥) → p ↪ p' → p ⁎ q ↪ p' ⁎ q
  app-rule p p' q pq = begin 
    γ (p ⁎ q) 
      ≡⟨ γ-rec ((suc (suc (suc (suc (suc (suc zero)))))) , p ∷ q ∷ []) ⟩ 
    B.F₁ ((λ x → x) , sig-lift xCL (xCL * ⊥) (Initial.⊥ (μΣ xCL)) (λ x → x)) (B.F₁ ((λ x → x) , (sig-lift xCL ((xCL * ⊥) ⊎ (xCL * ⊥)) (Σ-Algebra (xCL * ⊥) xCL) (λ x → Var ([ (λ x₁ → x₁) , (λ x₁ → x₁) ] x)))) (Law.ρ law (xCL * ⊥) (xCL * ⊥) ((suc (suc (suc (suc (suc (suc zero)))))) , ((p , proj₂ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) p)) ∷ ((q , proj₂ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) q)) ∷ []))))) 
      ≡⟨ Eq.cong (λ z → B.F₁ ((λ x → x) , sig-lift xCL (xCL * ⊥) (Initial.⊥ (μΣ xCL)) (λ x → x)) (B.F₁ ((λ x → x) , (sig-lift xCL ((xCL * ⊥) ⊎ (xCL * ⊥)) (Σ-Algebra (xCL * ⊥) xCL) (λ x → Var ([ (λ x₁ → x₁) , (λ x₁ → x₁) ] x)))) (Law.ρ law (xCL * ⊥) (xCL * ⊥) ((suc (suc (suc (suc (suc (suc zero)))))) , ((p , z) ∷ ((q , proj₂ (sig-lift xCL ⊥ (club'-alg (Initial.⊥ (μΣ xCL))) (λ ()) q)) ∷ [])))))) pq ⟩ 
    inj₁ (p' ⁎ q) ∎

  ----- I I -> I
  double-I : I ⁎ I ↪ I
  double-I = I-rule I
  -----

  ----- KIS -2-> I
  kis-I : [ 2 ] K ⁎ I ⁎ S ↪k I
  kis-I = step↪ (app-rule (K ⁎ I) (K' I) S (K-rule I)) 
          (step↪ (K'-rule I S) 
          base↪)
  -----

  ----- ((SK)I)((KI)S) -7-> I
  skikis-I : [ 7 ] S ⁎ K ⁎ I ⁎ (K ⁎ I ⁎ S) ↪k I
  skikis-I = step↪ (app-rule (S ⁎ K ⁎ I) (S' K ⁎ I) (K ⁎ I ⁎ S) (app-rule (S ⁎ K) (S' K) I (S-rule K))) 
            (step↪ (app-rule (S' K ⁎ I) (S'' K I) (K ⁎ I ⁎ S) (S'-rule K I)) 
            (step↪ (S''-rule K I (K ⁎ I ⁎ S)) 
            (step↪ (app-rule (K ⁎ (K ⁎ I ⁎ S)) (K' (K ⁎ I ⁎ S)) (I ⁎ (K ⁎ I ⁎ S)) (K-rule (K ⁎ I ⁎ S))) 
            (step↪ (K'-rule (K ⁎ I ⁎ S) (I ⁎ (K ⁎ I ⁎ S))) 
            kis-I))))
  -----

  --- EXAMPLE 3.2
  ----- SKI -> S'(K)I
  skis'ki : ((S ⁎ K) ⁎ I) ↪ (S' K ⁎ I) 
  skis'ki = app-rule (S ⁎ K) (S' K) I (S-rule K)
  -----

  ----- S'(K)I -> S''(K,I)
  s'kis''ki : (S' (K) ⁎ I) ↪ S'' (K) (I)
  s'kis''ki = S'-rule K I
  -----

  ----- SKK -> S'(K)K
  skks'kk : ((S ⁎ K) ⁎ K) ↪ (S' K ⁎ K)
  skks'kk = app-rule (S ⁎ K) (S' K) K (S-rule K)
  -----

  ----- S'(K)K -> S''(K,K)
  s'kks''kk : (S' (K) ⁎ K) ↪ S'' (K) (K)
  s'kks''kk = S'-rule K K
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

  -- TODO for next week: define record for HO-spec

  -- TODO theorem 3.7
  -- define coproduct as record HO-spec
  -- derive ρ from HO-spec

  preI-kstep : ∀ (k : ℕ) (t : xCL * ⊥) → [ k ] preI k t ↪k t
  preI-kstep ℕ.zero t = base↪
  preI-kstep (ℕ.suc k) t = step↪ (I-rule (preI k t)) (preI-kstep k t)

  preI-kstep2 : ∀ (k : ℕ) (t s : xCL * ⊥) → [ k ] ((preI k t) ⁎ s) ↪k (t ⁎ s)
  preI-kstep2 ℕ.zero t s = base↪
  preI-kstep2 (ℕ.suc k) t s = step↪ (Eq.cong₂
     (λ x y →
        inj₁ (App (suc (suc (suc (suc (suc (suc zero)))))) (x ∷ y ∷ [])))
     (inj₁-injective (I-rule (preI k t))) (inj₁-injective (I-rule s))) (preI-kstep2 k t s) 

  Ωk-kstep : ∀ (k : ℕ) → [ k ] Ωk k ↪k S ⁎ I ⁎ I ⁎ ωk k
  Ωk-kstep k = preI-kstep2 k (S ⁎ I ⁎ I) (ωk k)

  -- Ωk -k+3-> Ωk+1
  -- more explicitly the proof goes as follows:
  -- Ωk ->ᵏ S ⁎ I ⁎ I ⁎ ωk -> S' I ⁎ I ⁎ ωk -> S'' I I ⁎ ωk k -> Ωk+1
  Ωk-Ωk+1 : ∀ (k : ℕ) → [ ℕ.suc (ℕ.suc (ℕ.suc k)) ] Ωk k ↪k Ωk (ℕ.suc k)
  Ωk-Ωk+1 k = ↪k-trans' {n = k} {m = 3} (Ωk-kstep k) (step↪ step₁ (step↪ step₂ (step↪ step₃ base↪)))
    where
      step₁ : S ⁎ I ⁎ I ⁎ ωk k ↪ S' I ⁎ I ⁎ ωk k
      step₂ : S' I ⁎ I ⁎ ωk k ↪ S'' I I ⁎ ωk k
      step₃ : S'' I I ⁎ ωk k ↪ Ωk (ℕ.suc k)
      step₁ = Eq.cong (λ x → inj₁ (S' I ⁎ I ⁎ x)) (inj₁-injective (I-rule (ωk k))) 
      step₂ = Eq.cong (λ x → inj₁ (S'' I I ⁎ x)) (inj₁-injective (I-rule (ωk k)))
      step₃ = Eq.cong₂ (λ x y → inj₁ ((I ⁎ x) ⁎ (I ⁎ y))) (inj₁-injective (I-rule (ωk k))) (inj₁-injective (I-rule (ωk k)))
  ---
