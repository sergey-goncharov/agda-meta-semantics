{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import Data.Nat using (ℕ)
open import Data.Vec as V using (Vec ; lookup ; foldr ; [] ; _∷_ ; updateAt; removeAt)
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

open import Data.Sum
import Data.List as List
open List using ([]; _∷_; List)
open import Data.Unit.Polymorphic using (tt)
-- open import Data.Product

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

  -- open Cartesian Agda-Cartesian
  record Signature : Set where
    field
      -- operations
      ops : ℕ

      -- arities
      arts : Vec ℕ ops 
  open Signature
  -- PROBLEM:
  -- can't convert signatures to lists or work with signatures directly, record definition makes induction too hard.

  -- signatureToList : Signature → List ℕ
  -- signatureToList record { ops = zero ; arts = arts } = []
  -- signatureToList record { ops = suc n ; arts = arts } = (lookup arts (fromℕ n)) ∷ signatureToList (record { ops = n ; arts = removeAt arts (fromℕ n) })

  open ℕ

  product-Functor : ℕ → Endofunctor (Agda o)
  product-Functor zero = record
    { F₀           = λ _ → ⊤
    ; F₁           = λ _ _ → tt
    ; identity     = λ _ → ≡-refl
    ; homomorphism = λ _ → ≡-refl
    ; F-resp-≈     = λ _ _ → ≡-refl
    }
  product-Functor (suc n) = record
    { F₀           = λ X → X × Functor.₀ (product-Functor n) X
    ; F₁           = λ {A} {B} f → f ⁂ Functor.₁ (product-Functor n) f
    ; identity     = λ {X} → ⁂-cong₂ refl (Functor.identity (product-Functor n)) ○ ⟨⟩-unique refl refl
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → begin 
    (g ∘ f) ⁂ Functor.₁ (product-Functor n) (g ∘ f)                               ≈⟨ ⁂-cong₂ refl (Functor.homomorphism (product-Functor n)) ⟩
    (g ∘ f) ⁂ Functor.₁ (product-Functor n) g ∘ Functor.₁ (product-Functor n) f   ≈˘⟨ ⁂∘⁂ {f = g} {g = Functor.₁ (product-Functor n) g} {f′ = f} {g′ = Functor.₁ (product-Functor n) f} ⟩
    (g ⁂ Functor.₁ (product-Functor n) g) ∘ (f ⁂ Functor.₁ (product-Functor n) f) ∎
    ; F-resp-≈     = λ {A} {B} {f} {g} f≈g → ⁂-cong₂ f≈g (Functor.F-resp-≈ (product-Functor n) f≈g)
    }

  Σ-Functor : List ℕ → Endofunctor (Agda o)
  Σ-Functor [] = record
    { F₀           = λ _ → ⊥
    ; F₁           = λ _ ()
    ; identity     = λ ()
    ; homomorphism = λ ()
    ; F-resp-≈     = λ _ ()
    }
  Σ-Functor (n ∷ ns) = record
    { F₀           = λ X → Functor.₀ (product-Functor n) X + Functor.₀ (Σ-Functor ns) X
    ; F₁           = λ {A} {B} f → Functor.₁ (product-Functor n) f +₁ Functor.₁ (Σ-Functor ns) f
    ; identity     = λ {A} → +₁-cong₂ (Functor.identity (product-Functor n)) (Functor.identity (Σ-Functor ns)) ○ []-unique refl refl
    ; homomorphism = λ {X} {Y} {Z} {f} {g} → +₁-cong₂ (Functor.homomorphism (product-Functor n)) (Functor.homomorphism (Σ-Functor ns)) ○ sym +₁∘+₁
    ; F-resp-≈     = λ {A} {B} {f} {g} f≈g → +₁-cong₂ (Functor.F-resp-≈ (product-Functor n) f≈g) (Functor.F-resp-≈ (Σ-Functor ns) f≈g)
    }

  Σₘₒₙ : List ℕ
  Σₘₒₙ = 0 ∷ 2 ∷ []

  data _*_ (Σ : List ℕ) (X : Set o) : Set o where
    Var : X → Σ * X
    App : (n : Fin (List.length Σ)) → Vec (Σ * X) (List.lookup Σ n) → Σ * X

  Mon-Algebra : (V : Set o) → F-Algebra (Σ-Functor Σₘₒₙ)
  Mon-Algebra V = record 
    { A = Σₘₒₙ * V 
    ; α = λ { (inj₁ a) → {!  App 0 a !} ; (inj₂ b) → {!   !} } 
    }

  Σ-Algebra : (V : Set o) → (Σ : List ℕ) → F-Algebra (Σ-Functor Σ)
  Σ-Algebra V [] = record 
    { A = [] * V
    ; α = λ ()
    } 
  Σ-Algebra V Σ@(n ∷ ns) = record 
    { A = Σ * V 
    ; α = λ x → {!   !}
    }
