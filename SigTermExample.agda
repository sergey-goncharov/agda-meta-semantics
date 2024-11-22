{-# OPTIONS --without-K --safe #-}

module SigTermExample where

open import Data.Nat using (ℕ)
open import Agda.Builtin.Nat using (_==_)
open import Data.Bool using (true ; false ; not ; _∧_ ; _∨_; if_then_else_) renaming (Bool to 𝔹)
open import Data.Bool.Properties
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.Fin as F public using (Fin ; fromℕ ; toℕ) using (zero ; suc)
open import Data.Vec as V public using (Vec ; lookup ; foldr ; [] ; _∷_ ; updateAt)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; inspect ; trans ; sym ; cong) renaming ([_] to ⟨_⟩)
open import Data.Product.Base using (_×_; Σ-syntax ; ∃; _,_ ; proj₁ ; proj₂ )
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)


-- Signature with finitely many operations of finite arities 
record Signature : Set where
  field
    -- operations
    ops : ℕ

    -- arities
    arts : Vec ℕ ops 

open Signature

-- Example: monoid signature
Σₘₒₙ : Signature

-- Two operations
Signature.ops Σₘₒₙ  = 2

-- One arity is 0, one arity is 2
Signature.arts Σₘₒₙ = 0 ∷ (2 ∷ [])

-- Terms with variables
data _*_ (Σ : Signature) (X : Set) : Set where
  Var : X → Σ * X
  App : (f : Fin(ops Σ)) → Vec (Σ * X) (lookup (arts Σ) f)  → Σ * X

-- Terms without variables = closed terms
μΣ = λ {Σ} → Σ * ⊥

-- Example: terms in the monoid signature
x = Var {Σₘₒₙ} 1
y = Var {Σₘₒₙ} 2
z = Var {Σₘₒₙ} 3

-- Alias for monoid multiplication
_∘_ : {X : Set} → Σₘₒₙ * X → Σₘₒₙ * X → Σₘₒₙ * X 
x ∘ y = App (suc zero) (x ∷ y ∷ [])

_ = (x ∘ y) ∘ z   

-- Substitution
_[_]  : {X Y : Set} {Σ : Signature} → Σ * X → (X → Σ * Y) → Σ * Y
_[_]' : {X Y : Set} {Σ : Signature} {n : ℕ} → Vec (Σ * X) n → (X → Σ * Y) → Vec (Σ * Y) n

[] [ σ ]' = []
(t ∷ ts) [ σ ]' = t [ σ ] ∷ ts [ σ ]'

Var x [ σ ]    = σ x
App f xs [ σ ] = App f (xs [ σ ]')

-- Proceed under the assumption that we have some separation on active and passive, computations and values
module CoolTerms (Σ : Signature) (is-receiving : (f : Fin (ops Σ)) → Maybe (Fin (lookup (arts Σ) f))) (is-vformer : Fin (ops Σ) → 𝔹) where

  is-active : Fin(ops Σ) → 𝔹
  is-active f with (is-receiving f) 
  ... | just _  = true
  ... | nothing = false

  is-passive : Fin(ops Σ) → 𝔹
  is-passive f = not (is-active f)

  is-cformer : Fin(ops Σ) → 𝔹
  is-cformer f = not (is-vformer f)

  is-value : {X : Set} → Σ * X → 𝔹
  is-value (Var _)   = false
  is-value (App f _) = is-vformer f

  -- Is the given term active?
  is-active-term : {X : Set} → Σ * X → 𝔹

  -- This answers if the i-th element in the list is an active term
  -- This is roundabout, but Agda's termination checker dos not accept the direct definition,
  -- which would be this one:
  -- is-active-term (Var x) = true
  -- is-active-term (App f xs) with (is-receiving f)
  -- ... | just i  = is-active-term (lookup xs i)
  -- ... | nothing = false

  is-active-term' : {X : Set} {n : ℕ} → Vec (Σ * X) n → Fin n → 𝔹
  is-active-term' (Var _ ∷ _) zero = true
  is-active-term' (App f xs ∷ _) zero with (is-receiving f)
  ... | just i  = is-active-term' xs i
  ... | nothing = false
  is-active-term' (Var _ ∷ xs) (suc i)   = is-active-term' xs i
  is-active-term' (App _ _ ∷ xs) (suc i) = is-active-term' xs i
  
  is-active-term t = is-active-term' (t  ∷ []) zero 

