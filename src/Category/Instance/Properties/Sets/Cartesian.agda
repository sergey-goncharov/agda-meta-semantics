{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Instance.Sets
open import Level

open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts

open import Data.Unit.Polymorphic
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Product
open import Data.Product.Properties
open import Function.Base

module Category.Instance.Properties.Sets.Cartesian (o : Level) where
  Sets-Cartesian : Cartesian (Sets o)
  Sets-Cartesian = record 
    { terminal = record { ⊤ = ⊤ ; ⊤-is-terminal = record { ! = λ _ → tt ; !-unique = λ _ _ → refl } } 
    ; products = record { product = λ {A} {B} → record
      { A×B = A × B
      ; π₁ = proj₁
      ; π₂ = proj₂
      ; ⟨_,_⟩ = <_,_>
      ; project₁ = λ _ → refl
      ; project₂ = λ _ → refl
      ; unique = λ {C} {f} {p₁} {p₂} eq₁ eq₂ → λ x → begin 
        < p₁ , p₂ > x                 ≡⟨ ×-≡,≡→≡ (sym (eq₁ x) , sym (eq₂ x)) ⟩ 
        < proj₁ ∘′ f , proj₂ ∘′ f > x ≡⟨⟩
        f x                           ∎
      } } 
    }