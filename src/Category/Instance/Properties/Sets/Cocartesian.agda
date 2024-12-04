{-# OPTIONS --safe --without-K #-}

open import Categories.Category.Instance.Sets
open import Level

open import Categories.Category.Cocartesian

open import Data.Empty.Polymorphic
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Sum
open import Data.Sum.Properties
open import Function.Base

module Category.Instance.Properties.Sets.Cocartesian (o : Level) where
  Sets-Cocartesian : Cocartesian (Sets o)
  Sets-Cocartesian = record 
    { initial = record { ⊥ = ⊥ ; ⊥-is-initial = record { ! = λ () ; !-unique = λ _ () } }
    ; coproducts = record { coproduct = λ {A} {B} → record
      { A+B = A ⊎ B
      ; i₁ = inj₁
      ; i₂ = inj₂
      ; [_,_] = [_,_]
      ; inject₁ = λ _ → refl
      ; inject₂ = λ _ → refl
      ; unique = λ {C} {f} {c₁} {c₂} eq₁ eq₂ x → begin 
        [ c₁ , c₂ ] x ≡⟨ [,]-cong (λ x → sym (eq₁ x)) (λ x → sym (eq₂ x)) x ⟩ 
        [ f ∘′ inj₁ , f ∘′ inj₂ ] x ≡⟨ sym ([,]-∘ f x) ⟩ 
        (f ∘′ [ inj₁ , inj₂ ]) x ≡⟨ helper f x ⟩
        f x ∎
      } }
    }
    where
      helper : ∀ {A} {B} {C} (f : A ⊎ B → C) (x : A ⊎ B) → (f ∘′ [ inj₁ , inj₂ ]) x ≡ f x
      helper {A} {B} f (inj₁ a) = refl
      helper {A} {B} f (inj₂ b) = refl