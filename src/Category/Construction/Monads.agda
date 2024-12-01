open import Categories.Category.Core
open import Categories.Monad hiding (id)
open import Categories.NaturalTransformation using (_∘ᵥ_; NaturalTransformation) renaming (id to idN)
open import Level
open import Categories.NaturalTransformation.Equivalence using (_≃_; ≃-isEquivalence)
open import Relation.Binary.Structures using (IsEquivalence)

import Categories.Morphism as MM
import Categories.Morphism.Reasoning as MR

module Category.Construction.Monads where
  private 
    variable
      o ℓ e : Level

  module _ (C : Category o ℓ e) where
    open Category C
    open Equiv
    open HomReasoning
    open MM C
    open MR C

    record Monad⇒ (M : Monad C) (N : Monad C) : Set (o ⊔ ℓ ⊔ e) where
      module M = Monad M
      module N = Monad N
      field
        α : NaturalTransformation M.F N.F
      module α = NaturalTransformation α
      field
        α-η : ∀ {X} → α.η X ∘ M.η.η X ≈ N.η.η X
        α-μ : ∀ {X} → α.η X ∘ M.μ.η X ≈ N.μ.η X ∘ α.η (N.F.₀ X) ∘ M.F.₁ (α.η X)

    Monads : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) (o ⊔ e)
    Monads .Obj = Monad C
    Monads ._⇒_ M N = Monad⇒ M N
    Monads ._≈_ α β = Monad⇒.α α ≃ Monad⇒.α β
    Monads .id {M} = record { α = idN ; α-η = identityˡ ; α-μ = identityˡ ○ sym (elimʳ (identityˡ ○ Monad.F.identity M)) }
    Monads ._∘_ α β = record 
      { α = α.α ∘ᵥ β.α 
      ; α-η = pullʳ β.α-η ○ α.α-η 
      ; α-μ = pullʳ β.α-μ ○ extendʳ α.α-μ ○ ∘-resp-≈ʳ (pullʳ (extendʳ (sym (β.α.commute (α.α.η _))) ○ ∘-resp-≈ʳ (sym (β.M.F.homomorphism))) ○ sym-assoc) 
      }
      where 
        module α = Monad⇒ α
        module β = Monad⇒ β
    Monads .assoc = assoc
    Monads .sym-assoc = sym-assoc
    Monads .identityˡ = identityˡ
    Monads .identityʳ = identityʳ
    Monads .identity² = identity²
    Monads .equiv = record { refl = refl ; sym = λ eq → sym eq ; trans = λ eq eq′ → trans eq eq′ }
    Monads .∘-resp-≈ eq eq′ = ∘-resp-≈ eq eq′
