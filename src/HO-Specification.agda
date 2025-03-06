-- Theorem 3.7

open import Level
open import Data.Fin.Base
open import Data.Fin.Subset using (Subset)
open import Data.Vec as V using (Vec ; foldr ; [] ; _∷_ ; updateAt; removeAt) renaming (lookup to _!!_)
open import Data.Vec.Membership.Propositional
open import Data.Product using (_,_; Σ-syntax) renaming (Σ to Sigma)
open import Data.Product.Base using () renaming (_×_ to _×⁰_)
open import Data.Sum renaming (_⊎_ to _+⁰_)
open import Data.Unit.Polymorphic using (tt; ⊤)

open import Categories.Category
open import Categories.Category.Instance.Sets renaming (Sets to Agda)
open import Category.Instance.Properties.Sets.Cartesian using () renaming (Sets-Cartesian to Agda-Cartesian)
open import Category.Instance.Properties.Sets.Cocartesian using () renaming (Sets-Cocartesian to Agda-Cocartesian)
open import Categories.Functor hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Functor.Algebra
open import Categories.Category.Construction.F-Algebras
open import Categories.FreeObjects.Free


module HO-Specification (o : Level) where
  open import Example.Signature o

  module _ (Σ : Signature) where
    -- reducing rules
    data HO-reducing (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set where
        var-orig : Fin (arts Σ !! f)     → HO-reducing f W
        var-next : (Sigma _ λ x → x ∈ W) → HO-reducing f W
        var-app  : Fin (arts Σ !! f)     → (Sigma _ λ x → x ∉ W) → HO-reducing f W

    -- evaluating rules
    data HO-evaluating (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set where
      var-n-orig : Fin (arts Σ !! f) → HO-evaluating f W
      var-arg    : HO-evaluating f W
      var-n-next : (Sigma _ λ x → x ∈ W) → HO-evaluating f W
      var-n-app  : (Fin (arts Σ !! f) +⁰ ⊤) ×⁰ Fin (arts Σ !! f) ×⁰ (Sigma _ λ x → x ∉ W) → HO-evaluating f W

    data HO-specification-entry (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) : Set o where
      progressing-rule     : Σ * Level.Lift o (HO-reducing f W) → HO-specification-entry f W
      non-progressing-rule : Σ * Level.Lift o (HO-reducing f W) → HO-specification-entry f W

    record HO-specification : Set o where
      field
        rules : ∀ (f : Fin (ops Σ)) (W : Subset (arts Σ !! f)) → HO-specification-entry f W
    
    B : Bifunctor (Category.op (Agda o)) (Agda o) (Agda o)
    B = {!   !}

    open import HOGSOS (Agda o) (Agda-Cartesian o) (Agda-Cocartesian o) (Sig-Functor Σ) B

    freeAlgebras : ∀ X → FreeObject {C = Agda o} {D = F-Algebras (Sig-Functor Σ)} algebraForgetfulF X
    freeAlgebras X = {!   !}

    open Laws freeAlgebras

    Theorem3-7 : HO-specification → Law
    Theorem3-7 spec = {!   !}
    