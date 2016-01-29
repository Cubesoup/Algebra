module StandardAlgebra where

open import Data.Nat
open import Algebra
open import Algebra.Structures using (IsSemigroup)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Core 
open import Algebra.FunctionProperties

ℕ+-assoc : Associative _≡_ _+_
ℕ+-assoc zero y z = refl
ℕ+-assoc (suc x) y z = cong suc (ℕ+-assoc x y z)

ℕ+0-left-identity : LeftIdentity _≡_ 0 _+_
ℕ+0-left-identity x = refl

ℕ+0-right-identity : RightIdentity _≡_ 0 _+_
ℕ+0-right-identity zero = refl
ℕ+0-right-identity (suc x) = cong suc (ℕ+0-right-identity x)

ℕ+-preserves-≡ : ∀ x y z w → x ≡ w → y ≡ z → (x + y) ≡ (w + z)
ℕ+-preserves-≡ x y z w x=w y=z = trans (cong (λ x₁ → x₁ + y) x=w) 
                                        (cong (λ y₁ → w + y₁) y=z)

ℕ+-isSemigroup : IsSemigroup _≡_ _+_
ℕ+-isSemigroup = record { isEquivalence = isEquivalence ; 
                          assoc = ℕ+-assoc ; 
                          ∙-cong = {!!} }
