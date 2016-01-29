module FlatAlgebra where

-- "flat" because we're not playing with universe levels.

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; setoid)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Binary.EqReasoning as EqR

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl refl = refl

-- A semigroup is a set equipped with an associative binary operation.

record IsSemigroup {A : Set} (_•_ : A → A → A) : Set where
  field
    assoc : ∀ x y z → x • (y • z) ≡ (x • y) • z

-- It is easy to see that addition on natural numbers is associative ... 

ℕ+isAssociative : ∀ x y z → x + (y + z) ≡ (x + y) + z
ℕ+isAssociative zero y z = refl
ℕ+isAssociative (suc x) y z = cong suc (ℕ+isAssociative x y z)

-- ... which gives us a semigroup in the obvious way!

ℕ+isSemigroup : IsSemigroup _+_
ℕ+isSemigroup = record { assoc = ℕ+isAssociative }

-- Now, we can use the fact that this is a semigroup to prove other things, for example

module Example₁ where
  open IsSemigroup

  example : ∀ n → n + 2 ≡ (n + 1) + 1
  example n = (assoc ℕ+isSemigroup) n 1 1

-- or, opening the proof that ℕ with + is a semigroup, giving us access to its fields, we can do

module Example₂ where
  open IsSemigroup ℕ+isSemigroup

  example : ∀ n → n + 2 ≡ (n + 1) + 1
  example n = assoc n 1 1

-- we can also open the proof locally, as in

module Example₃ where
  example : ∀ n → n + 2 ≡ (n + 1) + 1
  example n = assoc n 1 1
    where
      open IsSemigroup ℕ+isSemigroup

-- next, a monoid is a semigroup with an identity element

record IsMonoid {A : Set} (_•_ : A → A → A) (e : A) : Set where
  field
    isSemigroup : IsSemigroup _•_
    identity-left : ∀ x → e • x ≡ x
    identity-right : ∀ x → x • e ≡ x

  open IsSemigroup isSemigroup public -- why is this here? (A: whenever we open an IsMonoid, this opens it's IsSemigroup field, allowing us to access it's assoc thing).

-- it is not too hard to show that ℕ , + , and 0 form a monoid. If we show that 0 is a left and right identity...

ℕ+left-identity : ∀ x → 0 + x ≡ x
ℕ+left-identity x = refl

ℕ+right-identity : ∀ x → x + 0 ≡ x
ℕ+right-identity zero = refl
ℕ+right-identity (suc x) = cong suc (ℕ+right-identity x)

-- then we can use our proof that ℕ and + form a semigroup to show that we have a monoid!

ℕ+isMonoid : IsMonoid _+_ 0
ℕ+isMonoid = record { isSemigroup = ℕ+isSemigroup ;
                      identity-left = ℕ+left-identity ;
                      identity-right = ℕ+right-identity }

-- as before, we can use a proof that something is a monoid to prove other things about it.

module Example₄ where
  example : ∀ n → (n + 0) + n ≡ n + n
  example n = cong (λ x → x + n) (identity-right n)
    where
      open IsMonoid ℕ+isMonoid

-- since we did that "open IsSemigroup isSemigroup public" thingy, we can also use the things in the proof that ℕ, + is a semigroup when we open the proof that it's a monoid.

module Example₅ where
  example : ∀ n → n + n ≡ (n + 0) + n
  example n = assoc n 0 n
    where
      open IsMonoid ℕ+isMonoid

-- Let's pretend we're getting tired of writing (A → A → A) all the time, and define the type of binary operations on A

Op₂ : Set → Set
Op₂ A = (A → A → A)

-- using this, we can name properties of binary operations

Associative : {A : Set} → Op₂ A → Set
Associative _•_ = ∀ x y z → (x • y) • z ≡ x • (y • z)

-- this gives us another way to construct the type of proofs that something is a semigroup

record IsSemigroup' {A : Set} (_•_ : Op₂ A) : Set where
  field
    assoc : Associative _•_

-- we can, of course, define other properties of binary operations like this

Commutative : {A : Set} → Op₂ A → Set
Commutative _•_ = ∀ x y → x • y ≡ y • x

-- with the neutral element as a parameter...

LeftIdentity : {A : Set} → A → Op₂ A → Set
LeftIdentity e _•_ = ∀ x → e • x ≡ x

RightIdentity : {A : Set} → A → Op₂ A → Set
RightIdentity e _•_ = ∀ x → x • e ≡ x

Identity : {A : Set} → A → Op₂ A → Set
Identity e _•_ = LeftIdentity e _•_ × RightIdentity e _•_

-- Now, consider the following definition of the commutative monoid property

record IsCommutativeMonoid' {A : Set} (_•_ : A → A → A) (e : A) : Set where
  field
    isMonoid : IsMonoid _•_ e
    commutative : Commutative _•_

-- this is correct, but redundant, since commutativity and the left identity property entail the right identity property.
-- a non-redundant but still easy to use definition of the property is the following

record IsCommutativeMonoid {A : Set} (_•_ : A → A → A) (e : A) : Set where
  field
    isSemigroup : IsSemigroup _•_
    identityˡ : LeftIdentity e _•_
    commutative : Commutative _•_

  open IsSemigroup isSemigroup public

  identity : Identity e _•_
  identity = (identityˡ , identityʳ)
    where
    identityʳ : RightIdentity e _•_
    identityʳ x = trans (commutative x e) (identityˡ x)

  isMonoid : IsMonoid _•_ e
  isMonoid = record { isSemigroup = isSemigroup ;
                      identity-left = proj₁ identity ;
                      identity-right = proj₂ identity }

-- so, when constructing an IsCommutativeMonoid, we supply the IsSemigroup, left identity, and commutative properties, but
-- when using an IsCommutativeMonoid, we have access to those, as well as the associativity, monoid, identity (both) properties!

-- next, we define groups and abelian groups

record IsGroup {A : Set} (_•_ : A → A → A) (e : A) (inv : A → A) : Set where
  field
    isMonoid : IsMonoid _•_ e
    inverseˡ : ∀ x → inv x • x ≡ e
    inverseʳ : ∀ x → x • inv x ≡ e

  open IsMonoid isMonoid public

record IsAbelianGroup {A : Set} (_•_ : A → A → A) (e : A) (inv : A → A) : Set where
  field
    isCommutativeMonoid : IsCommutativeMonoid _•_ e
    inverseˡ : ∀ x → inv x • x ≡ e
    inverseʳ : ∀ x → x • inv x ≡ e

  open IsCommutativeMonoid isCommutativeMonoid public

  isGroup : IsGroup _•_ e inv
  isGroup = record { isMonoid = isMonoid ;
                     inverseˡ = inverseˡ ;
                     inverseʳ = inverseʳ }


-- we can also define the type of all semigroups

record Semigroup : Set₁ where
  field
    Carrier : Set
    _•_ : Op₂ Carrier
    isSemigroup : IsSemigroup _•_

  open IsSemigroup isSemigroup public

-- for example

ℕ+ : Semigroup
ℕ+ = record { Carrier = ℕ ; _•_ = _+_ ; isSemigroup = ℕ+isSemigroup }

-- we can do this for monoids too, obviously

record Monoid : Set₁ where
  field
    Carrier : Set
    e : Carrier
    _•_ : Op₂ Carrier
    isMonoid : IsMonoid _•_ e

  open IsMonoid isMonoid public

  semigroup : Semigroup -- every monoid gives a semigroup!
  semigroup = record { Carrier = Carrier ; _•_ = _•_ ; isSemigroup = isSemigroup }


-- we can define operations that work in any monoid

module MonoidOperations (m : Monoid) where

  open Monoid m

  infixr 7 _×'_

  _×'_ : ℕ → Carrier → Carrier
  zero ×' x = e
  suc n ×' x = x • (n ×' x)

-- ... and so on.

-- this is how the algebra definitions in the standard library work, except:
-- 1. they are over an arbitrary equivalence relation, where there are over _≡_
-- 2. they are universe polymorphic, where these are not.
    
  

  









