import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p                       = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p) | (+-comm m n) | +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-identity : ∀ (m : ℕ) → zero * m ≡ zero
*-identity zero = refl
*-identity (suc m) rewrite *-identity m = refl

*-identityʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-identityʳ zero = refl
*-identityʳ (suc n) rewrite *-identityʳ n = refl

*-suc : ∀ (m n : ℕ) → m + m * n ≡ m * (suc n)
*-suc zero n = refl
*-suc (suc m) n rewrite +-swap m n (m * n) | cong (n +_) (*-suc m n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-identityʳ n = refl
*-comm (suc m) n rewrite *-comm m n | *-suc n m = refl

∸-identity : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-identity zero = refl
∸-identity (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite ∸-identity p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identity (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | sym (*-assoc m (m ^ n) (m ^ p)) = refl

lemma : ∀ m n o → m * n * o ≡ m * o * n
lemma m n o rewrite *-assoc m n o | *-assoc m o n = cong (m *_) (*-comm n o)

-- This need to be considered!!!
f' : ∀ m n o p → (m * n) * (o * p) ≡ (m * o) * (n * p)
f' m n o p rewrite *-comm (m * n) (o * p) | *-comm (m * o) (n * p) | *-assoc o p (m * n) | *-assoc n p (m * o)
  | *-comm o (p * (m * n)) | *-comm n (p * (m * o)) | *-assoc p (m * n) o | *-assoc p (m * o) n = cong (p *_) (lemma m n o)

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p | f' m n (m ^ p) (n ^ p) = refl  

^-identity : ∀ (m : ℕ) → 1 ^ m ≡ 1
^-identity zero = refl
^-identity (suc m) rewrite ^-identity m = refl 

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc zero zero p rewrite ^-identity p = refl
^-*-assoc zero (suc n) zero rewrite *-comm n zero | *-identity n = refl
^-*-assoc zero (suc n) (suc p) = refl
^-*-assoc (suc m) n zero rewrite *-identityʳ n = refl
^-*-assoc (suc m) n (suc p) rewrite ^-*-assoc (suc m) n p | sym (^-distribˡ-+-* (suc m) n (n * p)) | cong (suc m ^_) (*-suc n p) = refl

data Bin : Set where
  ⟨⟩  : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc m) = inc (to m)

from : Bin → ℕ
from ⟨⟩ = zero
from (m O) = 2 * (from m)
from (m I) = (2 * (from m)) + (suc zero)

+-lemma : ∀ (m : ℕ) → suc m ≡ m + 1
+-lemma zero = refl
+-lemma (suc m) rewrite +-lemma m = refl

f1 : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
f1 ⟨⟩ = refl
f1 (b O) rewrite +-identity (from b) | +-comm (from b + from b) 1 = refl
f1 (b I) rewrite +-identity (from (inc b)) | f1 b | cong (from b +_) (+-identity (from b)) | +-lemma (from b) | sym (+-assoc (from b) (from b) 1) = refl


-- cannot be proved?
-- Bin-lemma : ∀ (n : ℕ) → to (n + n) ≡ (to n) O
-- Bin-lemma zero = {!   !}
-- Bin-lemma (suc n) = {!   !}

-- tried but failed 
-- because cannot prove ⟨⟩ ≡ ⟨⟩ O 
-- so it doesn't work
-- If I change the [to zero ≡ ⟨⟩ O], it needs to prove (⟨⟩ O) O ≡ ⟨⟩ o
-- I cannot prove as before, so it is impossible?

-- f2 : ∀ (b : Bin) → to (from b) ≡ b
-- f2 ⟨⟩ = refl
-- f2 (b O) = {!   !}
-- f2 (b I) = {!   !} 

-- test for f2, does it work?
_ =
  begin
    to (from (⟨⟩ O))
  ≡⟨⟩ 
    to (2 * (from ⟨⟩))
  ≡⟨⟩ 
    to zero
  ≡⟨⟩ 
    ⟨⟩ 
  ∎

f3 : ∀ (n : ℕ) → from (to n) ≡ n
f3 zero = refl
f3 (suc n) rewrite f1 (to n) | f3 n = refl
