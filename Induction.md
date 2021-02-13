# Induction

1. 练习 `operators`（实践）

   请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配律。 （你不必证明这些性质）

   +

   请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。 （你不必证明这些性质）

   /

2. 练习：`+-swap`（推荐）

   请证明对于所有的自然数 `m`、`n` 和 `p`，

   ```
   m + (n + p) ≡ n + (m + p)
   ```
   
   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; cong; sym)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
   open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
   
   +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
   +-assoc zero n p =
     begin
       (zero + n) + p
     ≡⟨⟩
       n + p
     ≡⟨⟩
       zero + (n + p)
     ∎
   +-assoc (suc m) n p =
     begin
       (suc m + n) + p
     ≡⟨⟩
       suc (m + n) + p
     ≡⟨⟩
       suc ((m + n) + p)
     ≡⟨ cong suc (+-assoc m n p) ⟩
       suc (m + (n + p))
     ≡⟨⟩
       suc m + (n + p)
     ∎
     
   +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
   +-comm m zero =
     begin
       m + zero
     ≡⟨ +-identityʳ m ⟩
       m
     ≡⟨⟩
       zero + m
     ∎
   +-comm m (suc n) =
     begin
       m + suc n
     ≡⟨ +-suc m n ⟩
       suc (m + n)
     ≡⟨ cong suc (+-comm m n) ⟩
       suc (n + m)
     ≡⟨⟩
       suc n + m
     ∎
   
   +-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
   +-swap m n p rewrite sym (+-assoc m n p) | (+-comm m n) | +-assoc n m p = refl  
   ```

3. 练习 `*-distrib-+`（推荐）

   请证明乘法对加法满足分配律，即对于所有的自然数 `m`、`n` 和 `p`，

   ```
   (m + n) * p ≡ m * p + n * p
   ```

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; cong; sym)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
   open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
   
   +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
   +-assoc zero n p =
     begin
       (zero + n) + p
     ≡⟨⟩
       n + p
     ≡⟨⟩
       zero + (n + p)
     ∎
   +-assoc (suc m) n p =
     begin
       (suc m + n) + p
     ≡⟨⟩
       suc (m + n) + p
     ≡⟨⟩
       suc ((m + n) + p)
     ≡⟨ cong suc (+-assoc m n p) ⟩
       suc (m + (n + p))
     ≡⟨⟩
       suc m + (n + p)
     ∎
     
   +-comm : ∀ (m n : ℕ) → m + n ≡ n + m
   +-comm m zero =
     begin
       m + zero
     ≡⟨ +-identityʳ m ⟩
       m
     ≡⟨⟩
       zero + m
     ∎
   +-comm m (suc n) =
     begin
       m + suc n
     ≡⟨ +-suc m n ⟩
       suc (m + n)
     ≡⟨ cong suc (+-comm m n) ⟩
       suc (n + m)
     ≡⟨⟩
       suc n + m
     ∎
     
   *-distrib- : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
   *-distrib- zero n p = refl
   *-distrib- (suc m) n p rewrite *-distrib- m n p | sym (+-assoc p (m * p) (n * p)) = refl  
   
   ```

   