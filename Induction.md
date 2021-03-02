# Induction

1. 练习 `operators`（实践）

   请给出另一对运算符，它们拥有一个幺元，满足结合律、交换律，且其中一个对另一个满足分配律。 （你不必证明这些性质）

   +

   请给出一个运算符的例子，它拥有幺元、满足结合律但不满足交换律。 （你不必证明这些性质）

   /

2. 练习：`+-swap`（推荐）

   请证明对于所有的自然数 `m`、`n` 和 `p`，

   ```agda
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

   ```agda
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
     
   *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
   *-distrib-+ zero n p = refl
   *-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl  
   
   ```

4. 练习 `*-assoc`（推荐）

   请证明乘法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

   ```agda
   (m * n) * p ≡ m * (n * p)
   ```

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; cong; sym)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
   open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
   
   +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
   +-assoc zero    n p                        = refl
   +-assoc (suc m) n p rewrite +-assoc m n p = refl
   
   *-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
   *-distrib-+ zero n p = refl
   *-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl  
   
   *-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
   *-assoc zero n p = refl
   *-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl
   ```

5. 练习 `*-comm`（实践）

   请证明乘法满足交换律，即对于所有的自然数 `m` 和 `n`，

   ```agda
   m * n ≡ n * m
   ```

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; cong; sym)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
   open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
   
   *-identityʳ : ∀ (n : ℕ) → n * zero ≡ zero
   *-identityʳ zero = refl
   *-identityʳ (suc n) rewrite *-identityʳ n = refl
   
   *-suc : ∀ (m n : ℕ) → m + m * n ≡ m * (suc n)
   *-suc zero n = refl
   *-suc (suc m) n rewrite +-swap m n (m * n) | cong (n +_) (*-suc m n) = refl
   
   *-comm : ∀ (m n : ℕ) → m * n ≡ n * m
   *-comm zero n rewrite *-identityʳ n = refl
   *-comm (suc m) n rewrite *-comm m n | *-suc n m = refl
   ```

6. 练习 `0∸n≡0`（实践）

   请证明对于所有的自然数 `n`，

   ```agda
   zero ∸ n ≡ zero
   ```

   成立。你的证明需要归纳法吗？

   不需要。

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; cong; sym)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
   open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
   
   ∸-identity : ∀ (n : ℕ) → zero ∸ n ≡ zero
   ∸-identity zero = refl
   ∸-identity (suc n) = refl
   ```

7. 练习 `∸-+-assoc`（实践）

   请证明饱和减法与加法满足结合律，即对于所有的自然数 `m`、`n` 和 `p`，

   ```agda
   m ∸ n ∸ p ≡ m ∸ (n + p)
   ```

   成立。

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl; cong; sym)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
   open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)
   
   ∸-identity : ∀ (n : ℕ) → zero ∸ n ≡ zero
   ∸-identity zero = refl
   ∸-identity (suc n) = refl
   
   ∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
   ∸-+-assoc m zero p = refl
   ∸-+-assoc zero (suc n) p rewrite ∸-identity p = refl
   ∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl
   ```

8. 练习 `+*^` （延伸）

   证明下列三条定律

   ```agda
    m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
    (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
    (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)
   ```

   对于所有 `m`、`n` 和 `p` 成立。

   ```agda
   +-identity : ∀ (n : ℕ) → n + zero ≡ n
   +-identity zero = refl
   +-identity (suc n) rewrite +-identity n = refl
   
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
   
   ^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
   ^-*-assoc zero zero p rewrite ^-identity p = refl
   ^-*-assoc zero (suc n) zero rewrite *-comm n zero | *-identity n = refl
   ^-*-assoc zero (suc n) (suc p) = refl
   ^-*-assoc (suc m) n zero rewrite *-identityʳ n = refl
   ^-*-assoc (suc m) n (suc p) rewrite ^-*-assoc (suc m) n p | sym (^-distribˡ-+-* (suc m) n (n * p)) | cong (suc m ^_) (*-suc n p) = refl
   ```

9. 练习 `Bin-laws`（延伸）

   回想练习 [Bin](https://agda-zh.github.io/PLFA-zh/Naturals/#Bin) 中定义的一种表示自然数的比特串数据类型 `Bin` 以及要求你定义的函数：

   ```agda
   inc   : Bin → Bin
   to    : ℕ → Bin
   from  : Bin → ℕ
   ```

   考虑以下定律，其中 `n` 表示自然数，`b` 表示比特串：

   ```agda
   from (inc b) ≡ suc (from b)
   to (from b) ≡ b
   from (to n) ≡ n
   ```

   对于每一条定律：若它成立，请证明；若不成立，请给出一个反例。

   f1: from (inc b) ≡ suc (from b) 

   ```agda
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
   from (m O) = (from m) + (from m)
   from (m I) = ((from m) + (from m)) + (suc zero)
   
   +-lemma : ∀ (m : ℕ) → suc m ≡ m + 1
   +-lemma zero = refl
   +-lemma (suc m) rewrite +-lemma m = refl
   
   f1 : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
   f1 ⟨⟩ = refl
   f1 (b O) rewrite +-identityʳ (from b) | +-comm (from b + from b) 1 = refl
   f1 (b I) rewrite +-identityʳ (from (inc b)) | f1 b | cong (from b +_) (+-identityʳ (from b)) | +-lemma (from b) | sym (+-assoc (from b) (from b) 1) = refl
   
   -- cannot be proved?
   Bin-lemma : ∀ (n : ℕ) → to (n + n) ≡ (to n) O
   Bin-lemma zero = {!   !}
   Bin-lemma (suc n) = {!   !}
   
   -- tried but failed 
   -- because cannot prove ⟨⟩ ≡ ⟨⟩ O 
   -- so it doesn't work
   -- If I change the [to zero ≡ ⟨⟩ O], it needs to prove [(⟨⟩ O) O ≡ ⟨⟩ O]
   -- I cannot prove as before, so it is impossible?
   -- I found someone face the same problem it reddit. ref:https://www.reddit.com/r/agda/comments/f79emg/plfa_relations_problem_bin/
   
   f2 : ∀ (b : Bin) → to (from b) ≡ b
   f2 ⟨⟩ = refl
   f2 (b O) = {!   !}
   f2 (b I) = {!   !} 
   
   f3 : ∀ (n : ℕ) → from (to n) ≡ n
   f3 zero = refl
   f3 (suc n) rewrite f1 (to n) | f3 n = refl
   ```

   

   ​	

   

    
