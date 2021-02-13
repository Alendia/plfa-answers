## Natural

1. 请写出 `7` 的完整定义。

   ```agda
   suc (suc (suc (suc (suc (suc (suc zero))))))
   ```

2. 计算 `3 + 4`，将你的推导过程写成等式链，为 `+` 使用等式。

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
   
   data ℕ : Set where
     zero : ℕ
     suc  : ℕ → ℕ
   
   {-# BUILTIN NATURAL ℕ #-}
   
   _+_ : ℕ → ℕ → ℕ
   zero + n = n
   (suc m) + n = suc (m + n)
   
   _ : 3 + 4 ≡ 7
   _ = 
     begin
       3 + 4
     ≡⟨⟩
       suc (2 + 4)
     ≡⟨⟩
       suc (suc (1 + 4))
     ≡⟨⟩
       suc (suc (suc (0 + 4))) 
     ≡⟨⟩
       suc (suc (suc 4))
     ≡⟨⟩
       7
     ∎
   
   ```

3. 计算 `3 * 4`，将你的推导过程写成等式链，为 `*` 使用等式。 （不必写出 `+` 求值的每一步。）

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
   
   data ℕ : Set where
     zero : ℕ
     suc  : ℕ → ℕ
   
   {-# BUILTIN NATURAL ℕ #-}
   
   _+_ : ℕ → ℕ → ℕ
   zero + n = n
   (suc m) + n = suc (m + n)
   
   _⋆_ : ℕ → ℕ → ℕ
   zero    ⋆ n = zero
   (suc m) ⋆ n = n + (m ⋆ n)
   
   _ =
     begin
       3 ⋆ 4
     ≡⟨⟩
       4 + (2 ⋆ 4)
     ≡⟨⟩
       4 + (4 + (1 ⋆ 4))
     ≡⟨⟩
       4 + (4 + (4 + (0 ⋆ 4)))
     ≡⟨⟩
       12
     ∎
     
   ```

4. 根据以下等式写出乘方的定义。

   ```
   m ^ 0        =  1
   m ^ (1 + n)  =  m * (m ^ n)
   ```

   检查 `3 ^ 4` 是否等于 `81`。

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
   
   data ℕ : Set where
     zero : ℕ
     suc  : ℕ → ℕ
   
   {-# BUILTIN NATURAL ℕ #-}
   
   _+_ : ℕ → ℕ → ℕ
   zero + n = n
   (suc m) + n = suc (m + n)
   
   _⋆_ : ℕ → ℕ → ℕ
   zero    ⋆ n = zero
   (suc m) ⋆ n = n + (m ⋆ n)
   
   _^^_ : ℕ → ℕ → ℕ
   n ^^ zero = suc zero
   n ^^ (suc m) = n ⋆ (n ^^ m)
   
   _ : 3 ^^ 4 ≡ 81
   _ =
     begin
       3 ^^ 4
     ≡⟨⟩
       3 ⋆ (3 ^^ 3)
     ≡⟨⟩
       3 ⋆ (3 ⋆ (3 ^^ 2))
     ≡⟨⟩
       3 ⋆ (3 ⋆ (3 ⋆ (3 ^^ 1)))
     ≡⟨⟩
       3 ⋆ (3 ⋆ (3 ⋆ (3 ⋆ (3 ^^ 0))))
     ≡⟨⟩
       81
     ∎
     
   ```

5. 练习 `∸-example₁` 和 `∸-example₂`（推荐） {#monus-examples}

   计算 `5 ∸ 3` 和 `3 ∸ 5`，将你的推导过程写成等式链。

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
   
   data ℕ : Set where
     zero : ℕ
     suc  : ℕ → ℕ
   
   {-# BUILTIN NATURAL ℕ #-}
   
   _∸_ : ℕ → ℕ → ℕ
   m ∸ zero = m
   zero ∸ suc n = zero
   suc m ∸ suc n = m ∸ n
   
   _ =
     begin
       5 ∸ 3
     ≡⟨⟩
       4 ∸ 2
     ≡⟨⟩
       3 ∸ 1
     ≡⟨⟩
       2 ∸ 0
     ≡⟨⟩
       2
     ∎
   
   _ =
     begin
       3 ∸ 5
     ≡⟨⟩
       2 ∸ 4
     ≡⟨⟩
       1 ∸ 3
     ≡⟨⟩
       0 ∸ 2
     ≡⟨⟩
       0
     ∎
   
   ```

6. 使用二进制系统能提供比一进制系统更高效的自然数表示。我们可以用一个比特串来表示一个数：

   ```agda
   data Bin : Set where
     ⟨⟩ : Bin
     _O : Bin → Bin
     _I : Bin → Bin
   ```

   定义这样一个函数

   ```agda
   inc : Bin → Bin
   ```

   将一个比特串转换成下一个数的比特串。比如，`1100` 编码了十二，我们就应该有：

   ```agda
   inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
   ```

   实现这个函数，并验证它对于表示零到四的比特串都能给出正确结果。

   使用以上的定义，再定义一对函数用于在两种表示间转换。

   ```agda
   to   : ℕ → Bin
   from : Bin → ℕ
   ```

   对于前者，用没有前导零的比特串来表示正数，并用 `x0 nil` 表示零。验证这两个函数都能对零到四给出正确结果。

   ```agda
   import Relation.Binary.PropositionalEquality as Eq
   open Eq using (_≡_; refl)
   open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
   
   data ℕ : Set where
       zero : ℕ
       suc  : ℕ → ℕ
   
   {-# BUILTIN NATURAL ℕ #-}
   
   _+_ : ℕ → ℕ → ℕ
   zero + n = n
   suc m + n = suc (m + n)
   
   _⋆_ : ℕ → ℕ → ℕ
   zero ⋆ n = zero
   suc m ⋆ n = n + (m ⋆ n)
   
   data Bin : Set where
     ⟨⟩  : Bin
     _O : Bin → Bin
     _I : Bin → Bin
   
   inc : Bin → Bin
   inc ⟨⟩ = ⟨⟩
   inc (m O) = m I
   inc (⟨⟩ I) = ⟨⟩ I O
   inc (m I) = (inc m) O
   
   to : ℕ → Bin
   to zero = ⟨⟩ O 
   to (suc m) = inc (to m)
   
   from : Bin → ℕ
   from ⟨⟩ = zero
   from (m O) = 2 ⋆ (from m)
   from (m I) = (2 ⋆ (from m)) + (suc zero)
   
   
   _ =
     begin
       to 2
     ≡⟨⟩
       to (suc 1)
     ≡⟨⟩
       inc (to 1)
     ≡⟨⟩
       inc (inc (to zero))
     ≡⟨⟩
       inc (inc (⟨⟩ O))
     ≡⟨⟩
       inc (⟨⟩ I)
     ≡⟨⟩
       ⟨⟩ I O 
     ∎
   
   _ =
     begin
       to 3
     ≡⟨⟩
       to (suc 2)
     ≡⟨⟩
       inc (to (suc 1))
     ≡⟨⟩
       inc (inc (to 1))
     ≡⟨⟩
       inc (inc (to (suc zero)))  
     ≡⟨⟩
       inc (inc (inc (to zero)))
     ≡⟨⟩
       inc (inc (inc (⟨⟩ O)))
     ≡⟨⟩
       inc (inc (⟨⟩ I))
     ≡⟨⟩
       inc (⟨⟩ I O)
     ≡⟨⟩
       ⟨⟩ I I 
     ∎
   
   _ =
     begin
       inc (⟨⟩ I I)
     ≡⟨⟩
       ⟨⟩ I O O
     ∎
   
   _ =
     begin
       inc (⟨⟩ I O I O)
     ≡⟨⟩
       ⟨⟩ I O I I
     ∎
   
   _ =
     begin
       to 10
     ≡⟨⟩
       inc (to 9)
     ≡⟨⟩
       inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (to zero))))))))))
     ≡⟨⟩
       inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (⟨⟩ O))))))))))
     ≡⟨⟩
       ⟨⟩ I O I O
     ∎
   
   _ =
     begin
       from (⟨⟩ I O)
     ≡⟨⟩
       2 ⋆ (from (⟨⟩ I))
     ≡⟨⟩(
       2 ⋆ (((2 ⋆ (from ⟨⟩)) + (suc zero))))
     ≡⟨⟩ 
       2 ⋆ 1
     ≡⟨⟩ 
       (suc 1) ⋆ 1
     ≡⟨⟩ 
       1 + (1 ⋆ 1)
     ≡⟨⟩ 
       1 + ((suc zero) ⋆ 1)
     ≡⟨⟩ 
       1 + (zero + 1)
     ≡⟨⟩ 
       1 + 1
     ≡⟨⟩
       2
     ∎
   
   ```
   
   





