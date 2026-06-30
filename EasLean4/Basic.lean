import Init.Data.Fin.Basic
import Init.Data.Nat.Basic

namespace EAS

/--
认知系统的基本结构

使用 Fin n 和 Fin m 表示有限类型，完全基于标准库。

S ⊂ E (物理嵌入) → n < m (基数约束)
n: 表征空间大小 (|R_S|)
m: 环境空间大小 (|E|)
T_R: 系统内部动力学 (Fin n → Fin n)
T_E: 环境动力学 (Fin m → Fin m)
-/
structure CognitiveSystem (n m : Nat) where
  /-- 系统内部动力学 -/
  T_R : Fin n → Fin n
  /-- 环境动力学 -/
  T_E : Fin m → Fin m
  /-- 基数约束：|R_S| < |E| (A1(a) 物理嵌入的直接推论) -/
  card_constraint : n < m

namespace CognitiveSystem

/-- 认知余量 d = |E| - |R_S| -/
def epistemicResidue {n m : Nat} (S : CognitiveSystem n m) : Nat :=
  m - n

/-- 认知余量为正（由 A1(a) 保证） -/
theorem epistemicResidue_pos {n m : Nat} (S : CognitiveSystem n m) :
    S.epistemicResidue > 0 :=
  Nat.sub_pos_of_lt S.card_constraint

end CognitiveSystem

/-- 区分操作：将每个元素映射到其等价类 -/
def Distinction (E : Type _) := E → E → Prop

/-- 由映射 f 诱导的等价关系 -/
def InducedEquivalence {E R : Type _} (f : E → R) : E → E → Prop :=
  fun x y => f x = f y

namespace InducedEquivalence

theorem refl {E R : Type _} (f : E → R) (x : E) :
    InducedEquivalence f x x := rfl

theorem symm {E R : Type _} (f : E → R) {x y : E} :
    InducedEquivalence f x y → InducedEquivalence f y x :=
  fun h => Eq.symm h

theorem trans {E R : Type _} (f : E → R) {x y z : E} :
    InducedEquivalence f x y → InducedEquivalence f y z → InducedEquivalence f x z :=
  fun h₁ h₂ => Eq.trans h₁ h₂

end InducedEquivalence

/-!
## 函数性质

标准库中没有 Function.Injective 等，这里手动定义。
-/

/-- 单射函数 -/
def Injective {α β : Type _} (f : α → β) : Prop :=
  ∀ x y : α, f x = f y → x = y

/-- 满射函数 -/
def Surjective {α β : Type _} (f : α → β) : Prop :=
  ∀ y : β, ∃ x : α, f x = y

/-- 双射函数 = 单射 + 满射 -/
def Bijective {α β : Type _} (f : α → β) : Prop :=
  Injective f ∧ Surjective f

/-!
## 鸽巢原理 (Pigeonhole Principle)

对 `Fin n` 的构造性证明：若 n < m，则任何函数 f : Fin m → Fin n 都不是单射。

证明策略：对 n 进行归纳。
- 基例 n = 0：f : Fin m → Fin 0，若 m > 0 则 Fin m 有元素但 Fin 0 没有，矛盾。
- 归纳步：假设对 n 成立，证明对 n + 1 成立。
  给定 f : Fin (m + 1) → Fin (n + 1) 是单射，n + 1 < m + 1 即 n < m。
  令 y0 := f 0。
  因为 f 是单射，所以对所有 i : Fin m，f (Fin.succ i) ≠ y0。
  我们需要定义 g : Fin m → Fin n，使得 g 是单射。
  
  关键技巧：用 Fin.pred 把非零元素映射到 Fin n。
  但 y0 不一定是 0，所以我们需要一个"交换"操作。
  
  简化方法：用 Fin.rev 或直接分类讨论 y0 的值。
  
  更简单的方法：证明一个更强的命题，对 m 归纳。
  实际上，我们可以用对 n 的归纳，但需要先证明：
  对于任意 y : Fin (n + 1)，存在一个双射 s : Fin (n + 1) → Fin (n + 1)
  使得 s y = 0。这样 s ∘ f 就是单射且 (s ∘ f) 0 = 0。
  
  但构造双射比较繁琐。让我们换一种方法：
  证明对所有 m n，n < m → ¬Injective (f : Fin m → Fin n)
  对 m 归纳。
  
  实际上最简单的是用自然数版本的鸽巢原理，然后提升到 Fin。
  但我们没有自然数版本。
  
  让我们试试这个方法：对 n 归纳。
  定理：∀ n, ∀ m, n < m → ∀ (f : Fin m → Fin n), ¬Injective f
  
  基例 n = 0：
    m > 0，存在 x : Fin m，f x : Fin 0，但 Fin 0 没有元素，矛盾。
  
  归纳步：假设对 n 成立，证明对 n + 1 成立。
    设 f : Fin (m + 1) → Fin (n + 1) 是单射，且 n + 1 < m + 1，即 n < m。
    
    考虑两种情况：
    情况1：∃ i : Fin m, f (Fin.succ i) = 0
      则 f (Fin.succ i) = 0 = f 0？不，f 0 不一定是 0。
      
    等等，让我们重新组织。
    
    令 S := { f (Fin.succ i) | i : Fin m }，这是 f 在 Fin m 上的像。
    因为 f 是单射，所以 |S| = m。
    但 S ⊆ Fin (n + 1)，所以 |S| ≤ n + 1。
    因此 m ≤ n + 1。
    但我们有 n < m，所以 n < m ≤ n + 1，即 m = n + 1。
    这说明 S = Fin (n + 1)（因为大小都是 n + 1）。
    特别地，存在 i : Fin m 使得 f (Fin.succ i) = f 0。
    但 f 是单射，所以 Fin.succ i = 0，矛盾。
    
    这个论证需要"有限集的大小"理论，我们没有。
    
    让我们用更构造性的方法。
    
    实际上，让我们用经典逻辑+归纳。
    对 n 归纳证明：∀ m, n < m → ∀ (f : Fin m → Fin n), ¬Injective f
    
    归纳步，给定 f : Fin (m + 1) → Fin (n + 1) 单射，n < m。
    令 y0 := f 0。
    
    考虑函数 g : Fin m → Fin (n + 1)，g i := f (Fin.succ i)。
    g 是单射（因为 f 是单射）。
    且对所有 i，g i ≠ y0（因为 f 是单射且 Fin.succ i ≠ 0）。
    
    现在我们需要从 g 构造一个单射 h : Fin m → Fin n。
    
    如果 y0 = 0，那么对所有 i，g i ≠ 0，所以我们可以用 Fin.pred，
    h i := Fin.pred (g i) (show g i ≠ 0 from _)
    然后 h 是单射。
    
    如果 y0 ≠ 0，那么... 我们需要把 y0 "移动"到 0 的位置。
    
    让我们证明一个引理：
    对任意 y : Fin (k + 1)，存在一个函数 s : Fin (k + 1) → Fin (k + 1)
    使得 s 是单射且 s y = 0。
    
    实际上，我们不需要 s 是双射，只需要：
    如果 g : Fin m → Fin (k + 1) 是单射且 g i ≠ y 对所有 i，
    那么存在 h : Fin m → Fin k 是单射。
    
    让我们直接构造 h。给定 y : Fin (k + 1) 和 x : Fin (k + 1) 且 x ≠ y，
    定义 h(x) : Fin k 为：
      如果 x.val < y.val，则 h(x).val = x.val
      如果 x.val > y.val，则 h(x).val = x.val - 1
    
    这就是"去掉 y 后重新编号"。
-/

/--
给定 y : Fin (k + 1) 和 x : Fin (k + 1) 且 x ≠ y，
将 x 映射到 Fin k（相当于从 Fin (k+1) 中去掉 y）。
-/
def removeElem {k : Nat} (y : Fin (k + 1)) (x : Fin (k + 1)) (h : x ≠ y) : Fin k :=
  if hlt : x.val < y.val then
    ⟨x.val, by
      have h1 : x.val < y.val := hlt
      have h2 : y.val < k + 1 := y.isLt
      omega⟩
  else
    have hgt : y.val < x.val := by
      have h1 : x.val ≠ y.val := by
        intro h2
        have h3 : x = y := Fin.ext h2
        exact h h3
      have h4 : ¬x.val < y.val := hlt
      omega
    ⟨x.val - 1, by omega⟩

/-- removeElem y 是单射（当 x ≠ y 时） -/
theorem removeElem_inj {k : Nat} (y : Fin (k + 1)) :
    ∀ (x1 x2 : Fin (k + 1)) (h1 : x1 ≠ y) (h2 : x2 ≠ y),
      removeElem y x1 h1 = removeElem y x2 h2 → x1 = x2 := by
  intro x1 x2 h1 h2 h_eq
  have h_val_eq : (removeElem y x1 h1).val = (removeElem y x2 h2).val :=
    Fin.val_eq_of_eq h_eq
  have h_cases1 : x1.val < y.val ∨ x1.val > y.val := by
    have h_ne : x1.val ≠ y.val := by
      intro h
      have h' : x1 = y := Fin.ext h
      exact h1 h'
    omega
  have h_cases2 : x2.val < y.val ∨ x2.val > y.val := by
    have h_ne : x2.val ≠ y.val := by
      intro h
      have h' : x2 = y := Fin.ext h
      exact h2 h'
    omega
  have h_main : x1.val = x2.val := by
    rcases h_cases1 with (h1_lt | h1_gt)
    · -- x1.val < y.val
      rcases h_cases2 with (h2_lt | h2_gt)
      · -- x2.val < y.val
        have h5 : (removeElem y x1 h1).val = x1.val := by
          rw [removeElem, dif_pos h1_lt] <;> rfl
        have h6 : (removeElem y x2 h2).val = x2.val := by
          rw [removeElem, dif_pos h2_lt] <;> rfl
        rw [h5, h6] at h_val_eq
        exact h_val_eq
      · -- x2.val > y.val
        have h5 : (removeElem y x1 h1).val = x1.val := by
          rw [removeElem, dif_pos h1_lt] <;> rfl
        have h6 : (removeElem y x2 h2).val = x2.val - 1 := by
          rw [removeElem, dif_neg (show ¬x2.val < y.val from by omega)] <;> rfl
        rw [h5, h6] at h_val_eq
        omega
    · -- x1.val > y.val
      rcases h_cases2 with (h2_lt | h2_gt)
      · -- x2.val < y.val
        have h5 : (removeElem y x1 h1).val = x1.val - 1 := by
          rw [removeElem, dif_neg (show ¬x1.val < y.val from by omega)] <;> rfl
        have h6 : (removeElem y x2 h2).val = x2.val := by
          rw [removeElem, dif_pos h2_lt] <;> rfl
        rw [h5, h6] at h_val_eq
        omega
      · -- x2.val > y.val
        have h5 : (removeElem y x1 h1).val = x1.val - 1 := by
          rw [removeElem, dif_neg (show ¬x1.val < y.val from by omega)] <;> rfl
        have h6 : (removeElem y x2 h2).val = x2.val - 1 := by
          rw [removeElem, dif_neg (show ¬x2.val < y.val from by omega)] <;> rfl
        rw [h5, h6] at h_val_eq
        omega
  exact Fin.ext h_main

/--
鸽巢原理：若 n < m，则任何函数 f : Fin m → Fin n 都不是单射。

对 m 进行归纳证明。
-/
theorem pigeonholePrinciple : ∀ (m : Nat), ∀ (n : Nat), n < m → ∀ (f : Fin m → Fin n), ¬Injective f := by
  intro m
  induction m with
  | zero =>
    intro n h f h_inj
    exfalso
    exact Nat.not_lt_zero n h
  | succ m ih =>
    intro n h f h_inj
    have h_n_pos : 0 < n := by
      have h_pos : 0 < Nat.succ m := Nat.zero_lt_succ m
      let x0 : Fin (Nat.succ m) := ⟨0, h_pos⟩
      let y := f x0
      have h4 : y.val < n := y.isLt
      have h_cases : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      match h_cases with
      | Or.inl h_n0 =>
        have h5 : y.val < 0 := by
          have h6 : y.val < n := h4
          exact h_n0 ▸ h6
        exact absurd h5 (by omega)
      | Or.inr h_pos_n =>
        exact h_pos_n
    let n' := n - 1
    have hn_eq : n = n' + 1 := by omega
    have h_n'_lt_m : n' < m := by omega
    let x0 : Fin (Nat.succ m) := ⟨0, Nat.zero_lt_succ m⟩
    let y0_val : Nat := (f x0).val
    have h_y0_lt_n : y0_val < n := (f x0).isLt
    have h_y0_lt_succ_n' : y0_val < n' + 1 := by
      rw [←hn_eq]
      exact h_y0_lt_n
    let y0' : Fin (n' + 1) := ⟨y0_val, h_y0_lt_succ_n'⟩
    let g : Fin m → Fin (n' + 1) := fun i =>
      let fi_val := (f (Fin.succ i)).val
      have hfi_lt_n : fi_val < n := (f (Fin.succ i)).isLt
      have hfi_lt_succ_n' : fi_val < n' + 1 := by
        rw [←hn_eq]
        exact hfi_lt_n
      ⟨fi_val, hfi_lt_succ_n'⟩
    have h_g_inj : Injective g := by
      intro i1 i2 h_eq
      have h1 : (g i1).val = (g i2).val := Fin.val_eq_of_eq h_eq
      have h2 : (f (Fin.succ i1)).val = (f (Fin.succ i2)).val := h1
      have h3 : f (Fin.succ i1) = f (Fin.succ i2) := Fin.ext h2
      have h4 : Fin.succ i1 = Fin.succ i2 := h_inj (Fin.succ i1) (Fin.succ i2) h3
      have h5 : (Fin.succ i1).val = (Fin.succ i2).val := Fin.val_eq_of_eq h4
      have h6 : i1.val + 1 = i2.val + 1 := h5
      have h7 : i1.val = i2.val := by omega
      exact Fin.ext h7
    have h_g_ne_y0 : ∀ (i : Fin m), g i ≠ y0' := by
      intro i h_eq
      have h1 : (g i).val = y0'.val := Fin.val_eq_of_eq h_eq
      have h2 : (f (Fin.succ i)).val = (f x0).val := h1
      have h3 : f (Fin.succ i) = f x0 := Fin.ext h2
      have h4 : Fin.succ i = x0 := h_inj (Fin.succ i) x0 h3
      have h5 : (Fin.succ i).val = x0.val := Fin.val_eq_of_eq h4
      have h6 : i.val + 1 = 0 := h5
      omega
    let h : Fin m → Fin n' := fun i =>
      removeElem y0' (g i) (h_g_ne_y0 i)
    have h_h_inj : Injective h := by
      intro i1 i2 h_eq
      have h1 : removeElem y0' (g i1) (h_g_ne_y0 i1) = removeElem y0' (g i2) (h_g_ne_y0 i2) := h_eq
      have h2 : g i1 = g i2 := removeElem_inj y0' (g i1) (g i2) (h_g_ne_y0 i1) (h_g_ne_y0 i2) h1
      exact h_g_inj i1 i2 h2
    exact ih n' h_n'_lt_m h h_h_inj

end EAS
