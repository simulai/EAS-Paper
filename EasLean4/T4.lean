import EasLean4.Basic

namespace EAS

namespace T4

/-
## T4 真理定理 (Truth Theorem)

有限度量空间上的巴拿赫压缩映射定理。
真理 = 认知压缩映射的不动点。
-/

/-
### 辅助小引理
-/

private theorem mul_gt_self (k : Nat) (hk : k ≥ 2) (n : Nat) (hn : 0 < n) : k * n > n := by
  have h1 : k ≥ 2 := hk
  have h2 : k * n ≥ 2 * n := Nat.mul_le_mul_right n h1
  have h3 : 2 * n = n + n := by
    have h4 : n * 2 = n + n := Nat.mul_two n
    have h5 : 2 * n = n * 2 := Nat.mul_comm 2 n
    rw [h5, h4]
  rw [h3] at h2
  have h5 : n + n > n := by
    have h6 : 0 < n := hn
    have h7 : n + n > n := Nat.add_lt_add_left h6 n
    exact h7
  exact Nat.lt_of_lt_of_le h5 h2

private theorem eq_zero_of_mul_eq_zero (a b : Nat) (h : a * b = 0) (ha : 0 < a) : b = 0 := by
  have h1 : a * b = 0 := h
  have h2 : a > 0 := ha
  by_cases h3 : b = 0
  · exact h3
  · have h4 : 0 < b := Nat.pos_of_ne_zero h3
    have h5 : 0 < a * b := Nat.mul_pos h2 h4
    rw [h1] at h5
    exact False.elim (Nat.not_lt_zero 0 h5)

private theorem min_le_max (a b : Nat) : Nat.min a b ≤ Nat.max a b := by
  have h1 : Nat.min a b ≤ a := Nat.min_le_left a b
  have h2 : a ≤ Nat.max a b := Nat.le_max_left a b
  exact Nat.le_trans h1 h2

/-
### 有限度量空间
-/

/-- Fin m 上的度量：自然数绝对值差 -/
def dist {m : Nat} (x y : Fin m) : Nat :=
  Nat.max x.val y.val - Nat.min x.val y.val

theorem dist_self {m : Nat} (x : Fin m) : dist x x = 0 := by
  have h1 : Nat.max x.val x.val = x.val := Nat.max_self x.val
  have h2 : Nat.min x.val x.val = x.val := Nat.min_self x.val
  unfold dist
  rw [h1, h2]
  exact Nat.sub_self x.val

theorem dist_eq_zero {m : Nat} (x y : Fin m) : dist x y = 0 → x = y := by
  intro h
  have h1 : Nat.max x.val y.val - Nat.min x.val y.val = 0 := h
  have h2 : Nat.max x.val y.val ≤ Nat.min x.val y.val := Nat.le_of_sub_eq_zero h1
  have h3 : Nat.min x.val y.val ≤ Nat.max x.val y.val := min_le_max x.val y.val
  have h4 : Nat.max x.val y.val = Nat.min x.val y.val := Nat.le_antisymm h2 h3
  have h5 : x.val = y.val := by
    have h6 : x.val ≤ y.val ∨ y.val ≤ x.val := Nat.le_total x.val y.val
    cases h6 with
    | inl h7 =>
      have h8 : Nat.max x.val y.val = y.val := Nat.max_eq_right h7
      have h9 : Nat.min x.val y.val = x.val := Nat.min_eq_left h7
      rw [h8, h9] at h4
      exact Eq.symm h4
    | inr h7 =>
      have h8 : Nat.max x.val y.val = x.val := Nat.max_eq_left h7
      have h9 : Nat.min x.val y.val = y.val := Nat.min_eq_right h7
      rw [h8, h9] at h4
      exact h4
  exact Fin.ext h5

theorem dist_comm {m : Nat} (x y : Fin m) : dist x y = dist y x := by
  unfold dist
  have h1 : Nat.max x.val y.val = Nat.max y.val x.val := Nat.max_comm x.val y.val
  have h2 : Nat.min x.val y.val = Nat.min y.val x.val := Nat.min_comm x.val y.val
  rw [h1, h2]

/-
### 压缩映射
-/

def Contraction {m : Nat} (f : Fin m → Fin m) : Prop :=
  ∃ k : Nat, k ≥ 2 ∧ ∀ (x y : Fin m), k * dist (f x) (f y) ≤ dist x y

def FixedPoint {m : Nat} (f : Fin m → Fin m) (x : Fin m) : Prop :=
  f x = x

/-
### 函数迭代
-/

def iter {m : Nat} (f : Fin m → Fin m) : Nat → Fin m → Fin m
  | 0, x => x
  | n + 1, x => f (iter f n x)

theorem iter_zero {m : Nat} (f : Fin m → Fin m) (x : Fin m) :
    iter f 0 x = x := by rfl

theorem iter_succ {m : Nat} (f : Fin m → Fin m) (n : Nat) (x : Fin m) :
    iter f (n + 1) x = f (iter f n x) := by rfl

theorem iter_comm_f {m : Nat} (f : Fin m → Fin m) :
    ∀ (n : Nat) (x : Fin m), iter f n (f x) = f (iter f n x) := by
  intro n x
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iter_succ, iter_succ, ih]
    <;> rfl

theorem iter_add {m : Nat} (f : Fin m → Fin m) :
    ∀ (n k : Nat) (x : Fin m), iter f (n + k) x = iter f k (iter f n x) := by
  intro n k x
  induction n with
  | zero =>
    have h1 : 0 + k = k := Nat.zero_add k
    rw [h1]
    <;> rfl
  | succ n ih =>
    have h4 : n + 1 + k = (n + k) + 1 := by
      have h5 : n + 1 + k = n + (1 + k) := Nat.add_assoc n 1 k
      have h6 : n + (1 + k) = n + (k + 1) := by
        have h7 : 1 + k = k + 1 := Nat.add_comm 1 k
        rw [h7]
      have h8 : n + (k + 1) = n + k + 1 := (Nat.add_assoc n k 1).symm
      rw [h5, h6, h8]
    rw [h4]
    rw [iter_succ, ih, iter_succ, iter_comm_f f k]
    <;> rfl

/-
### 压缩迭代的距离衰减
-/

theorem contraction_iter_decay {m : Nat} {f : Fin m → Fin m}
    (k : Nat) (_hk2 : k ≥ 2)
    (hk : ∀ (x y : Fin m), k * dist (f x) (f y) ≤ dist x y) :
    ∀ (n : Nat) (x y : Fin m), k ^ n * dist (iter f n x) (iter f n y) ≤ dist x y := by
  intro n
  induction n with
  | zero =>
    intro x y
    have h1 : k ^ 0 = 1 := Nat.pow_zero k
    rw [h1]
    have h2 : 1 * dist (iter f 0 x) (iter f 0 y) = dist x y := by
      rw [iter_zero, iter_zero]
      exact Nat.one_mul (dist x y)
    rw [h2]
    exact Nat.le_refl (dist x y)
  | succ n ih =>
    intro x y
    have h1 : k ^ (n + 1) = k ^ n * k := by
      exact Nat.pow_succ k n
    have h2 : dist (iter f (n + 1) x) (iter f (n + 1) y) = dist (f (iter f n x)) (f (iter f n y)) := by
      rw [iter_succ, iter_succ]
      <;> rfl
    rw [h1, h2]
    have h3 : k * dist (f (iter f n x)) (f (iter f n y)) ≤ dist (iter f n x) (iter f n y) :=
      hk (iter f n x) (iter f n y)
    have h4 : k ^ n * (k * dist (f (iter f n x)) (f (iter f n y))) ≤ k ^ n * dist (iter f n x) (iter f n y) :=
      Nat.mul_le_mul_left (k ^ n) h3
    have h5 : k ^ n * k * dist (f (iter f n x)) (f (iter f n y)) = k ^ n * (k * dist (f (iter f n x)) (f (iter f n y))) := by
      exact Nat.mul_assoc (k ^ n) k (dist (f (iter f n x)) (f (iter f n y)))
    have h6 : k ^ n * k * dist (f (iter f n x)) (f (iter f n y)) ≤ k ^ n * dist (iter f n x) (iter f n y) := by
      rw [h5]
      exact h4
    have h7 : k ^ n * dist (iter f n x) (iter f n y) ≤ dist x y := ih x y
    exact Nat.le_trans h6 h7

/-
### 不动点存在性
-/

theorem iter_eventually_repeats {m : Nat} (f : Fin m → Fin m) (x : Fin m) :
    ∃ i j : Nat, i < j ∧ iter f i x = iter f j x := by
  let g : Fin (m + 1) → Fin m := fun k => iter f k.val x
  have h_inj : ¬Injective g := pigeonholePrinciple (m + 1) m (Nat.lt_succ_self m) g
  have h1 : ∃ a b : Fin (m + 1), g a = g b ∧ a ≠ b := by
    simpa [Injective] using h_inj
  match h1 with
  | ⟨a, b, heq, hne⟩ =>
    have h_cases : a.val < b.val ∨ b.val < a.val := by
      have h2 : a.val ≠ b.val := by
        intro h3
        have h4 : a = b := Fin.ext h3
        exact hne h4
      exact Nat.lt_or_gt_of_ne h2
    cases h_cases with
    | inl hlt =>
      exact ⟨a.val, b.val, hlt, heq⟩
    | inr hgt =>
      exact ⟨b.val, a.val, hgt, Eq.symm heq⟩

theorem periodic_implies_fixed {m : Nat} {f : Fin m → Fin m}
    (k : Nat) (hk2 : k ≥ 2)
    (hk : ∀ (x y : Fin m), k * dist (f x) (f y) ≤ dist x y)
    (x : Fin m) (n : Nat) (hn_pos : 0 < n)
    (h_per : iter f n x = x) :
    FixedPoint f x := by
  have h_iter_decay := contraction_iter_decay k hk2 hk
  have h_comm : ∀ n x, iter f n (f x) = f (iter f n x) := by
    intro n x
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iter_succ, ih, iter_succ]
      <;> rfl
  have h1 : k ^ n * dist (iter f n (f x)) (iter f n x) ≤ dist (f x) x := h_iter_decay n (f x) x
  have h2 : iter f n (f x) = f (iter f n x) := h_comm n x
  have h_main : k ^ n * dist (f x) x ≤ dist (f x) x := by
    rw [h2] at h1
    have h3 : f (iter f n x) = f x := by rw [h_per]
    rw [h3] at h1
    have h4 : iter f n x = x := h_per
    rw [h4] at h1
    exact h1
  have h9 : dist (f x) x = 0 := by
    match Classical.em (dist (f x) x = 0) with
    | Or.inl h10 => exact h10
    | Or.inr h10 =>
      have h11 : 0 < dist (f x) x := Nat.pos_of_ne_zero h10
      have h12 : k ^ n ≥ 2 := by
        have h13 : k ≥ 2 := hk2
        have h14 : ∀ n : Nat, k ^ n ≥ 2 ^ n := by
          intro n
          exact Nat.pow_le_pow_of_le_left h13 n
        have h15 : 2 ^ n ≥ 2 := by
          have h16 : 0 < n := hn_pos
          cases n with
          | zero => exact False.elim (Nat.not_lt_zero 0 h16)
          | succ n' =>
            have h17 : 2 ^ (n' + 1) = 2 ^ n' * 2 := by
              exact Nat.pow_succ 2 n'
            rw [h17]
            have h18 : 2 ^ n' * 2 ≥ 2 := by
              have h19 : 2 ^ n' ≥ 1 := by
                have h20 : ∀ k : Nat, 2 ^ k ≥ 1 := by
                  intro k
                  induction k with
                  | zero => decide
                  | succ k ih =>
                    have h21 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
                    rw [h21]
                    have h22 : 2 ^ k ≥ 1 := ih
                    have h23 : 2 ^ k * 2 ≥ 1 * 2 := Nat.mul_le_mul_right 2 h22
                    have h24 : 1 * 2 = 2 := by decide
                    rw [h24] at h23
                    omega
                exact h20 n'
              have h21 : 2 ^ n' * 2 ≥ 1 * 2 := Nat.mul_le_mul_right 2 h19
              have h22 : 1 * 2 = 2 := by decide
              rw [h22] at h21
              exact h21
            exact h18
        have h16 : k ^ n ≥ 2 ^ n := h14 n
        exact Nat.le_trans h15 h16
      have h17 : k ^ n * dist (f x) x > dist (f x) x := mul_gt_self (k ^ n) h12 (dist (f x) x) h11
      have h18 : ¬ (k ^ n * dist (f x) x ≤ dist (f x) x) := Nat.not_le.mpr h17
      exact False.elim (h18 h_main)
  have h12 : f x = x := dist_eq_zero (f x) x h9
  exact h12

theorem contraction_fixed_point_exists {m : Nat} {f : Fin m → Fin m} (hm : 0 < m) (h : Contraction f) :
    ∃ x : Fin m, FixedPoint f x := by
  match h with
  | ⟨k, hk2, hk⟩ =>
    let x0 : Fin m := ⟨0, hm⟩
    have h_rep := iter_eventually_repeats f x0
    match h_rep with
    | ⟨i, j, hlt, heq⟩ =>
      let y := iter f i x0
      let n := j - i
      have hn_pos : 0 < n := Nat.sub_pos_of_lt hlt
      have h_per : iter f n y = y := by
        dsimp only [y, n]
        have h1 : i + (j - i) = j := Nat.add_sub_of_le (Nat.le_of_lt hlt)
        have h2 : iter f (i + (j - i)) x0 = iter f (j - i) (iter f i x0) := iter_add f i (j - i) x0
        have h3 : iter f j x0 = iter f (j - i) (iter f i x0) := by
          have h4 : i + (j - i) = j := h1
          rw [h4] at h2
          exact h2
        have h5 : iter f (j - i) (iter f i x0) = iter f i x0 := by
          have h6 : iter f j x0 = iter f i x0 := Eq.symm heq
          rw [←h3, h6]
        exact h5
      have h_fixed : FixedPoint f y := periodic_implies_fixed k hk2 hk y n hn_pos h_per
      exact ⟨y, h_fixed⟩

theorem contraction_fixed_point_unique {m : Nat} {f : Fin m → Fin m} (h : Contraction f)
    (x y : Fin m) (hx : FixedPoint f x) (hy : FixedPoint f y) : x = y := by
  match h with
  | ⟨k, hk2, hk⟩ =>
    have h1 : k * dist x y ≤ dist x y := by
      have h2 : f x = x := hx
      have h3 : f y = y := hy
      have h4 : k * dist (f x) (f y) ≤ dist x y := hk x y
      rw [h2, h3] at h4
      exact h4
    have h5 : k ≥ 2 := hk2
    have h6 : dist x y = 0 := by
      match Classical.em (dist x y = 0) with
      | Or.inl h7 => exact h7
      | Or.inr h7 =>
        have h8 : 0 < dist x y := Nat.pos_of_ne_zero h7
        have h9 : k * dist x y > dist x y := mul_gt_self k h5 (dist x y) h8
        have h10 : ¬ (k * dist x y ≤ dist x y) := Nat.not_le.mpr h9
        exact False.elim (h10 h1)
    exact dist_eq_zero x y h6

/-
### 巴拿赫不动点定理（有限版本）
-/

theorem banach_fixed_point_theorem {m : Nat} {f : Fin m → Fin m} (hm : 0 < m) (h : Contraction f) :
    ∃ (x : Fin m), FixedPoint f x ∧ ∀ (y : Fin m), FixedPoint f y → y = x := by
  have h_exists := contraction_fixed_point_exists hm h
  match h_exists with
  | ⟨x, hx⟩ =>
    refine' ⟨x, hx, _⟩
    intro y hy
    exact contraction_fixed_point_unique h y x hy hx

/-
### 真理 = 压缩映射不动点
-/

noncomputable def Truth {m : Nat} (f : Fin m → Fin m) (hm : 0 < m) (h : Contraction f) : Fin m :=
  Classical.choose (banach_fixed_point_theorem hm h)

theorem truth_is_fixed_point {m : Nat} (f : Fin m → Fin m) (hm : 0 < m) (h : Contraction f) :
    FixedPoint f (Truth f hm h) :=
  (Classical.choose_spec (banach_fixed_point_theorem hm h)).1

theorem truth_unique {m : Nat} (f : Fin m → Fin m) (hm : 0 < m) (h : Contraction f)
    (x : Fin m) (hx : FixedPoint f x) : x = Truth f hm h :=
  (Classical.choose_spec (banach_fixed_point_theorem hm h)).2 x hx

/-
### 迭代收敛到真理
-/

theorem iter_converges_geometric {m : Nat} {f : Fin m → Fin m}
    (k : Nat) (hk2 : k ≥ 2)
    (hk : ∀ (x y : Fin m), k * dist (f x) (f y) ≤ dist x y)
    (x0 : Fin m) (hx0 : FixedPoint f x0) (x : Fin m) (n : Nat) :
    k ^ n * dist (iter f n x) x0 ≤ dist x x0 := by
  have h2 : f x0 = x0 := hx0
  have h3 : ∀ n, iter f n x0 = x0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iter_succ, ih, h2]
      <;> rfl
  have h4 := contraction_iter_decay k hk2 hk n x x0
  rw [h3 n] at h4
  exact h4

end T4

end EAS
