import EasLean4.Basic

namespace EAS

namespace T2

/-
## T2 概念定理 (Concept Theorem)

迭代区分操作在有限系统上必然收敛到不动点。
-/

/-- 迭代区分操作的第 n 代 -/
def iterateDistinction {E : Type _} (T : E → E) (rel : E → E → Prop) :
    Nat → (E → E → Prop)
  | 0 => rel
  | n + 1 => fun x y => iterateDistinction T rel n x y ∧ iterateDistinction T rel n (T x) (T y)

/-- 迭代区分是单调递减的（越迭代越细） -/
theorem iterateDistinction_mono {E : Type _} (T : E → E) (rel : E → E → Prop) (n : Nat) :
    ∀ x y, iterateDistinction T rel (n + 1) x y → iterateDistinction T rel n x y := by
  intro x y h
  exact h.1

/-- 迭代区分的传递单调性：k ≥ n → 第 k 代蕴含第 n 代 -/
theorem iterateDistinction_mono_trans {E : Type _} (T : E → E) (rel : E → E → Prop) :
    ∀ (n k : Nat), n ≤ k → ∀ x y, iterateDistinction T rel k x y → iterateDistinction T rel n x y := by
  intro n k hnk
  induction k with
  | zero =>
    have h1 : n = 0 := Nat.eq_zero_of_le_zero hnk
    intro x y h
    subst h1
    exact h
  | succ k ih =>
    intro x y h
    match Nat.lt_or_eq_of_le hnk with
    | Or.inl h2 =>
      have h3 : n ≤ k := Nat.le_of_lt_succ h2
      have h4 := iterateDistinction_mono T rel k x y h
      exact ih h3 x y h4
    | Or.inr h2 =>
      have h5 : n = k + 1 := h2
      subst h5
      exact h

/-
### 辅助引理
-/

/-- 对 Fin m，¬(∀ x, P x) → ∃ x, ¬P x -/
theorem fin_not_forall_exists_not {m : Nat} {P : Fin m → Prop} :
    ¬(∀ x : Fin m, P x) → ∃ x : Fin m, ¬P x := by
  intro h
  induction m with
  | zero =>
    have h1 : ∀ x : Fin 0, P x := by
      intro x
      exact Fin.elim0 x
    exact False.elim (h h1)
  | succ m ih =>
    match Classical.em (P 0) with
    | Or.inl h0 =>
      have h1 : ¬(∀ x : Fin m, P x.succ) := by
        intro h2
        have h3 : ∀ x : Fin (m + 1), P x := by
          intro x
          exact Fin.cases h0 (fun x => h2 x) x
        exact h h3
      match ih h1 with
      | ⟨x, hx⟩ =>
        exact ⟨x.succ, hx⟩
    | Or.inr h0 =>
      exact ⟨0, h0⟩

/-- 对 Fin m，¬(∀ x y, P x y) → ∃ x y, ¬P x y -/
theorem fin_not_forall2_exists_not {m : Nat} {P : Fin m → Fin m → Prop} :
    ¬(∀ x y : Fin m, P x y) → ∃ x y : Fin m, ¬P x y := by
  intro h
  have h1 : ∃ x : Fin m, ¬(∀ y : Fin m, P x y) :=
    fin_not_forall_exists_not (P := fun x => ∀ y : Fin m, P x y) h
  match h1 with
  | ⟨x, h2⟩ =>
    have h3 : ∃ y : Fin m, ¬P x y := fin_not_forall_exists_not (P := fun y => P x y) h2
    match h3 with
    | ⟨y, h4⟩ =>
      exact ⟨x, y, h4⟩

/-
### 有限乘积编码
-/

def pairEncode {m : Nat} : Fin m × Fin m → Fin (m * m) :=
  fun p =>
    let i := p.1.val
    let j := p.2.val
    have h : i * m + j < m * m := by
      have h1 : i < m := p.1.isLt
      have h2 : j < m := p.2.isLt
      have h3 : i * m + j < i * m + m := Nat.add_lt_add_left h2 (i * m)
      have h4 : i * m + m = (i + 1) * m := by
        have h5 : i * m + m = m * i + m := by rw [Nat.mul_comm i m]
        have h6 : m * i + m = m * (i + 1) := by
          have h7 : m * (i + 1) = m * i + m * 1 := Nat.mul_add m i 1
          have h8 : m * 1 = m := Nat.mul_one m
          rw [h7, h8]
        have h9 : (i + 1) * m = m * (i + 1) := Nat.mul_comm (i + 1) m
        rw [h5, h6, h9]
      have h10 : i + 1 ≤ m := Nat.succ_le_of_lt h1
      have h11 : (i + 1) * m ≤ m * m := Nat.mul_le_mul_right m h10
      rw [h4] at h3
      exact Nat.lt_of_lt_of_le h3 h11
    ⟨i * m + j, h⟩

theorem pairEncode_inj {m : Nat} : Injective (@pairEncode m) := by
  intro p1 p2 h_eq
  let x1 := p1.1
  let y1 := p1.2
  let x2 := p2.1
  let y2 := p2.2
  have h1 : x1.val * m + y1.val = x2.val * m + y2.val := Fin.val_eq_of_eq h_eq
  have hx : x1.val = x2.val := by
    match Nat.lt_trichotomy x1.val x2.val with
    | Or.inl h_lt =>
      have h4 : x1.val + 1 ≤ x2.val := Nat.succ_le_of_lt h_lt
      have h5 : x1.val * m + y1.val < x2.val * m := by
        have h6 : x1.val * m + y1.val < x1.val * m + m := Nat.add_lt_add_left y1.isLt (x1.val * m)
        have h7 : x1.val * m + m = (x1.val + 1) * m := by
          have h8 : x1.val * m + m = m * x1.val + m := by rw [Nat.mul_comm x1.val m]
          have h9 : m * x1.val + m = m * (x1.val + 1) := by
            have h10 : m * (x1.val + 1) = m * x1.val + m * 1 := Nat.mul_add m x1.val 1
            have h11 : m * 1 = m := Nat.mul_one m
            rw [h10, h11]
          have h12 : (x1.val + 1) * m = m * (x1.val + 1) := Nat.mul_comm (x1.val + 1) m
          rw [h8, h9, h12]
        have h13 : (x1.val + 1) * m ≤ x2.val * m := Nat.mul_le_mul_right m h4
        have h14 : x1.val * m + m ≤ x2.val * m := by
          rw [h7]
          exact h13
        exact Nat.lt_of_lt_of_le h6 h14
      have h15 : x2.val * m + y2.val < x2.val * m := by
        have h16 : x1.val * m + y1.val = x2.val * m + y2.val := h1
        rw [h16] at h5
        exact h5
      have h17 : y2.val < 0 := Nat.lt_of_add_lt_add_left h15
      have h18 : 0 ≤ y2.val := Nat.zero_le y2.val
      exact False.elim (Nat.not_lt_zero y2.val h17)
    | Or.inr (Or.inl h_eq2) => exact h_eq2
    | Or.inr (Or.inr h_gt) =>
      have h4 : x2.val + 1 ≤ x1.val := Nat.succ_le_of_lt h_gt
      have h5 : x2.val * m + y2.val < x1.val * m := by
        have h6 : x2.val * m + y2.val < x2.val * m + m := Nat.add_lt_add_left y2.isLt (x2.val * m)
        have h7 : x2.val * m + m = (x2.val + 1) * m := by
          have h8 : x2.val * m + m = m * x2.val + m := by rw [Nat.mul_comm x2.val m]
          have h9 : m * x2.val + m = m * (x2.val + 1) := by
            have h10 : m * (x2.val + 1) = m * x2.val + m * 1 := Nat.mul_add m x2.val 1
            have h11 : m * 1 = m := Nat.mul_one m
            rw [h10, h11]
          have h12 : (x2.val + 1) * m = m * (x2.val + 1) := Nat.mul_comm (x2.val + 1) m
          rw [h8, h9, h12]
        have h13 : (x2.val + 1) * m ≤ x1.val * m := Nat.mul_le_mul_right m h4
        have h14 : x2.val * m + m ≤ x1.val * m := by
          rw [h7]
          exact h13
        exact Nat.lt_of_lt_of_le h6 h14
      have h15 : x1.val * m + y1.val < x1.val * m := by
        have h16 : x1.val * m + y1.val = x2.val * m + y2.val := h1
        rw [h16]
        exact h5
      have h17 : y1.val < 0 := Nat.lt_of_add_lt_add_left h15
      have h18 : 0 ≤ y1.val := Nat.zero_le y1.val
      exact False.elim (Nat.not_lt_zero y1.val h17)
  have hy : y1.val = y2.val := by
    rw [hx] at h1
    exact Nat.add_left_cancel h1
  have hx' : x1 = x2 := Fin.ext hx
  have hy' : y1 = y2 := Fin.ext hy
  exact Prod.ext hx' hy'

/-
### 收敛性证明
-/

/-- 辅助引理：如果前 N 步都没收敛，那么存在 N 个不同的"见证对" -/
theorem strict_mono_gives_distinct_pairs {m : Nat} (T : Fin m → Fin m) (rel : Fin m → Fin m → Prop) (N : Nat)
    (h_strict : ∀ n < N, ∃ (p : Fin m × Fin m),
      iterateDistinction T rel n p.1 p.2 ∧ ¬iterateDistinction T rel (n + 1) p.1 p.2) :
    ∃ (f : Fin N → Fin m × Fin m), Injective f := by
  have h1 : ∀ n : Nat, n < N → ∃ (p : Fin m × Fin m),
      iterateDistinction T rel n p.1 p.2 ∧ ¬iterateDistinction T rel (n + 1) p.1 p.2 := by
    intro n hn
    exact h_strict n hn
  let choose_p : ∀ n : Nat, n < N → (Fin m × Fin m) := fun n hn => Classical.choose (h1 n hn)
  have choose_prop : ∀ (n : Nat) (hn : n < N),
      iterateDistinction T rel n (choose_p n hn).1 (choose_p n hn).2 ∧
      ¬iterateDistinction T rel (n + 1) (choose_p n hn).1 (choose_p n hn).2 := by
    intro n hn
    exact Classical.choose_spec (h1 n hn)
  let f : Fin N → Fin m × Fin m := fun i => choose_p i.val i.isLt
  have h_f_inj : Injective f := by
    intro i1 i2 h_eq
    have h_main : i1.val = i2.val := by
      match Nat.lt_trichotomy i1.val i2.val with
      | Or.inl h12 =>
        have h2 : i1.val < i2.val := h12
        have h3 : i1.val + 1 ≤ i2.val := Nat.succ_le_of_lt h2
        have h4 : ∀ x y, iterateDistinction T rel i2.val x y → iterateDistinction T rel (i1.val + 1) x y :=
          iterateDistinction_mono_trans T rel (i1.val + 1) i2.val h3
        have h5 : ¬iterateDistinction T rel (i1.val + 1) (f i1).1 (f i1).2 :=
          (choose_prop i1.val i1.isLt).2
        have h6 : iterateDistinction T rel i2.val (f i2).1 (f i2).2 :=
          (choose_prop i2.val i2.isLt).1
        have h7 : f i1 = f i2 := h_eq
        have h8 : (f i1).1 = (f i2).1 := by
          rw [h7]
        have h9 : (f i1).2 = (f i2).2 := by
          rw [h7]
        have h10 : iterateDistinction T rel i2.val (f i1).1 (f i1).2 := by
          rw [h8, h9]
          exact h6
        have h11 : iterateDistinction T rel (i1.val + 1) (f i1).1 (f i1).2 := h4 (f i1).1 (f i1).2 h10
        exact False.elim (h5 h11)
      | Or.inr (Or.inl h_eq2) => exact h_eq2
      | Or.inr (Or.inr h21) =>
        have h2 : i2.val < i1.val := h21
        have h3 : i2.val + 1 ≤ i1.val := Nat.succ_le_of_lt h2
        have h4 : ∀ x y, iterateDistinction T rel i1.val x y → iterateDistinction T rel (i2.val + 1) x y :=
          iterateDistinction_mono_trans T rel (i2.val + 1) i1.val h3
        have h5 : ¬iterateDistinction T rel (i2.val + 1) (f i2).1 (f i2).2 :=
          (choose_prop i2.val i2.isLt).2
        have h6 : iterateDistinction T rel i1.val (f i1).1 (f i1).2 :=
          (choose_prop i1.val i1.isLt).1
        have h7 : f i1 = f i2 := h_eq
        have h8 : (f i1).1 = (f i2).1 := by
          rw [h7]
        have h9 : (f i1).2 = (f i2).2 := by
          rw [h7]
        have h10 : iterateDistinction T rel i1.val (f i2).1 (f i2).2 := by
          rw [←h8, ←h9]
          exact h6
        have h11 : iterateDistinction T rel (i2.val + 1) (f i2).1 (f i2).2 := h4 (f i2).1 (f i2).2 h10
        exact False.elim (h5 h11)
    exact Fin.ext h_main
  exact ⟨f, h_f_inj⟩

/-- T2 概念定理：迭代区分操作必然在有限步内收敛 -/
theorem concept_convergence {m : Nat} (T : Fin m → Fin m) (rel : Fin m → Fin m → Prop) :
    ∃ N : Nat, ∀ n ≥ N, ∀ x y,
      iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y := by
  have h_main : ∃ N : Nat, ∀ x y,
      iterateDistinction T rel (N + 1) x y ↔ iterateDistinction T rel N x y := by
    match Classical.em (∃ N : Nat, ∀ x y, iterateDistinction T rel (N + 1) x y ↔ iterateDistinction T rel N x y) with
    | Or.inl h => exact h
    | Or.inr h =>
      have h1 : ∀ n : Nat, ¬(∀ x y, iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y) := by
        intro n
        intro h2
        have h3 : ∃ N : Nat, ∀ x y, iterateDistinction T rel (N + 1) x y ↔ iterateDistinction T rel N x y :=
          ⟨n, h2⟩
        exact h h3
      have h2 : ∀ n : Nat, ∃ (p : Fin m × Fin m),
          iterateDistinction T rel n p.1 p.2 ∧ ¬iterateDistinction T rel (n + 1) p.1 p.2 := by
        intro n
        have h3 : ¬(∀ x y, iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y) := h1 n
        have h4 : ∃ x y : Fin m, ¬(iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y) :=
          fin_not_forall2_exists_not (P := fun x y => iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y) h3
        match h4 with
        | ⟨x, y, h5⟩ =>
          have h6 : ∀ x y, iterateDistinction T rel (n + 1) x y → iterateDistinction T rel n x y :=
            iterateDistinction_mono T rel n
          have h7 : iterateDistinction T rel n x y ∧ ¬iterateDistinction T rel (n + 1) x y := by
            match Classical.em (iterateDistinction T rel n x y) with
            | Or.inl h8 =>
              have h9 : ¬iterateDistinction T rel (n + 1) x y := by
                intro h10
                have h11 : (iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y) := by
                  constructor
                  · intro h12
                    exact h6 x y h12
                  · intro _
                    exact h10
                exact h5 h11
              exact ⟨h8, h9⟩
            | Or.inr h8 =>
              have h9 : ¬iterateDistinction T rel (n + 1) x y := by
                intro h10
                exact h8 (h6 x y h10)
              have h10 : (iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y) := by
                constructor
                · intro h11
                  exact h6 x y h11
                · intro h11
                  exact False.elim (h8 h11)
              exact False.elim (h5 h10)
          exact ⟨(x, y), h7⟩
      let N := m * m + 1
      have h_strict : ∀ n < N, ∃ (p : Fin m × Fin m),
          iterateDistinction T rel n p.1 p.2 ∧ ¬iterateDistinction T rel (n + 1) p.1 p.2 := by
        intro n _
        exact h2 n
      have h_exists_inj : ∃ (f : Fin N → Fin m × Fin m), Injective f :=
        strict_mono_gives_distinct_pairs T rel N h_strict
      match h_exists_inj with
      | ⟨f, hf_inj⟩ =>
        let g : Fin N → Fin (m * m) := fun i => pairEncode (f i)
        have hg_inj : Injective g := by
          intro i1 i2 h_eq
          have h1 : pairEncode (f i1) = pairEncode (f i2) := h_eq
          have h2 : f i1 = f i2 := pairEncode_inj (f i1) (f i2) h1
          exact hf_inj i1 i2 h2
        have h_lt : m * m < N := by
          have h9 : N = m * m + 1 := by rfl
          rw [h9]
          exact Nat.lt_succ_self (m * m)
        have h_contra : ¬Injective g := pigeonholePrinciple N (m * m) h_lt g
        exact False.elim (h_contra hg_inj)
  match h_main with
  | ⟨N, hN⟩ =>
    have h_step : ∀ k : Nat, ∀ x y,
        iterateDistinction T rel (N + k + 1) x y ↔ iterateDistinction T rel (N + k) x y := by
      intro k
      induction k with
      | zero =>
        intro x y
        have h1 : N + 0 + 1 = N + 1 := by simp
        rw [h1]
        exact hN x y
      | succ k ih =>
        intro x y
        have h_ih' : ∀ x y, iterateDistinction T rel (N + k + 1) x y ↔ iterateDistinction T rel (N + k) x y := ih
        have h_def1 : iterateDistinction T rel (N + (k + 1) + 1) x y =
            (iterateDistinction T rel (N + k + 1) x y ∧ iterateDistinction T rel (N + k + 1) (T x) (T y)) := by
          have h_eq : N + (k + 1) + 1 = (N + k + 1) + 1 := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [h_eq]
          <;> rfl
        have h_def2 : iterateDistinction T rel (N + (k + 1)) x y =
            (iterateDistinction T rel (N + k) x y ∧ iterateDistinction T rel (N + k) (T x) (T y)) := by
          have h_eq : N + (k + 1) = (N + k) + 1 := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [h_eq]
          <;> rfl
        rw [h_def1, h_def2]
        have h1 : iterateDistinction T rel (N + k + 1) x y ↔ iterateDistinction T rel (N + k) x y := h_ih' x y
        have h2 : iterateDistinction T rel (N + k + 1) (T x) (T y) ↔ iterateDistinction T rel (N + k) (T x) (T y) := h_ih' (T x) (T y)
        constructor
        · intro h
          exact ⟨h1.mp h.1, h2.mp h.2⟩
        · intro h
          exact ⟨h1.mpr h.1, h2.mpr h.2⟩
    refine' ⟨N, _⟩
    intro n hn
    have h4 : ∃ k : Nat, n = N + k := by
      refine' ⟨n - N, _⟩
      have h5 : N + (n - N) = n := Nat.add_sub_of_le hn
      exact Eq.symm h5
    match h4 with
    | ⟨k, hk⟩ =>
      rw [hk]
      exact h_step k

/-- 概念 = 迭代区分的不动点 -/
def Concept {m : Nat} (T : Fin m → Fin m) (rel : Fin m → Fin m → Prop) :
    Fin m → Fin m → Prop :=
  let N := Classical.choose (concept_convergence T rel)
  iterateDistinction T rel N

/-- 概念是迭代区分的不动点 -/
theorem concept_is_fixedpoint {m : Nat} (T : Fin m → Fin m) (rel : Fin m → Fin m → Prop) :
    ∀ x y, iterateDistinction T (Concept T rel) 1 x y ↔ Concept T rel x y := by
  have hN_spec := Classical.choose_spec (concept_convergence T rel)
  let N := Classical.choose (concept_convergence T rel)
  have hN : ∀ n ≥ N, ∀ x y, iterateDistinction T rel (n + 1) x y ↔ iterateDistinction T rel n x y := hN_spec
  have h1 : Concept T rel = iterateDistinction T rel N := by rfl
  have h2 : N ≥ N := Nat.le_refl N
  have h3 : ∀ x y, iterateDistinction T rel (N + 1) x y ↔ iterateDistinction T rel N x y := hN N h2
  intro x y
  have h4 : iterateDistinction T (Concept T rel) 1 x y = iterateDistinction T rel (N + 1) x y := by
    rw [h1] <;> rfl
  rw [h4]
  exact h3 x y

end T2

end EAS
