import EasLean4.Axiom

namespace EAS

namespace T0

/--
T0 区分必然性定理

在 A1(a) 成立的条件下，任何非退化的有限认知系统
必然执行区分操作。即：A1 ⟹ 区分必然涌现。

非退化条件：f 不是常值映射（否则系统退化为无认知的死物）

核心表述：认知 = 对世界做商映射 (Knowledge = Quotienting the World)
-/
theorem distinction_inevitable
    {n m : Nat}
    (S : CognitiveSystem n m)
    (f : Fin m → Fin n)
    (h_nontrivial : ¬(∃ c : Fin n, ∀ x : Fin m, f x = c)) :
    ∃ (rel : Fin m → Fin m → Prop),
      (∀ x, rel x x) ∧
      (∀ x y, rel x y → rel y x) ∧
      (∀ x y z, rel x y → rel y z → rel x z) ∧
      (∃ x y : Fin m, x ≠ y ∧ rel x y) ∧
      (∃ x y : Fin m, ¬rel x y) ∧
      (∀ x y, rel x y ↔ f x = f y) := by
  have h_pos : 0 < m := by
    have h : n < m := S.card_constraint
    omega
  let x₀ : Fin m := ⟨0, h_pos⟩
  let p := ∃ (x y : Fin m), ¬(f x = f y)
  have h_em : p ∨ ¬p := Classical.em p
  have h_notp_imp : ¬p → ∀ (x y : Fin m), f x = f y :=
    fun h_notp x y =>
      if h : f x = f y then h
      else False.elim (h_notp ⟨x, y, h⟩)
  have h_main : p → (∃ (rel : Fin m → Fin m → Prop),
        (∀ x, rel x x) ∧
        (∀ x y, rel x y → rel y x) ∧
        (∀ x y z, rel x y → rel y z → rel x z) ∧
        (∃ x y : Fin m, x ≠ y ∧ rel x y) ∧
        (∃ x y : Fin m, ¬rel x y) ∧
        (∀ x y, rel x y ↔ f x = f y)) :=
    fun h_exists_separate =>
      have h1 : ∃ (x y : Fin m), ¬(InducedEquivalence f x y) :=
        match h_exists_separate with
        | ⟨x, y, h_ne⟩ => ⟨x, y, h_ne⟩
      have h_exists_merge : ∃ x y : Fin m, x ≠ y ∧ InducedEquivalence f x y :=
        A1.indistinguishable_pair S f
      ⟨InducedEquivalence f,
        InducedEquivalence.refl f,
        fun {x y} h => InducedEquivalence.symm f h,
        fun {x y z} h1 h2 => InducedEquivalence.trans f h1 h2,
        h_exists_merge,
        h1,
        fun x y => Iff.rfl⟩
  have h_contra : (∀ (x y : Fin m), f x = f y) → False :=
    fun h_all_eq =>
      have h_const : ∃ c : Fin n, ∀ x : Fin m, f x = c :=
        ⟨f x₀, fun x => h_all_eq x x₀⟩
      h_nontrivial h_const
  have h_final : ∃ (rel : Fin m → Fin m → Prop),
        (∀ x, rel x x) ∧
        (∀ x y, rel x y → rel y x) ∧
        (∀ x y z, rel x y → rel y z → rel x z) ∧
        (∃ x y : Fin m, x ≠ y ∧ rel x y) ∧
        (∃ x y : Fin m, ¬rel x y) ∧
        (∀ x y, rel x y ↔ f x = f y) := by
    exact Or.elim h_em
      (fun hp => h_main hp)
      (fun hnp => False.elim (h_contra (h_notp_imp hnp)))
  exact h_final

/--
T0.1 Rosen 封闭性约束

即使 |R_S| = |E|（等势），只要动力学同构不可能，
区分仍然必然涌现。

证明思路：
  若 f 是动力学同态且不是双射，则：
  - 若 f 不是单射 → 多对一 → 区分
  - 若 f 不是满射 → 存在 E 中状态无法被表征 → 区分
-/
theorem rosen_constraint
    {n m : Nat}
    (T_R : Fin n → Fin n)
    (T_E : Fin m → Fin m)
    (h_no_iso : ¬∃ (f : Fin n → Fin m), Bijective f ∧
      (∀ x : Fin n, f (T_R x) = T_E (f x))) :
    ∀ (f : Fin m → Fin n),
      (∀ x, f (T_E x) = T_R (f x)) →
      ¬Bijective f →
      (¬Injective f ∨ ¬Surjective f) := by
  intro f _ h_not_bij
  have h : ¬(Injective f ∧ Surjective f) := by
    intro h'
    exact h_not_bij h'
  by_cases h_inj : Injective f
  · -- 如果是单射，则不是满射
    have h_not_surj : ¬Surjective f := by
      intro h_surj
      exact h ⟨h_inj, h_surj⟩
    exact Or.inr h_not_surj
  · -- 如果不是单射
    exact Or.inl h_inj

/--
动力学稳定性引理：
  若 f 是动力学同态（f ∘ T_E = T_R ∘ f），
  则等价关系 ~_f 在动力学下封闭。

  即：若 x ~_f y，则 T_E(x) ~_f T_E(y)
  这保证了概念（稳定等价类）在时间演化下保持稳定。
-/
theorem dynamical_stability
    {n m : Nat}
    (S : CognitiveSystem n m)
    (f : Fin m → Fin n)
    (h_hom : ∀ x, f (S.T_E x) = S.T_R (f x)) :
    ∀ x y : Fin m,
      InducedEquivalence f x y →
      InducedEquivalence f (S.T_E x) (S.T_E y) := by
  intro x y h_eq
  have h1 : f x = f y := h_eq
  have h2 : f (S.T_E x) = S.T_R (f x) := h_hom x
  have h3 : f (S.T_E y) = S.T_R (f y) := h_hom y
  have h4 : f (S.T_E x) = f (S.T_E y) := by
    calc
      f (S.T_E x) = S.T_R (f x) := h2
      _ = S.T_R (f y) := by rw [h1]
      _ = f (S.T_E y) := h3.symm
  exact h4

end T0

end EAS
