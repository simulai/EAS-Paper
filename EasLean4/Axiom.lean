import EasLean4.Basic

namespace EAS

namespace A1

/--
鸽巢原理（Pigeonhole Principle）

如果 m > n，则任何函数 f : Fin m → Fin n 都不是单射。
即：至少有两个不同的输入映射到同一个输出。

这是 A1(a) 的核心数学内容。
由 Basic.lean 中的构造性证明给出。
-/
theorem pigeonhole_principle {n m : Nat} (h : n < m) (f : Fin m → Fin n) :
    ¬Injective f :=
  pigeonholePrinciple m n h f

/--
A1(a) 基数约束层：
  由 S ⊂ E → |R_S| < |E|
  → 任何映射 f : E → R_S 必然非单射（鸽巢原理）
-/
theorem noninjective {n m : Nat} (S : CognitiveSystem n m) (f : Fin m → Fin n) :
    ¬Injective f :=
  pigeonhole_principle S.card_constraint f

/--
A1(a) 直接推论：存在不可区分的状态对
  即 ∃ x y : E, x ≠ y ∧ f x = f y
-/
theorem indistinguishable_pair {n m : Nat} (S : CognitiveSystem n m)
    (f : Fin m → Fin n) :
    ∃ x y : Fin m, x ≠ y ∧ f x = f y := by
  have h_noninj := noninjective S f
  have h : ∃ x y : Fin m, f x = f y ∧ x ≠ y := by
    simpa [Injective] using h_noninj
  rcases h with ⟨x, y, h_eq, h_ne⟩
  exact ⟨x, y, h_ne, h_eq⟩

/--
A1(b) 动力学同构不可能层：
  不存在双射 f : R_S → E 使得 f ∘ T_R = T_E ∘ f
  即不存在动力系统意义上的同构 R_S ≃ E

  注意：完整的形式化需要将"物理嵌入"和"自指"形式化，
  这涉及停机问题的对角化论证。
  当前版本作为公理接受。
-/
axiom no_dynamical_isomorphism {n m : Nat} (S : CognitiveSystem n m) :
    ¬∃ (f : Fin n → Fin m), Bijective f ∧
      (∀ x : Fin n, f (S.T_R x) = S.T_E (f x))

/--
A1 完整陈述：
  (a) 任何映射 f : E → R_S 必然非单射
  (b) 不存在动力学同构 R_S ≃ E
-/
theorem finitude {n m : Nat} (S : CognitiveSystem n m) :
    (∀ f : Fin m → Fin n, ¬Injective f) ∧
    (¬∃ (f : Fin n → Fin m), Bijective f ∧
      (∀ x : Fin n, f (S.T_R x) = S.T_E (f x))) := by
  constructor
  · exact fun f => noninjective S f
  · exact no_dynamical_isomorphism S

end A1

end EAS
