import EasLean4.Basic

namespace EAS

namespace T3

/-
## T3 规律定理 (Law Theorem)

直观：规律 = 在变换群作用下保持不变的区分操作。
-/

/-
### 群结构（最小版本）
-/

/-- 群结构 -/
class Group (G : Type _) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_left_inv : ∀ a : G, mul (inv a) a = one

/-- 群作用 -/
class GroupAction (G E : Type _) [Group G] where
  act : G → E → E
  one_act : ∀ x : E, act (Group.one) x = x
  mul_act : ∀ (g h : G) (x : E), act (Group.mul g h) x = act g (act h x)

infixl:70 " • " => GroupAction.act

/-
### 不变区分
-/

/-- 区分关系 rel 在群 G 作用下不变 -/
def InvariantDistinction (G E : Type _) [Group G] [GroupAction G E]
    (rel : E → E → Prop) : Prop :=
  ∀ (g : G) (x y : E), rel x y ↔ rel (g • x) (g • y)

/-
### T3 规律定理
-/

/-- 规律定理：若区分是 G-不变的，则群作用保持等价类 -/
theorem law_theorem (G E : Type _) [Group G] [GroupAction G E]
    (rel : E → E → Prop) (h_invar : InvariantDistinction G E rel) :
    ∀ (g : G) (x y : E), rel x y → rel (g • x) (g • y) := by
  intro g x y h
  have h1 : rel x y ↔ rel (g • x) (g • y) := h_invar g x y
  exact h1.mp h

/-- 逆作用也保持等价类 -/
theorem inv_law_theorem (G E : Type _) [Group G] [GroupAction G E]
    (rel : E → E → Prop) (h_invar : InvariantDistinction G E rel) :
    ∀ (g : G) (x y : E), rel (g • x) (g • y) → rel x y := by
  intro g x y h
  have h1 : rel (g • x) (g • y) ↔ rel x y := (h_invar g x y).symm
  exact h1.mp h

/-
### 时间平移版本（Noether 定理的认识论版本）

如果区分关系在动力学 T 下不变，那么它在所有时间步下都不变。
这就是"守恒量"的认识论起源。
-/

/-- 自然数迭代作用：T^n(x) -/
def natAction {E : Type _} (T : E → E) : Nat → E → E
  | 0, x => x
  | n + 1, x => T (natAction T n x)

/-- natAction 的加法性质 -/
theorem natAction_add {E : Type _} (T : E → E) (m n : Nat) (x : E) :
    natAction T (m + n) x = natAction T m (natAction T n x) := by
  induction m with
  | zero =>
    have h1 : natAction T (0 + n) x = natAction T n x := by
      have h2 : 0 + n = n := by omega
      rw [h2]
      <;> rfl
    have h3 : natAction T 0 (natAction T n x) = natAction T n x := by rfl
    rw [h1, h3]
  | succ m ih =>
    have h1 : natAction T (m + 1 + n) x = T (natAction T (m + n) x) := by
      have h2 : m + 1 + n = (m + n) + 1 := by omega
      rw [h2]
      <;> rfl
    have h4 : natAction T (m + 1) (natAction T n x) = T (natAction T m (natAction T n x)) := by
      rfl
    rw [h1, h4]
    rw [ih]

/-- T-不变 = 在单步时间平移下不变 -/
def TInvariant {E : Type _} (T : E → E) (rel : E → E → Prop) : Prop :=
  ∀ x y : E, rel x y ↔ rel (T x) (T y)

/-- T-不变 → 在所有时间步下都不变 -/
theorem TInvariant_all_steps {E : Type _} (T : E → E) (rel : E → E → Prop)
    (h : TInvariant T rel) :
    ∀ (n : Nat) (x y : E), rel x y ↔ rel (natAction T n x) (natAction T n y) := by
  intro n
  induction n with
  | zero =>
    intro x y
    exact Iff.rfl
  | succ n ih =>
    intro x y
    have h1 : rel x y ↔ rel (natAction T n x) (natAction T n y) := ih x y
    have h2 : rel (natAction T n x) (natAction T n y) ↔ rel (T (natAction T n x)) (T (natAction T n y)) :=
      h (natAction T n x) (natAction T n y)
    have h3 : rel x y ↔ rel (T (natAction T n x)) (T (natAction T n y)) :=
      Iff.trans h1 h2
    have h4 : natAction T (n + 1) x = T (natAction T n x) := rfl
    have h5 : natAction T (n + 1) y = T (natAction T n y) := rfl
    rw [h4, h5]
    exact h3

end T3

end EAS
