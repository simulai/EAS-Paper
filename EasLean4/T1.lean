import EasLean4.Axiom

namespace EAS

namespace T1

/--
T1 压缩定理 (Compression Theorem)

由于 d > 0，系统不可能完整复制环境，因此必须选择性地保留信息。
认知不是重建世界，而是压缩世界。

形式化：任何映射 f : E → R_S 必然非单射 → 必然丢失信息 → 压缩。
-/
theorem compression_inevitable
    {n m : Nat}
    (S : CognitiveSystem n m)
    (f : Fin m → Fin n) :
    ¬Injective f :=
  A1.noninjective S f

/--
T1 信息论解释：
  非单射 ⟺ 存在至少两个不同的环境状态被映射到同一个内部状态
  ⟺ 信息丢失 ⟺ 压缩

  这是 A1(a) 基数约束的直接推论。
-/
theorem information_loss_exists
    {n m : Nat}
    (S : CognitiveSystem n m)
    (f : Fin m → Fin n) :
    ∃ x y : Fin m, x ≠ y ∧ f x = f y :=
  A1.indistinguishable_pair S f

end T1

end EAS
