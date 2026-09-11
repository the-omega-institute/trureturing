# 偏迹与互信息修复：预登记 v1

产地：Codex implementation 席，使用 lean4 skill；本席直接实施并核验，零独立评审席。

question_answered：任意有限维联合 DensityState 的两个偏迹能否作为合法边缘态，
并使只接受联合态的量子互信息获得非定义展开的连接定理？

admission_basis: escape-witness

拟议 escape_witness：偏迹保半正定与保迹。拟用主子矩阵的半正定性和有限和，
以及乘积指标上的迹求和证明；此构造不是 VonNeumannEntropyPinching 的实例或投影。
具名消费者为 marginalLeft、marginalRight，以及 quantumMutualInformation。
第三级目标优先任意乘积态的互信息为零；先检索熵张量可加性及次可加性。
如其分析缺口不可闭合，交付已证保态与单参数定义，并精确记录剩余子命题，判 blocked。
不以公式展开、独立给定边缘或额外熵假设冒充该目标。

utility: none。所有拟议声明均为任意有限维矩阵/态的一般定理，
没有有界枚举、检查器、数值归约或已认证有限实例；其余用途字段不适用。

检索次序：D5 → 钉版 Mathlib → 可准入第三方 Lean 库 → 本地证明。
精确命中直接引用。新观察见证若偏离上述拟议，另写 v2 后再实施。
保持现有两个偏迹定义、加性与 Kronecker 公式；移除三独立参数 API 与 rfl 公式定理。

验收：serial-lean status=complete failed=0 → make lean-report 退出 0 且公理闭包合规
→ make emit → make deposit-uncovered；另跑精确 merge-base 的 scribe-content-checks。
每个可编译增量即时 commit。最终仅成、翻（kernel 反例）或 blocked。
