# 原输入信息的内外平衡：预登记

源：`quantum-reality` atom
`1a71353ff4dfdc935a0206eb30fa29832f961bb7548537ca4530dcfb91c0409f`。
问题：同一个纯三体态的实际约化态是否满足
`I(A:R) + I(A:B) = 2 S(A)`。

- proposed admission_basis: `escape-witness`
- proposed escape_witness: 任意有限维纯二体态的两个互补边缘具有相等的
  von Neumann 熵；先查 D5、钉版 mathlib、可准入的第三方 Lean 库，再决定是否自证。
- proposed proof_shape: 互补熵引理须逐项判形；恒等式在取得该引理后为算术绑定。
  三体索引重排、约化态构造和一致性等式属于类型/API 工作，单独计入，
  不将它们冒称为互补熵的数学证明。
- 若互补熵已有精确上游声明，则降级为 `rule-11-upstream-wrapper`；若仓内已覆盖，
  直接复用并说明是否仍有合法落地依据，不重复证明。
- 具名消费者：拟议 `InputInformationBalance.input_information_balance`，其输入须是
  一个纯三体态；不能用彼此无约束的三个状态或直接假设目标熵等式代替。
- computational_content.kind: `none`（目标为任意有限维状态的一般恒等式，
  数值实验只作探针，不作为有限实例交付）。
- 数值判据：固定随机种子，三组维数各 50 个纯态；残差阈值 `1e-10`。
  另取 80 个纯态将右端改成 `S(A)`，预期全部失败。
- 成：完整目标通过串行构建、lean-report、emit、deposit-uncovered，
  公理闭包无 sorryAx 或私有公理；翻：提供 kernel 反例；
  blocked：只提交已经证明且连接到目标的部分，列明检索范围、失败路线与最锐剩余命题。
- 构建入口：`bash tools/scripts/agent/serial-lean.sh /Users/chronoai/trureturing-quantumobs2`。

产地：Codex 实施席，使用 lean4 技能；当前为单席检索、实施与自查，
不声称独立评审或多模型共识。文献中该恒等式已知；本任务是源 atom 的形式化，
不是开放问题新发现。
