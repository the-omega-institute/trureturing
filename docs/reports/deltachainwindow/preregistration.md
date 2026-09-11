# 矩形窗口 δ-链：预登记 v1

工作范围：源 quantum-reality 的
05c69f6fe7ff332e2d23220daf55e902cc52a7b9c46435ea2d3c722116d8df10 中公式 377.2。
这是用户指定的组合公式形式化，不是开放问题研究线，不宣称新数学。
377.1 与素数对数独立性不在范围内；不重证两处已冻结结果。

起点：b5c49d91bd，分支 lane/math/deltachainwindow。
产地：Codex implementation worker，lean4 skill，主循环直接实施、单点自查；
未派独立评审席。PR、独立评审与合并交回 orchestrator。

拟议落点：D5/S3/Arith/Lattices/RectangularDeltaChain。
generality: G；只 import Mathlib；Arith 已注册于 S3。
拟议 proof_shape: content；admission_basis: escape-witness。
拟议 escape_witness：按 δ 符号选择窗口角点，并证明该角点出发的每一步，
直到所有非零坐标整除商的最小值，仍在窗口内。
该构造须在最终最大长度定理的活推导路径上；逐坐标上界本身不作为见证。
若命中现成等价计数，先降级并另行预登记，不重证。

陈述回声：任意有限坐标型、自然数边长 L、整数步长 δ，显式假设
存在 p 使 δ(p)≠0。IsChain 用所有 m∈Fin n 与所有坐标的上下界定义。
交付须证明角点达到 M=1+min(L(p)/natAbs(δ(p)))，且任意链长度≤M；
将存在链与此界连成 iff 或 IsGreatest，不能只定义 M 再 rfl 展开。
零向量允许任意长度，将单独说明；不以 δ≠0 隐藏非零坐标假设。
utility: none：所有结果量化任意有限维度、任意边长与步长；没有固定实例、
有界枚举、检查器或依赖待履行数值前提的归约。枚举只作诊断。

检索收据：D5 查询 DeltaChain、delta.chain、δ.chain、longest.*chain、
rectangular.*window；未命中等价陈述。钉版 Mathlib 查 Finset.Ico、Nat.div、
格点与 arithmetic progression，找到 Nat.card_Ico、Nat.le_div_iff_mul_le、
Finset.inf' 的通用接口，未找到符号角点达到多坐标最小商的定理。
第三方能力实测：gh search code 与 Loogle HTTP 均成功。
GitHub 查询 arithmetic progression language:Lean，前20结果含 Mathlib、
dwrensha/compfiles、FLT 等；这是有界词面搜索，不宣称生态穷尽。
Loogle 返回 Nat.le_div_iff_mul_le 的精确类型，直接复用。

复算预期：完整范围 1≤k≤3、0≤L≤6、-3≤δ≤3、δ非全零，
组数为 Σ 7^k(7^k-1)=119700。对每组穷举所有起点，逐步移动直到出界，
最大点数应与主公式相同；去掉 min 的对照应出现不符。
用户提供 280/280 与 74/280，但该280组的选取规则未提供，不能声称精确重放。

停止判据：成=一般公式与构造全部 kernel 通过且完成规定门链；
翻=反例附 kernel 见证；否则 blocked，交付真实已证部分及最锐剩余命题。
构建使用 serial-lean，随后 lean-report、emit、deposit-uncovered；
CI Scribe 层另用精确 merge-base SHA 核验。每个编译单元及时提交。
