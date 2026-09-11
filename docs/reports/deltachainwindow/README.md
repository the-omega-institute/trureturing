# 矩形指数窗口内最长 δ-链

本席终局：**成**。一般公式、显式达到构造及规定本地门链均通过，仅处理 377.2。
这表示实施席目标达成，不表示 PR 已合入；PR 与合并交回 orchestrator。
实施者为 Codex worker，使用 lean4 skill，单点自查、零独立评审席。
本报告是席位亲验，不冒充 orchestrator 的复验或共识。

## 形式化与忠实性

模块 `D5/S3/Arith/Lattices/RectangularDeltaChain.lean`，generality G。
`IsChain L δ a n` 是可判定的谓词：对每个 m∈Fin n 与坐标 p，
要求 0≤a(p)+mδ(p)≤L(p)。L 取自然数，δ 与起点取整数；坐标型任意有限。
`active` 只收 δ(p)≠0 的坐标，`stepLimit` 是这个非空集合上的有限最小商。
最大点数定理显式带 `hδ : ∃ p, δ p ≠ 0`。

`longest_chain_length` 断言 **IsGreatest {n | ∃ a, IsChain L δ a n}
(1+stepLimit L δ hδ)**，同时包含达到与上界，绝非定义体的 rfl 展开。
`exists_chain_iff` 进一步给出所有且仅有 n≤M 的长度可实现。
下界起点 `corner` 逐坐标取 L(p) 当 δ(p)<0，其余取0。
对零步长坐标自然有零位移；非零坐标的 m≤min⌊L/|δ|⌋ 保证 m|δ(p)|≤L(p)。
`corner_coordinate` 分正负方向证明完整上下界，供 `corner_chain` 使用。
上界从任意起点链的首末点推出 (n−1)|δ(p)|≤L(p)，再逐坐标取最小值。
δ 非零时不同序号对应不同点，因为一个非零坐标上的整数乘法可消去；
此消去事实没有另设公开定理。零向量结论按用户定义讨论序列长度，允许重复点。

377.1 不在本证明的 import 或依赖闭包中；没有改写或重证素数对数独立性。

## 判形与准入

admission_basis: escape-witness；与预登记 v1 一致。
直接冻结依赖：全部公开定理均为空（GID/statement_id 无条目），只依赖 Mathlib。
以下名字均以 `D5/S3/Arith/Lattices/RectangularDeltaChain.` 为 GID 前缀。

| 公开定理 | proof_shape | escape_witness / 伴随义务 |
| --- | --- | --- |
| chain_length_le_coordinate | bind-only | 首末点算术上界；不单独当见证 |
| chain_length_le | bind-only | 汇合逐坐标上界；不单独当见证 |
| corner_chain | content | 显式符号角点与 corner_coordinate 的区间保持构造 |
| exists_chain_iff | content | corner_chain 的初段构造实现每个 n≤M |
| longest_chain_length | content | corner_chain 供给 IsGreatest 的成员见证 |
| zero_direction_unbounded | bind-only | 预登记的零向量边界义务；零起点直接化简 |

伴随的有向边（消费者→前置）：
longest_chain_length→chain_length_le→chain_length_le_coordinate；
exists_chain_iff→chain_length_le，且它与 longest_chain_length 都→corner_chain。
零向量边界义务（预登记 v1 的陈述回声）→zero_direction_unbounded；
它单独解释显式非零假设，未作为新增独立冻结的理由。

见证四项：corner_chain 的构造在最终定理的传递常量闭包中；
已冻结前置与 Mathlib 通用 min/div 接口不提供该角点区间保持结论；
具体角点满足所有中间步的界不是最大性命题的别名或定义等价；
构造实用于 IsGreatest 的存在性分量，删掉它便缺少达到上界的证据。
此为源码和 Lean 语义读数的实施者核对，不冒称判形已经被机器或独立评审裁决。

utility: none。全部定义、实例、私有引理与公开定理服务任意有限坐标型及任意
自然边长、整数步长的通用命题。Decidable 实例直接采用已有有限全称可判定实例，
不是新检查器基础设施。没有固定数值实例、有界枚举交付、数值归约或待履行数值前提；
计算性用途其余字段为 not-applicable(kind=none)。
question_answered：预登记 v1 指定的 377.2 公式及角点达到性。
dominating_theorem_search：not-found-in-searched-scope；范围与方法见预登记及下段。

## 检索与复算

先查 D5，再查钉版 Mathlib 的 Finset.Ico、Nat.div、格点、arithmetic progression，
再查公开 GitHub Lean 代码与 Loogle。复用 Finset.inf'_le、Finset.le_inf'、
Nat.le_div_iff_mul_le、Int.natCast_natAbs；Nat.card_Ico 不是目标的等价陈述。
GitHub 补充查询 chain+rectangle 与 longest+lattice（各前10结果），
结果涉及网格结复形、Euler 路、图论圈长等，未命中本目标；
有界词面检索不证明整个生态没有等价定理。没有第三方移植或依赖变更。
外网能力已实测成功，未修改宿主配置。

独立枚举方法：每组参数穷举窗口内所有整数起点，从每个起点反复整数加 δ，
第一次出界时停止；以所有起点的最大实得点数比较两个公式。
枚举脚本与完整输出在 runner attempt 的 probe.py / probe.json。

| 维数 | 参数组数 | 主公式相符 | 主公式不符 | 首个非零坐标对照不符 |
| --- | ---: | ---: | ---: | ---: |
| 1 | 42 | 42 | 0 | 0 |
| 2 | 2352 | 2352 | 0 | 692 |
| 3 | 117306 | 117306 | 0 | 53548 |
| 合计 | 119700 | 119700 | 0 | 54240 |

范围为 1≤k≤3、0≤L(p)≤6、−3≤δ(p)≤3、存在非零分量。
计算用时 11.0695 秒，macOS 本树；不作为性能保证或形式证明。
对照例 L=(1,0)、δ=(−1,−3)：最长1点，只看首坐标错误给出2。
用户输入读数为 280/280 相符、对照74/280不符；未提供这280组的选取规则，
故不能声称精确复现该样本。完整范围的复算支持公式及 min 的判别力。

## 验证与失败边界

完整阅读 CLAUDE.md 与 agents/CONTEXT.md；Lean 头部7行、全文件每行≤100字符。
目录实测（新增后；Blueprint .md 不计）：D5/S3/Arith/Lattices=12，
Blueprint 对应目录=12，Library/ArithSums=28，均在48以内。
Library/Arith 原已48，故本 note 使用已存在且有余量的 ArithSums 桶。
Library note 逐键采用指定样本的 frontmatter，并在 Verified locator 正文含完整绑定URL。

首轮串行构建失败：首末点的 Fin 值未显式归约，omega 视为两个不同乘积；
零长度分支改为 Nat.zero_le。Lean LSP 诊断后补 change 归约，错误已消除。
此时曾由 Lean 自动引入 sorryAx，未据源码无 sorry 冒称通过。
修复后 LSP 的最终三条 axiom 输出仅为标准三公理，零错误和警告；
serial-lean 正式退出0，哨兵 status=complete built=1 failed=0 missing=1。
第一次构建还补齐了本树另一个已有缺失单元，不修改其源码。

lean-report 前两轮失败在新 Scribe 的编译：先是 DSL 名称应为 Land/Neq，
随后是 ScribeNode 的正文参数需要统一 Blocks。均按实际编译错误修复；
未改门、预算、检测或冻结模块。构建未被杀，没有遗留被杀的 lake 作业。

最终门链（退出码均为0，未跳门）：

1. serial-lean：status=complete built=1 failed=0 missing=1；missing 表示开跑时的待建数。
2. make lean-report：delta changed=0 added=1 recheck=1。29个报告声明，16个 included；
   全部 axiom 闭包之并恰为 Classical.choice、Quot.sound、propext。
3. make emit：发射1个 Blueprint；六条公开定理均为 std3。
4. CI Scribe 层：精确 merge-base
   b5c49d91bd5dc6ddb61a4785f479d1c5c4dcb1b0，
   DESCRIBE_STATUS case=DESCRIBE-NODES status=classified nodes=11154
   suspected_novel=0 formula_content_slots=68 formula_statements=32 red=0 observe=5011；
   `^RED` 行为0。Observe 数不是错误数。
5. make deposit-uncovered：使用完整 GID
   D5/S3/Arith/Lattices/RectangularDeltaChain.longest_chain_length；
   BASE为上述精确SHA。header-check通过，ledger-align changed=0 added=1 conflicts=0，
   最终 PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED reason=NO_ATOM。

冻结模块 statement_id：
sha256:00c84271d3559d435ceabb5b521db325e0b4e140d91e2899930b33035fca4fd9。
主定理 statement_id：
sha256:2b8021a0f4d43a173214c09398e6b0dabbfe68d7905ab80c3f5b7584ef353f2b。
Freeze event_hash：
sha256:6071d20325b4b3f771343550a418d0bad8a5b7cf811599c600614547a10f792d。
事件的 prerequisite_frozen_node_ids 为空。仅新增本模块的一对冻结工件。
源 atom 保持未覆盖；本次形态为 deposit-uncovered，不宣称整 atom 已消化。

当前源码 SHA-256 与 report 绑定一致：
3ad2cd3cc7bacbf283d6122bf1641c4dacb0a5fdef702b6385d7d44fcd8499d5。
缓存收据为 present、Mathlib/project 两层 warm、stamp_miss=null。
canonical route 实测返回预登记的 GID/path/S3 与七行骨架。
build_seconds: null（未单独测量正式串行构建墙钟）。

最终交接：分支 lane/math/deltachainwindow；提交以 runner result.json 为准。
fetch 后 origin/dev=35be0e20564c9fec39940c37740a03a8917ce4de；
merge-base仍为上述SHA，git merge-tree试合退出0。
未开PR、未运行 make pr-open、未合并；远端三 required check 与独立评审未由本席执行。
没有剩余数学子命题。下一步仅由 orchestrator 复核、开PR并完成合并。

日志根目录：
/var/folders/wv/ht3wzsj138b4sxl3q4t0xdr40000gn/T/consensus-rnd/sshx/dchain-1/attempt-1。
关键文件：serial-lean.log、lean-report-3.log、emit.log、scribe-content-checks.log、
deposit-uncovered.log、module-report.json、probe.py、probe.json。
