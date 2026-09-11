# A398720 implementation — 2026-09-10

产地：`lean4` skill；Codex implementation worker 单点实施、自查，零独立评审席。
用户/分诊席的枚举与文献读数是转述，不冒作本席实测；外层 runner 的评审另计。

当前 implementation 结果：**成**。原签名已证明并冻结，make lean EXIT=0；
PR https://github.com/the-omega-institute/trureturing/pull/6744 已开出，base=dev，未合并。
CI 在本条收据时仍运行，本文不主张 CI 三门已绿。以下各批次的“尚未”仅指该批次当时状态。

## 预登记

第一档。目标严格为用户的 `spcp_odd_top_weight`，矩阵类型为
`Fin n → Fin n → Bool`，每行每列的 1 数为偶，总重量为 `n*(n-1)`。
定义不得含阶乘或计数结论。拟议见证为：每行至少一个零，加上总重量条件，
迫使每行恰一个零；列同理，零位置构成置换，反向用置换的补集构造矩阵。
这仍待 Lean 核验。预计唯一公开定理 proof_shape=content，
admission_basis=escape-witness；直接冻结依赖与见证四项留待证明后核对。
utility=none：无界量化的组合双射，非有限枚举、checker、数值归约或认证实例。

停止条件照 brief：DATA 对不齐、发现同一全称命题的外文证明、或无额外假设双射
无法构造则退 note。三态：成=make lean EXIT=0、无 sorry/私 axiom、PR 开出；
翻=kernel 反例；blocked=实际 Lean goal/错误及最锐剩余子命题。
无 atom；使用现有 `make deposit-uncovered`（内部 ledger-align --add），不建理论卷，
不 ingest，不制造 coverage。n=1 必须涵盖。

## 开工与检索第 1 批

- 分段完整阅读 CLAUDE.md 779 行（工具截断处补读）、agents/CONTEXT.md、lean4 skill。
- 指定工作树初始干净，lane/math/a398720；固定 base=24279623ef5253194f6c64ee3b3b627e62e3df50。
- lean-toolchain=v4.33.0，manifest mathlib pin=db584cd6d46c92f209a44c0f1c829460d327499d。
- docs/reports 直属文件数 48，故本报告在 a398720 子桶。
- D5/Library/Blueprint 粗筛 A398720、A396317、EvenRowsCols、SPCP、single.parity、
  even.row、even.column：只有分诊 note 与非目标的 dyadic-row 结果，未见同目标定义/定理。
- 扩展检索 card_perm、sum_eq_sum_iff、card_eq_one、existsUnique、Equiv.Perm、
  rowSum/rowWeight；命中模块公开面还需逐项读取，不以题名排除一般引理。
- spec A5.1：utility: none 在 anchors 与 digest 之间；域由 Meta/domains.yaml 注册表选取。
- 已首先启动 make lean-cache-ensure；未运行冷树裸 lake。缓存结果尚待读取。

## 未主张

尚未主张证明、冻结、构建或 PR 已完成。未主张全球无已有证明或首创性。
尚未打开的外部页面均为 ASSUMED-UNVERIFIED；用户 1/3/5 枚举及分诊的 66068
自由赋值核对不是本席计算。不把有限核对称为一般定理的部分进展。

## 检索第 2 批与缓存

- make lean-cache-ensure EXIT=0：status=seeded、method=clonefile、donor=/Users/chronoai/trureturing、
  clonefile_attempts=1、stamp_miss=null、project_olean_state=warm、mathlib_olean_state=warm，
  archive_status=not_attempted。分支首个提交 129ce69141 已成功推送。
- 钉版 Mathlib Data/Fintype/Perm.lean 全文已读，直接复用 Fintype.card_perm。
  Data/Finset/Card 的 card_filter_add_card_filter_not、card_eq_one_iff_existsUnique
  是拟用的零数分解与唯一性接口；Matrix/Permutation、Stochastic 公开面继续核对。
- D5 选中相关公开接口逐项读取：EscapeCount 的 diagonal_landing_fixed 与
  escaped_listing_card；FiniteSelfMapConjugacy 的两条一般共轭定理；MatchingEquiv 的
  fiberToFactors、单射/满射、matchingMonomialFiberEquiv 和三条计数/系数定理；
  DataProcessingEquality 的一般通道等号条件。均未提供本题的偶性/重量到零位置的桥。
  GoldenFactorSecondOrderBinomialRigidity 的公开定理约束 goldenWord 前缀，不直接适用，
  但其使用的 Mathlib sum_eq_sum_iff_of_le 可直接复用，继续定位上游。
- 实际 curl 成功打开 A398720/internal，已读全部字段：revision #66 (2026-08-20)；
  %C 明定 n×n、2k 个 1；%F 仍明确 Conjecture: T(n,n*(n-1)/2)=n! for n odd。
  %e 各行 n=0..6 唯一对齐，n=1/3/5 行尾为 1/6/120；%O=0,8。
  标题的 (n+1)^2 偏移不进入模型。原始页面存 runner attempt/oeis-internal.html。
- 本席未重新打开 11 个 xref 全文与 Thompson/Patel–Hong PDF；其既有检查见
  Library/Words/oeis2026triage0910.md 的 A398720 段，是上游转述的有界文献结论，
  对本席亲验口径标 ASSUMED-UNVERIFIED。不声称穷尽编码文献。

## 检索第 3 批：收口

- GitHub code 搜索 A398720 language:Lean 与 EvenRowsCols language:Lean 均返回 []。
  arXiv A398720 查询页明确 produced no results（原页存 runner attempt/arxiv-search.html）。
- GitHub parity/matrix/Lean 粗筛命中 FormalRV/QEC/LDPCMatrix.lean，已在
  c40ac65d72df7760a5e441ad7269e2ddedcc49c7 打开全文：List Bool 矩阵、xor、行组合、
  稀疏度布尔检查及小例，无本目标计数或双射。其余粗筛为群/模形式/微分形式等邻词命中，
  未逐页打开，标 ASSUMED-UNVERIFIED，不以该查询声称全生态无定理。
- 新命中的 D5 MonomialDiagonalPreserving 全文公开面已读，只从给定置换定义 monomial
  并证明保持对角矩阵；GraphPairingCriterion 全文给函数图的行列分离条件。
  二者不提供从行列偶性与总重量导出的唯一零位置，未发现可直接消费的冻结前置。
- Mathlib Stochastic 公开 API 为非负性、行列和、凸性、置换矩阵正向实例及转置/reindex；
  未见本目标或 Bool 计数反向构造。直接使用有限和/有限集及置换基数 API。
- dominating_theorem_search=not-found-in-searched-scope，维持第一档，有界检索不主张首创。
- 检索中一条自写 rg 正则有 unclosed character class，已改简单词首正则重跑；
  一个候选 Mathlib 路径不存在，已按实际源码路径读取，未把命令错误当零命中。

## Lean 片段 1：唯一零位

- canonical route 返回 D5/S1/Words/ParityCode/OddTopWeight.lean，S1，generality G；
  二维二进制字的奇偶约束采用已注册 Words 域，新 ParityCode 子桶原不存在、落入 1 文件；
  Blueprint/Words 直属 20 文件、Library/Words 29 文件（find 实测）。
- 已定义 ones（逐位 0/1 自然数和）、EvenRowsCols（逐行/列 Even）、weight（行和总和）。
  定义均不含阶乘或计数结论。
- 热树 #check 成功核对 Finset.sum_eq_sum_iff_of_le、sum_boole、Nat.card_congr、
  Equiv.ofBijective、Finite.surjective_of_injective、Equiv.sum_comp 等签名。
- 单文件 Lean EXIT=0，已证 ones_add_zeros、row_bound、rows_saturated、row_unique_zero。
  第一编译在反向 sum_boole 的 Nat coercion 匹配和 hn.not_even 字段失败；
  用显式自然数求和恒等式与 Nat.not_even_iff_odd 修复，未改假设或命题。
  成功编译仅有 unnecessarySimpa 警告，已按建议简化为 simp，下一批验证。
- 新中间命题 row_unique_zero 正是预登记见证；列转置、置换与反向构造尚待完成。

## Lean 片段 2：双射与原定理

- 单文件 Lean EXIT=0，无警告；spcp_odd_top_weight 原签名已闭合。
  #print axioms 输出恰 [propext, Classical.choice, Quot.sound]，没有 sorryAx 或私有 axiom。
- 列唯一性由转置和 Finset.sum_comm 得到；零位函数由列唯一性为单射，
  直接调用 Finite.surjective_of_injective 与 Equiv.ofBijective 构造置换。
- permComplement σ i j = decide (σ i ≠ j)，其每行/列零集分别为 singleton σ(i)
  与 singleton σ.symm(j)，从 ones_add_zeros 得到重量 n-1；Odd n 推出 Even(n-1)。
  topWeightEquiv 的两侧逆律都已证明，再直接调用 Nat.card_congr 与 Fintype.card_perm。
- 编译修复记录：simp 未自动把等式筛选集化为单点，补显式集合外延；
  `ext i` 曾递归到 Fin.val 等式，改 Equiv.ext；宽泛 simp [eq_comm] 达到递归限制，
  改 simp only 后 exact eq_comm；移除了一个 deprecated Equiv 引理名。
  这些均是 Lean 目标修复，未改数学陈述或加强假设。
- Library note 已写 Verified locator，正文逐字包含 url 与 doi 行；Scribe 叙事只写数学。
  全项目 make 门、Scribe 内容检查、冻结和 PR 尚待执行。

## 逐公开定理判形（实现后）

唯一公开定理：D5/S1/Words/ParityCode/OddTopWeight.spcp_odd_top_weight。
proof_shape: content；admission_basis: escape-witness；直接冻结依赖：[]（仅 import Mathlib）。
escape_witness: row_unique_zero（private），及其活前置 rows_saturated/row_bound。
第 3.2 条四项：
1. 依赖闭包内：主定理 → topWeightEquiv → zeroPerm/zeroPerm_spec → row_unique_zero。
   该调用链为 elaborated 证明所使用；稍后 canonical report 核对声明身份。
2. 非投影可得：冻结前置为空；Mathlib 有比较和的等号条件，但没有给出
   Odd n 与 EvenRowsCols、weight 假设下的逐行唯一零位置。row_bound 用奇偶不相容
   排除满行，rows_saturated 将整体重量落实到每行，非只改写已有目标定理。
3. 非定义等价：每行唯一零位是一个结构命题，既不是 Nat.card 等式，也非其定义展开。
4. 活推导路径：zeroPerm 用该存在性选值、列版本证明单射；zeroPerm_spec 用唯一性
   证明矩阵重建。删除这些证据后该置换及两侧逆律无法仅由绑定步骤获得。
全部 helper 为 private，不单独冻结普通实例；公开定义 ones/EvenRowsCols/weight 只建模。
utility=none：所有定理均为任意奇数阶的一般组合构造，不属于四类计算性内容。
其余用途字段 not-applicable(kind=none)。此判形为本席语义自查，不冒称机器或独立评审判词。

## 全项目构建

- make lean EXIT=0，实测 62.506 秒（macOS ARM，本工作树 clonefile 热缓存，含 donor
  与当前树之间的增量构建；不是 CI 性能）。真实退出码与耗时由 subprocess 收据记录于
  runner attempt/make-lean.receipt.json，原始日志 make-lean.log。
- 构建等待时按实际进程核对：lake build 与 Lean 编译器在工作，不以静默判失败。
- 开 PR 前再次 git fetch origin dev；git merge-tree --write-tree HEAD origin/dev
  EXIT=0，树 OID 3cb756e1fee26499cd994cf449e1e4e57debec4b，无冲突。
  对该次 origin/dev 的 D5 用 git grep -P 查 spcp_odd_top_weight/A398720/EvenRowsCols
  无命中；未发现并发重复实现。没有迁移或复活 dev 上已删除模块。

## Canonical Lean report

- make lean-report EXIT=0，65.979 秒；delta 计划 changed=0、added=3、recheck=3，
  含本模块与 donor 缺的两模块，未手搓全库报告。
- raw report SHA256=d6193c94db65fa5320b029809a4727203f485062f6bf05b4ccf893a965d5e06f。
  输入地址 182c0d1c84a725c2b2112baca7f34df1125f14db15bdfebac23fe7cabc63970e。
- make lean 的缓存收据另为 status=present、method=none、stamp_miss=null、
  project/mathlib 两层 warm；初次播种收据见第 2 批，二者口径不混用。
- 已开始 make emit。第一次临时 Lean 常量遍历脚本 EXIT=0 但没有输出边，
  尚不能作为闭包读数，正在核对 ConstantInfo.value? 对 opaque 证明的读取语义。

## 发射与证明依赖核对

- make emit EXIT=0，52.975 秒；恰 1 篇 Blueprint 改变，生成的公式与数学叙事已读。
  其余全局 Generated 投影均未进入 git 索引。
- Lean 环境 API 的 ConstantInfo.value? 默认不返回 theorem/opaque 证明；
  加 allowOpaque := true 后临时脚本 EXIT=0，实际打印主定理 → topWeightEquiv →
  zeroPerm/zeroPerm_spec → row_unique_zero → rows_saturated → row_bound。
  原脚本与边日志将存 runner attempt，取自本次编译环境，不是 grep 推断证明依赖。
- canonical module report 中 imports 恰为 Init 与四个 Mathlib 模块，无 D5 冻结前置。
  手写公开 theorem 仅 spcp_odd_top_weight，statement_id=
  sha256:8a74ef05b4212a6907b6175b7becd3ba6cad3e7a5589bf17c0f02365a87a5bcc。
  ones.eq_1/weight.eq_1 是编译器方程定理，include_in_statement=false，不另作交付声明。
  row_unique_zero 的 statement_id=
  sha256:1d421a4b93d7b860b489e1402876eb2c09a72b541d777259b653882e7a9bbf0d。
- 已启动用户指定 scribe-content-checks.sh，固定 base 24279623ef5253194f6c64ee3b3b627e62e3df50。

## Scribe 内容门

- 用户指定命令 bash tools/scripts/workflow/scribe-content-checks.sh
  .lake/build/stratalint/raw-lean-report.json "" 24279623ef5253194f6c64ee3b3b627e62e3df50
  EXIT=0，23.436 秒。describe-report 检查通过；真 KaTeX markdown-check
  judged=1、formula(s)=1、red=0；Library locator 无 incomplete-library-locator 红。
- 本次 delta 不含 Golden/Projection 变更，脚本按其现行条件不唤醒 projections；
  另用同一 canonical Scribe 程序显式运行 projections --check --report
  .lake/build/stratalint/raw-lean-report.json，EXIT=0。三子项均已在本地检查。
- 已启动 make deposit-uncovered，GID=主定理、BASE=固定 40 位 SHA。
  这是用户允许的无 atom 路径，canonical writer 内部执行 ledger-align --add；
  不运行 make ingest，不新增 theory/atom/backfill，也不制造自指 coverage。

## 冻结

- make deposit-uncovered EXIT=0，83.833 秒；内部 lean-report 命中相同输入缓存，
  deposit-header-check 成功，emit 为 0 changed，ledger-align --add 成功：
  selectors_considered=3952、changed=0、added=1、unchanged=3951、conflicts=0。
- 新状态片 Golden/Frozen/state/D5/S1/Words/ParityCode/OddTopWeight.lean.json
  模块 statement_id=sha256:088ebcae487f0abaf7a32d2fc1e0318eb2a84f752ad805bbec40ca688b6d3358。
- 对应 accepted 事件为
  9faa636507290b7ccdf15f2f20e529030970ef7c2230a170476d41313ee689e5.json。
  主定理声明身份见上，模块身份与声明身份不混称。
- 落地形态是冻结、未覆盖：reason=NO_ATOM；无 source_id/atom_id，也无消化状态迁移。
- 已完成本地要求门序。下面开 PR；不主动合并，由外层 runner 按本 implementation brief 接手。


## PR 与交付范围

- make pr-open 已创建 PR #6744，state=OPEN、isDraft=false、baseRefName=dev；
  创建时 head=bdf94227d52a2c3a24d1aa8c6f4d1bf453a92790。未设置 AUTO_MERGE。
- question_answered：A398720 奇数阶边界项猜想，预登记见用户 brief 与本报告首节。
  目标未改、无额外假设，采用 comment/DATA 的 n×n 对象；全称证明包含 n=1。
- 本 implementation brief 的“成”门槛已达到；它不等于 PR 已合并或全部 CI 已绿。
  CI 最后读数另列于 runner result.json，不以本地成功替代远端判词。
- 未主张整个 SPCP 三角形、任意固定 k 公式或其他同族问题已解决；未主张全球文献穷尽
  或首创性；未重算或冒领用户有限核对；未主张独立评审、未主动合并 PR。
- runner 产物将原子写入 result.json 与 completion.sentinel；原始构建日志、收据、
  module-report.json、proof-dependencies.lean/log 与主条目页面存同一 attempt 目录。
