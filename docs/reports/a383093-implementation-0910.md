# A383093 implementation — 2026-09-10

产地：lean4 skill；Codex implementation worker 单点实施、自查，独立评审席为 0。
用户 brief 的两侧枚举及分诊结果为用户/分诊席报告，不冒充本席核验。

## 预登记

第一档。目标：独立定义 capablePartitionCount 与 constantEqualSumSystemCount，
证明对所有 n > 0 的 capable_divisor_sum。两侧定义均不得含目标除数和。
拟议逃逸见证沿用用户 brief：支撑 lcm L 为规范公共块和；系统公共和 D=tL，
重数除以 t 得到重量 n/t 的 capable 分拆；乘回 t 唯一恢复系统。
该路线当前为 ASSUMED-UNVERIFIED；需证明规范化可行、唯一与重量等式。
拟议 proof_shape=content，admission_basis=escape-witness，最终按实际证明核对。
无 atom 时使用 canonical deposit-uncovered（内部 ledger-align --add），不建理论卷、不 ingest。
停止：发现公开同一规范化双射即撤派；成须 make lean EXIT=0、无 sorry/私 axiom、PR 开出；
翻须 kernel 反例；blocked 须真实 Lean 尝试、具体 goal/错误、最锐剩余子命题。

## 开工与检索第 1 批

- 完整分段读 CLAUDE.md（779 行，截断处补读）、agents/CONTEXT.md、lean4 skill。
- 工作树初始干净；branch=lane/math/a383093；固定 base=462d0a4368ba5a890c5eab619c82437baa88966f。
- 报告目录新增前直属文件数为 46。
- D5 粗筛：rg -n -i 'capable|A383093|A323774|A381995|A381993|A383014|constant.{0,30}(equal|sum)|等和常值' D5。
  未命中目标 A 号；命中 ConstantBlocksDistinctRunSums 的组合模块，另有无关领域同词。
  下一步逐条读命中组合模块的公开声明，并扩大同族词汇检索。
- 尚未进行 Mathlib/第三方/OEIS 检索与 Lean 编译，不主张 search-complete。

## 未主张（开工时记录）

未主张已证明、反驳、冻结、构建通过或开 PR。未主张全球不存在既有证明或首创性。
未打开的外部页面为 ASSUMED-UNVERIFIED；有限枚举不作为一般定理的部分进展。

## 检索第 2 批

- 完整读 ConstantBlocksDistinctRunSums.lean 的 383 行，包括全部公开面：
  HasConstantBlocks（正值正重数、块和单射的有限集合）、runSums、HasDistinctRunSums，
  constantBlocks_iff_distinctRunSums、card_constantBlocks_eq_distinctRunSums。
  两条定理提供块和互异/极大游程和互异的对应，不给本题等和块的规范化；
  私有引理的重平衡/排序构造亦不提供 lcm 重数缩放。
- 扩检 equal.?sum|constant.?block|capable.?partition 与五个 A 号，D5 无新增相关命中。
  Library/Words/oeis2026triage0910.md 记载用户同一预登记（308 行）；不是新的证明来源。
- make lean-cache-ensure 已启动；未运行裸 lake。首次报告提交 9dbcc5a3b3 已推远端。

## 检索第 3 批与缓存

- make lean-cache-ensure EXIT=0：status=seeded, donor=/Users/chronoai/trureturing,
  method=clonefile, clonefile_attempts=1, stamp_miss=null, project_olean_state=warm,
  mathlib_olean_state=warm, archive_status=not_attempted。
- 实测 lean-toolchain=leanprover/lean4:v4.33.0；Mathlib HEAD=db584cd6d46c92f209a44c0f1c829460d327499d。
- Mathlib Combinatorics/NumberTheory 搜 capable|constant.?block|equal.?sum|383093|323774 无命中。
  已读 Nat.Partition 的结构、正性/重量/有穷性、计数编码 API，以及 Finset.lcm 的
  lcm_dvd_iff、dvd_lcm、lcm_ne_zero_iff 等签名；这些是可直接复用的基础设施，未见目标桥。
- 扩大 D5 公开面检查：FirstSumsPartitionCharacterization 全文，
  TrimmedAlternatingPartitions 两公开定理及定义，PowerfulDivisorTransform 全部公开面。
  前两者分别是相邻和重建及排序尾严格性；后者是 powerful 指示函数的卷积，
  其一般参数 f 不提供本题两种对象的计数等价。未发现可消费的规范化声明。
- 已打开 OEIS A383093/internal（HTTP 成功，13917 字节）；外部文献核查继续。
- spec A5.1 确认 utility: none 文法与七行头位置；Meta/domains.yaml 已读。

## 检索第 4 批

- OEIS 主条目 revision 13 (2025-05-04)：formula 仍为 Conjecture，
  Sum_{d|n} a(d)=A323774(n)。全部 42 个直接 xref 已下载成功，原 HTML 与提取字段在 runner attempt。
- 已逐字段读 A323774、A381995、A381993、A383014、A383309、A382203、A279789。
  A323774 给系统计数二项式和，A381995 按整数编码纤维求和，未给本题规范化双射。
  A382203 当前名称是 distinct sums；主条目一条 xref 把 equal 类型指到它，实为 A382204，
  此为来源交叉引用差异，不影响目标定义，未静默当成同一对象。
- gh search code 'A383093 language:Lean' 返回 []；'"constant blocks" language:Lean'
  返回两个 Kakeya Plank/Refinement 路径（非分拆库），尚未打开，ASSUMED-UNVERIFIED。
- arXiv A383093 检索页成功下载；下一批读其结果及全部 xref 的相关命中。
- 精确可复用 Mathlib 命中：Multiset.exists_smul_of_dvd_count，
  ∀a∈s, k∣count a s → ∃u, s=k•u。已读完整证明与签名；本题将直接应用，禁止重证。

## 检索第 5 批与 Lean 片段 1

- 42 xref 的全文提取字段检索 lcm|least common|normaliz|bijection|bijective|383093|moebius|möbius|mobius|common sum。
  逐条读相关命中并完整补读 A382204、A383096、A383098、A383100、A383110、A047966。
  A047966 是 uniform partitions 到 distinct partitions 的另一除数变换；未给本题 lcm 桥。
  arXiv 搜 A383093 明确 produced no results。未打开的 xref 外链、未逐字段细读的普通族条目
  仍标 ASSUMED-UNVERIFIED；不主张全球搜索穷尽。dominating_theorem_search=not-found-in-searched-scope。
- canonical route EXIT=0 返回 D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity.lean，S1/G。
  创建前该 Lean 桶 7 文件，Blueprint 桶 14 文件；utility: none（无界组合证明）。
- 热树 /tmp/A383093.lean 首试失败于缺 NormalizedGCDMonoid ℕ 实例与 nlinarith import。
  加 Mathlib.Algebra.GCDMonoid.Nat 与 tactics 后 EXIT=0，无 sorry/私 axiom。
- 已证私有 normalize：正整数多重集 m 在 D>0 可行，则存在 t>0、u，
  m=t•u、D=t*lcm(u)、u capable；使用 Mathlib.exists_smul_of_dvd_count，未重证它。
  lcm_smul/canonical/admits_smul 同批通过。这是无界构造，非有限枚举进展。
- 定义尚在组装：下一步为块多重集编码证明、重量与计数双射。主目标尚未证明。

## Lean 片段 2：重量与计数双射

- 当前模块热树 lake env lean EXIT=0。已构造从除数 d 上的 capable 分拆到
  (n/d) 倍重数、公共和 (n/d)*L 的系统编码的映射，并证明 injective/surjective。
- injective 使用支撑 lcm 不变先恢复缩放因子，再由重量恢复 d，最后取消非零 nsmul。
  surjective 使用 normalize 及 t*u.sum=n；没有把目标除数和写入计数定义。
- 私有 encoded_divisor_sum 已证明编码系统的 Nat.card 等于除数和；
  下一步将右侧改接独立的公共和/块值多重集定义，证明展开编码等价。
- 编译修复：omega 不处理交换次序的乘积，改用 mul_comm；依赖 subtype 的 sum 改显式
  Finset.sum_subtype；pair projection 的 rewrite 改精确使用已有等式。无数学目标削弱。

## Lean 片段 3：原始块系统与主定理

- 模块热树 lake env lean EXIT=0，capable_divisor_sum 的 #print axioms 仅为
  [propext, Classical.choice, Quot.sound]；无 sorry/私 axiom。
- 左侧现在以 ∃D,b, D>0、b 的每个值为 D 的正除数、expand D b=m 直接定义存在性，
  不是用另一侧计数生成。右侧独立以 (D,b) 的基数定义；b 的重数是相同块的次数，
  每个 x 编成 D/x 个 x 的常值块，重量 D*b.card=n；n=0 单独计唯一空系统。
- 私有 count_expand、mem_expand、sum_expand 验证此编码的重数、支撑与重量；
  blocksOf/expand_blocksOf 与 expand_injective 证明任意算术可行编码都唯一还原块多重集。
  encodeSystem 的双射把 encoded_divisor_sum 接回原始系统定义。
- 先前一次编译错误为 Prod.ext rfl 过早推断两端相同；改 refine 后通过。
- 唯一公开 theorem 是 capable_divisor_sum；两侧没有除数和定义。仍待项目构建与叙事/冻结/PR 门。

## 项目构建与语义回声

- make lean EXIT=0，实测 51.720 秒，Build completed successfully (12835 jobs)。
  日志：runner attempt/make-lean.log；本模块有两处长行警告，已折行；最终重跑通过（见下）。
  其余长行警告来自既有模块。先前“本模块无警告”的记录有误，在此更正。
- 首次 make lean-report EXIT=0，实测 97.718 秒；报告位于
  .lake/build/stratalint/raw-lean-report.json。折行改变源码字节，最终构建后须重新生成。
- 独立 Python 语义探针 n=1..25：左侧枚举所有分拆并直接检验公共和/重数整除；
  右侧枚举公共和 D 的除数多重集并展开真实块；没有从一侧生成另一侧计数。
  a(1..12)=[1,2,2,4,2,7,2,9,5,9,2,23]；s(1..8)=[1,3,3,7,3,12,3,16]；
  不满足恒等式的 n 数量=0。systems(4) 的七项实际列在 semantic-probe.json。
  这是语义回声，不是数学证明或单独冻结的正向有限实例。
- 新 Library note 含 Verified locator，逐字包含 frontmatter 的 url 与 doi: null；
  Scribe 仅陈述定义、归一化证明与数学结论，不含判形治理词汇。

## 逐公开定理判形（候选最终证明）

唯一公开 theorem：D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity.capable_divisor_sum。

- proof_shape: content。
- 直接冻结依赖（GID + statement_id）：[]。模块只导入钉版 Mathlib；其声明不计本仓冻结前置。
- escape_witness: private normalize（D=tL 的系统重数除以 t、支撑不变且规范和为 L）。
- admission_basis: escape-witness。
- 第 3.2(i)：normalize → liftSystem_surjective → encoded_divisor_sum → capable_divisor_sum，
  按“消费者 → 前置”写为 capable_divisor_sum → encoded_divisor_sum → liftSystem_surjective → normalize。
  后续以当前 Lean report 确認公理闭包及声明身份。
- 第 3.2(ii)：已有 lcm/整除与 exists_smul 引理不直接提供重数可除、保留支撑的可行性或系统逆映射；
  normalize 中先新证 t∣count，再取消 t 得规范分拆。不是冻结前置的实例化/投影所得。
- 第 3.2(iii)：normalize 是逐对象存在构造，结论非计数等式，非其定义等价/别名/重述。
- 第 3.2(iv)：构造的 u 用作满射原像，参与 Equiv.ofBijective 的逆函数与 Nat.card_congr；
  删除此构造后所给证明不能得到任意系统的原像。不是合取中被丢弃的死分量。
- utility: none。全部公开定理均无界量化；无枚举、检查器、数值归约或认证有限实例。
  其它用途字段 not-applicable(kind=none)。
- question_answered：用户预登记的 A383093 除数和猜想，保持 n>0。
- dominating_theorem_search：not-found-in-searched-scope；范围与限制见各批检索收据。

## 最终源码构建

- 折行后 make lean EXIT=0，实测 23.505 秒；日志 runner attempt/make-lean-final.log。
  本模块无长行警告，主定理公理仍仅 propext、Classical.choice、Quot.sound。
- 再次自查全部 311 行源码：两侧独立对象定义、正性、展开/唯一恢复、lcm 规范化、
  缩放双射和有限基数取和均在实际证明路径内。尚未冻结或开 PR。

## 最终 Lean report 与冻结前复查

- make lean-report EXIT=0，实测 65.367 秒；日志 runner attempt/make-lean-report-final.log。
  LEAN_CACHE=status:present, method:none, project_olean_state:warm, mathlib_olean_state:warm。
- 主定理 statement_id=sha256:be6319a9b79b844435ef13c6697b64d6d5349220ef1557392d9a215b6485a67e；
  公理闭包仅 Classical.choice、Quot.sound、propext。报告同时列出编译器生成的
  expand.eq_1、constantEqualSumSystemCount.eq_1，它们 include_in_statement=false，
  不是本席新增的公开数学结论；手写公开 theorem 仍仅 capable_divisor_sum。
- normalize 的 statement_id=sha256:c27baac5262b322b9b97905fbe74cd8cc67d8280a6a766bb4d3c9eec214206ee。
  此为私有见证，不作为单独公开/冻结结果。
- git fetch origin dev 成功，origin/dev 仍为预登记 base 462d0a4368ba5a890c5eab619c82437baa88966f；
  D5 再查 A383093|A323774|capable.?partition|constant.?equal.?sum，无新增命中。

## Scribe 发射

- 首次 make emit EXIT=2，18.293 秒，命中 Formula emission rejected：Mid 后直接接 n
  会生成错误宏 midn。已在 .scribe.cs 的 Mid 与 n 之间加 FormulaDsl.Sp；未手改 Markdown。
- 修复后 make emit EXIT=0，61.214 秒；日志 runner attempt/make-emit-final.log。
  仅本模块 Blueprint 新增；emit-values、filemap、dag 生成均完成。
- 已读完整生成的 Blueprint：正整数范围、除数和公式、两侧定义、规范化及 Conjecture
  来源标识均与 Lean/Library 一致。下一步为 scribe-content-checks 的机器内容检查。

## Scribe 内容门（PR 前本地实跑）

- bash tools/scripts/workflow/scribe-content-checks.sh .lake/build/stratalint/raw-lean-report.json
  "" 462d0a4368ba5a890c5eab619c82437baa88966f：EXIT=0，23.656 秒。
  describe-report：red=0；markdown-check：judged=1、formula(s)=1、red=0（真 KaTeX）。
  本次路径条件未触发 projections；另显式运行同一 Scribe 的 projections --check
  --report .lake/build/stratalint/raw-lean-report.json：EXIT=0，10.854 秒。
- 原始日志为 runner attempt/scribe-content-checks.log、scribe-projections-check.log。
  describe-report 的既有 OPEN/OBSERVE 不冒称已解决；新增 note 没有 incomplete-library-locator。

## 冻结

- make deposit-uncovered BASE=462d0a4368ba5a890c5eab619c82437baa88966f
  GID=D5/S1/Words/Compositions/ConstantEqualSumDivisorIdentity.capable_divisor_sum：
  EXIT=0，83.695 秒；日志 runner attempt/make-deposit-uncovered.log。
- canonical 门序：lean-report（当前输入缓存命中）→ deposit-header-check → emit
  → ledger-align --add；最终 reason=NO_ATOM。
  LEDGER_ALIGN：changed=0、added=1、unchanged=3948、conflicts=0。
- 仅新增本模块 accepted/state 两个文件；无 theory/atom/coverage 修改。
  Freeze event_hash=sha256:2b6e7afd8babc047068c8daa85e00b22730aa6b9273aa93ff3c2381a52a25f2a；
  模块 statement_id=sha256:254430127ee8a1507f96467f6f24c19db7d11b45efec016652b5300fbf6dcf15；
  prerequisite_frozen_node_ids=[]。以上直接读取新冻结记录，未重算历史账本。
- 冻结后不再改 Lean 文件；下一步开 PR 并由 canonical pr-open 等待 required CI 判词。

## PR 交付

- PR：https://github.com/the-omega-institute/trureturing/pull/6740；state=OPEN，base=dev。
  首次 PR head=f3f66fe7d5aa988bc284fafce064cd1a21c58f4e；autoMergeRequest=null。
- 按用户三态判据已达“成”：主定理证明完成、make lean EXIT=0、无 sorry/私 axiom、PR 已开。
  这不等于 CI 已绿或 PR 已合并；写入本条时两项 required check 正在运行，第三项尚待上游。
  canonical make pr-open 正在同步等待最终 required-CI 判词，原始日志及最终退出码保存在
  runner attempt/make-pr-open.log、make-pr-open-receipt.json，最终结构化结果在 result.json。
- 当前无待证子命题。原先 ASSUMED-UNVERIFIED 的 lcm 规范化路线已经 Lean 验证；
  来源检索中未打开的外部页面仍保持 ASSUMED-UNVERIFIED。

## 最终未主张

- 不主张 n=0 的除数和恒等式、全球首创或文献检索穷尽。
- 不把有限枚举称为证明；不把用户/分诊席的独立核验或外层 runner 评审冒作本席结果。
- 不主张同族所有条目均已形式化、原条目已有公开证明或本 PR 已合并。
- 没有新增理论卷、atom、coverage、私 axiom、sorry、native_decide 或正向有限冻结实例。
