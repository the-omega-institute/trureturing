# A110037 implementation — 2026-09-10

产地：lean4 skill；Codex implementation worker 单点实施、自查，独立评审席 0。
用户与分诊席读数不冒作本席实测；外层 runner 独立评审另计。

当前结果：**blocked（命中用户的源文 0/1 边界停止条件）**。
目标 n≥2 未证明、未反驳；未冻结、未开 PR。以下早期“尚未”描述当批状态。

## 预登记

第一档。目标为用户给定 signed_nonsquashing_diff，n ≥ 2；左侧是互异且每部件
大于等于后缀和的直接分拆集合，右侧使用 A073089 独立分支定义。
拟议逃逸沿用户方案：正指标 f(r)=B(4r)%2 与 c(4r+1) 互补的强归纳，
再由 B 的已发表奇偶规则连接全部差分分支。该路线尚待实测，不预报成功。
禁止私有 axiom、sorry、native_decide、以一侧定义另一侧、造理论卷/atom。
无 atom 时走 make deposit-uncovered（现行内部为 ledger-align --add）。
先核 B(6)=4、B(10)=9；有限核对只是语义回声，不作正向实例冻结或部分进展。
停止判据照用户：规定范围内反例、分支数学不闭合或 0/1 边界冲突立即退回。
成须 make lean EXIT=0、无 sorry/私 axiom、PR 开出；否则报告真实 Lean goal 与最锐残题。

## 第一批检索与环境

- 已分段完整阅读 CLAUDE.md（780 行，工具截断处补读）、agents/CONTEXT.md、lean4 skill。
- 初始树干净，分支 lane/math/a110037；固定 base=82938786158c163b50350c14c948e63df61107a8。
- 仓内 rg -n -i 'nonsquash|non.?squash|paperfold|A110037|A073089|Sellers'
  D5 Library Blueprint，仅命中 Library/Words/oeis2026triage0910.md 的用户分诊记录；
  D5 无命中。该记录不是 Lean 定理。
- 已阅读 spec A5.1 的 utility 文法，none 为独立值。
- make lean-cache-ensure 已启动，未执行冷树裸 lake；Mathlib 与联网检索待续。

## 未主张

尚未证明、冻结、构建或开 PR；不主张文献全球完备或首创性。
尚未打开的页面均 ASSUMED-UNVERIFIED；用户列出的数值不算本席复验。

## 第二批检索与停止触发

- make lean-cache-ensure EXIT=0：status=seeded, donor=/Users/chronoai/trureturing,
  method=clonefile, clonefile_attempts=1, stamp_miss=null，project/mathlib 均 warm。
  Lean 4.33.0；Mathlib HEAD=db584cd6d46c92f209a44c0f1c829460d327499d。
- 钉版 Mathlib 全树 rg 上述 non-squashing / paperfold / A 号，零命中。
  已读 Partition.Basic 的公开定义/接口、Partition.Glaisher 全部公开面、
  Partition.GenFun 的全部公开签名及 genFun 定义。
  Euler/Glaisher 的 restricted/countRestricted 基于每种部件的 multiplicity；
  本题谓词比较一个部件与全部更小部件之和，不能直接代入该 API。
  partitionWithPartEquiv 只删去指定部件，不提供保持 non-squashing 的限制双射或本题递推。
- GitHub code search：'"non-squashing" language:Lean' 与 '"paperfold" language:Lean'
  均返回 []。这只是所搜范围无命中，不作全生态不存在的断言。
- 已实际打开 OEIS A110037/internal（revision 9, 2025-08-24），
  其 2025-08-19 差分式仍标 Conjecture；A073089/internal（revision 47, 2021-03-13）
  的分支与用户提供的一致。完整字段已读；未打开其余外链，ASSUMED-UNVERIFIED。
- 已实际下载并阅读 Sloane–Sellers arXiv:math/0312418 PDF p6–8，
  以及 Barry arXiv:2107.00442 PDF p2–4。二者所读段落未给目标差分证明。
  pdftotext 本机不存在（EXIT=127），已用 uv 的临时 pypdf/fonttools 环境提取并读取，
  不将工具缺失当文献缺失。
- **触发用户的 0/1 边界停止条件**：Corollary 4 (21) 原文为
  “if n is odd, b(n) ≡ b(n−1)+1”，未排除 n=1；同论文 Theorem 2 明给 b(0)=b(1)=1。
  故该原文在 n=1 变成 1≡0 (mod 2)，不成立。
  Theorem 2 的奇项递推 b(2m+1)=b(2m)+1 则明确限制 m≥1，没有这处问题。
  p7 Corollary 3 (i) 的 “adding 1” 也与 (14) 的减 1 文字相冲突，未作任何承重应用。
- **不是目标反例**：用户目标明确 n≥2。拟议桥若只用 n≥3 的奇项规则，
  此边界错误本身不否定该桥；但用户明令“任何 n=0/1 边界冲突，立即退回”，
  因而本席停止一般推导，只补 kernel 见证与交付收据，不自行解除该停止条件。

## 当前 Lean 检查

直接集合使用正整数区间的 powerset，部件天然互异；对每个 p 检查所有 q<p 的和 ≤p。
这就是按降序排列时的后缀和条件，允许等号。它不以 B 的递推或目标等式定义计数。
右侧独立照 A073089 分支递归；n=0 仅为域外总化，未用于目标或冲突证明。
BoundaryProbe.lean 已开始热树编译，先以 decide 检查 B(6)、B(10)，随后检查源句的 n=1 反例。
所有有限定理为 private，且只住报告目录，不新建 D5 模块、不冻结任何正向实例。

## Lean 实际尝试与构建收据

- 第一轮热树 Lean 检查：EXIT=1。B(6)=4、B(10)=9、B(0..12)、六的精确分拆集合、
  zero_one、printed_odd_rule_false 均已接受；错误只在 c 初值及 n=2/3 回声的 decide。
  具体错误：paperfoldVariant 是良基递归，Decidable instance 未归约到 isTrue/isFalse。
  这不是 decide 判命题为假；最终改用递归方程 norm_num。
- 第二轮对映射中的递归函数直接 norm_num，执行 91.299 秒后由本席中断，EXIT=130。
  修法是先化简 List.range/map，再展开数值参数的 paperfoldVariant，避免在符号 lambda 下
  展开递归定义。该次中断属于探针战史，不冒作 kernel 反例。
- 首轮的 #print axioms b_six、b_ten、printed_odd_rule_false 均只列
  propext / Classical.choice / Quot.sound；没有私 axiom 或 sorry。
- make lean EXIT=0，59.445 秒，12840 jobs；本机 macOS ARM、donor 热树。
  日志：runner attempt-1/make-lean.log，结构收据：make-lean-receipt.json。
  此命令构建既有 D5 项目；本席没有新增 D5 模块，不能用它冒称主目标已证明。
- 本次对用户点名模块 ConvolutionRecurrenceOddPowersOfTwo 的公开面亦作了逐条复读。
  convolution_pairing 对任意 f:ℕ→ZMod 2 成立；它消去卷积中点外的项。
  本席未建立直接分拆计数的卷积表示，所以它未成为本次 kernel 见证的依赖。
  不以该模块的序列题名排除一般引理。

本次 make lean 的完整缓存收据：

```text
LEAN_CACHE {"status":"present","worktree":"/Users/chronoai/trureturing-a110037","donor":null,"method":"none","reason":null,"stamp_miss":null,"pin_sha256":"sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":0,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## 最终 kernel 核验与结算

- 最终 BoundaryProbe.lean 热树检查 EXIT=0，全部私有探针通过。
  精确耗时见 runner attempt-1/boundary-probe-checked-receipt.json。
  B(6)=4、B(10)=9、B(0..12)、六的四个分拆、c(1..16)、目标 n=2/3 均通过。
  这些只是语义回声，不主张为原猜想的部分进展。
- 递归回声第三轮仍报 maxRecDepth（EXIT=1，34.286 秒），说明仅拆开 map 与递归
  简化不足；最终用 interval_cases 后一次 rw 展开每个具体分支，再 norm_num，EXIT=0。
  未提高预算以掩盖错误，未使用 native_decide。全部尝试日志保留在 runner attempt。
- **kernel 见证**：private printed_odd_rule_false : ¬ printedOddRule。
  活证明只取 n=1、Odd 1 与直接集合的 B(0)=B(1)=1，推出 1≠0 mod2；
  不调用 paperfoldVariant，不依赖其零指标总化，不改变或反驳用户的 n≥2 目标。
- **真实卡点**：原文无边界奇项规则 printedOddRule 已被 kernel 否定，
  不能作为一个闭合 Lean 前置。改为 n≥3 即与 Theorem 2 的 m≥1 边界一致；
  本席不声称这个修正难以完成，也不声称拟议差分分支无法闭合。
  本次停止的原因是用户明确的“任何 n=0/1 边界冲突，立即退回”，不是未搜到现成定理。
- **尝试路线**：先库后证与原文核对 → 直接分拆语义回声 → 原文奇项规则的 Lean 反例。
  触发停止后没有继续强归纳/四差分分支，也未走连分数路线。
- **最锐剩余的新桥**：对 r>0，直接集合基数 B 满足
  B(4r)%2 + paperfoldVariant(4r+1) = 1。
  还需有正确边界且可被 kernel 消费的 B 奇偶前置；文献引用本身不产生 Lean 证明项。
  未把该桥或 B 递推放在 axiom 位置，未用假设替换原目标后冒称已证。

## 声明级账目与未主张（最终）

公开 theorem：0。没有 D5 / Blueprint / Library / atom / 冻结状态变更。
主目标 signed_nonsquashing_diff 尚未声明为已证 theorem：
proof_shape=null（未完成证明）；direct_frozen_dependencies=[]；escape_witness=null；
admission_basis=null（不申请冻结）。所以不存在可据以声称 content 准入的见证。
全部通过的有限检查均为 private，未单独冻结；printed_odd_rule_false 同样只作停止证据。
三项禁止均守住：无 sorry、无新增 axiom、无 native_decide。
未运行 make lean-report / make emit / make deposit / scribe-content-checks：
本席因停止条件只交付报告与探针，无叙事/冻结候选；不宣称这些门已经通过。
未开 PR，未改理论源、未 ingest、未新增/删除 atom、未构造 coverage。
未执行 n≤4096 全范围或直接分拆 n≤35 的核对；用户已核读数仍为用户来源。
未证明或反驳原猜想；未主张全球文献无证明、首创性或多模型共识。
原条目的未访问链接仍 ASSUMED-UNVERIFIED；外层 runner 的后续评审不计入本席结果。
