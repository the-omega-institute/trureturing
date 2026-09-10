# A110037 attempt 2 — implementation record

产地：lean4 skill；Codex 主 worker 单点实施与自查；独立评审席 0。
Runner 的后续独立评审不计入本席。本次用户 brief 为预登记输入。

结算：**blocked（具体 B 的 kernel 前置与现有“不重证”约束冲突）**。
不是 n=1 勘误导致停止：该勘误已记录并绕过。目标未翻，强归纳及四分支在显式
文献前提下全部闭合；不能虚报其中一项数学失败。原目标仍无无条件 kernel 证明，
不能报“成”。继续所需输入已明确为现成 Lean 声明，或允许移植论文前置的授权。

## 预登记与边界

目标仍为 n≥2 的 signed_nonsquashing_diff。第一档：OEIS 的已发表猜想。
拟议逃逸见证：对 r>0 的 B(4r)%2 + c(4r+1)=1，由强归纳产生，
四个差分分支活用该桥。准入拟为 escape-witness，非有限探针反例搭车。
定义域订正 n≥3 已获用户授权；attempt 1 的反例仍有效，但停止结算不沿用。
仅原目标反例、强归纳桥或差分分支真实不闭合可作数学停止理由。
不建理论卷，不 ingest，不造 atom；无 atom 的冻结入口为 deposit-uncovered
（内部 ledger-align --add）。不使用 sorry、私 axiom 或 native_decide。

## 第一批检索收据

- 已完整分段阅读 CLAUDE.md，截断处补读；已读 agents/CONTEXT.md 和 lean4 skill。
- 初始 HEAD=e9257083ef，基线沿用 82938786158c163b50350c14c948e63df61107a8；
  分支 lane/math/a110037，工作树干净。attempt 1 的报告、BoundaryProbe.lean、
  Sloane–Sellers PDF 提取 p6–8 均已打开阅读。
- D5/Library/Blueprint：rg 搜索 nonsquash、Sloane–Sellers、A110037、A073089、
  paperfold，仅命中 Library/Words/oeis2026triage0910.md；它是分诊散文，无 Lean 定理。
- 钉版 mathlib 全树：rg 搜索 non.?squash、paperfold、两个 A 号，零命中。
  attempt 1 已读 Partition.Basic/Glaisher/GenFun 公共面，报告可读且未重证。
- 本轮逐条读 ConvolutionRecurrenceOddPowersOfTwo 的公开面；convolution_pairing
  对任意 f:ℕ→ZMod 2 成立，但尚无本题分拆计数的卷积表示，不因此伪称可以引用。
- GitHub code search：`"non-squashing" language:Lean`、`"paperfold" language:Lean`，
  两次成功返回 []。D5/tools/lean-inspector/docs/reports 的 FromLiterature 三种拼写无命中。
- 已重新 GET OEIS 两个 internal 页面，HTTP 请求均 EXIT=0；逐字段读取在下批记录。
- 源论文 Corollary 4 (21) 收窄为 n≥3；Theorem 2 的奇项递推原有 m≥1。
  (22)/(23) 对 m≥0，(24) 的 printed m>0 将按原界使用，小边界另作私有核验。

## 待解决的前置输入

公开论文证明与已 elaborate 的 Lean 声明是不同工件。所搜范围内没有可直接 import 的
B 奇偶规则。用户同时禁止重证这部分和添加 axiom，故当前无法生成这一具体前置的
kernel 证明项；已异步请求具体 Lean 声明位置或允许移植已发表证明，继续独立完成桥。
此处不是目标反例，也不声称数学路线失败，不据此提前停止。

## 构建收据

make lean-cache-ensure EXIT=0：status=present，method=none，stamp_miss=null，
project_olean_state=warm，mathlib_olean_state=warm，clonefile_attempts=0，
mathlib_missing_olean_files=0；没有执行冷树裸 lake。
pin_sha256=sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e。

## 未主张

尚未证明主目标、尚未冻结、尚未开 PR。未主张全球检索完备、首创性或独立多模型共识。
未打开的页面和第三方链接均 ASSUMED-UNVERIFIED；用户有限读数不冒作本席新实测。
公开 theorem 当前为 0；proof_shape/direct_frozen_dependencies/escape_witness/
admission_basis 待实际证明后逐条记录，不用提前写的标签替代核验。

## 第二批来源读数

OEIS A110037/internal 完整条目已读：revision 9，2025-08-24；目标仍标 Conjecture，
归属 Alan Michael Gómez Calderón，2025-08-19。A073089/internal 完整条目已读：
revision 47，2021-03-13，独立八分支与用户一致。未打开其余链接，ASSUMED-UNVERIFIED。
重新 GET arXiv abstract 成功，原页 metadata 核出题名 On Non-Squashing Partitions、
作者 N. J. A. Sloane / James A. Sellers、日期 2003-12-22、DOI。
Library/Words 落点创建前 find -type f | wc -l=30；新增 note 不触容量上限。
note 的 Verified locator 正文逐字含 doi 与 url 两行，收录 n=1 kernel 见证与 n≥3 订正。
D5/S1/Recurrence 递归计数为99（含子桶），如需落 Lean 须再按直接文件数选子桶。

强归纳与 c 的分支已编码于 Bridge.lean，首轮热树检查已启动，尚未取得退出判词。

首轮检查现已完成：`lake env lean docs/reports/a110037-attempt2/Bridge.lean` EXIT=0。
c_four/c_four_two/c_eight_three/c_eight_seven/c_sixteen_five/c_sixteen_thirteen/
c_halving 均通过；complement_of_halving 由 strong_induction_on 对所有 r>0 证明。
这是无界归纳的条件数学结果，不是有限核对；仍不冒称具体 B 已满足输入。
`#print axioms complement_of_halving` 仅 propext/Classical.choice/Quot.sound。
首轮日志：attempt-2/bridge-first.log；本轮未采墙钟耗时，不填估算值。

## 无界桥与四差分分支已核验

`SloaneSellersParity B` 是显式的八项 Prop 输入，不是 axiom、不是已有 theorem、
也没有为具体 B 安装 instance。odd 字段只在 m>0 使用（n=2m+1≥3）。
两个 32 进展式的 m=0 输入对应 Corollary 4 最后一句的二进制位表征；
不把印刷 (24) 的 m>0 擅自去掉。

- parity_halving：按 r 偶数或 r≡1/3 mod4，引用上述输入，得 B(8r)%2=B(4r)%2。
- parity_complement：把 f(r)=B(4r)%2 送入已核验强归纳，得 r>0 时 f(r)+c(4r+1)=1。
- diff_four、diff_four_one、diff_four_two、diff_four_three：四个分支全部通过。
- signed_diff_of_parity：统一得对任意 n≥2 的差分式，但仍带 SloaneSellersParity B 前提。
- 原来的 n=1 printed_odd_rule_false 和目标 n=2/3 私有回声保留并通过。

第二轮 EXIT=1，35.38秒：diff_four 的整数 1 尚是 Nat.cast 1，linarith 未规范化；
合并分支时 convert/congr 未把 n=4*(n/4)+i 改写进函数参数，omega 不会推函数同余。
第三轮明确规范化 cast 1 并按指标等式改写，EXIT=0，14.88秒；所有新声明只含
标准三公理。第二轮失败产生的 sorryAx 是编译器错误恢复项，不是已核验结果；
第三轮完整日志不含 sorryAx。没有通过抬预算或加入 axiom 修复。

这是条件无界推导，不能替换用户要求的无条件具体计数定理；三条数学路线均已推进，
未把“未搜到现成定理”单独当作 blocked 结算，也未以有限实例声称部分进展。

## 具体目标的 Lean 实例化尝试

已把用户原签名逐字放入 runner 工件 InstantiationGap.lean，使用
`apply signed_diff_of_parity (fun k => (nonsquashingDistinctPartitions k).card) ?_ n hn`
后执行 `constructor`。EXIT=1，41.89秒，产生八个具体计数的未解 goal；
完整原文在 attempt-2/instantiation-gap.log，未将该失败文件加入 D5 或当成通过项。
例如首个 goal 精确为：

```lean
⊢ ∀ (m : ℕ), 0 < m →
    (nonsquashingDistinctPartitions (2 * m + 1)).card % 2 =
      ((nonsquashingDistinctPartitions (2 * m)).card % 2 + 1) % 2
```

最锐的缺口是闭合命题
`SloaneSellersParity (fun k => (nonsquashingDistinctPartitions k).card)`。
它的八个子句全部有论文出处；本席已证明其后续归纳与全部差分，并没有证明这八个
具体计数子句。现存禁令“不重证公开 B 奇偶定理”使本席不能自行移植论文证明，
而“无私 axiom”又不能用文献断言代替 kernel 证明项。具体 Lean 声明位置/移植授权
的异步问题仍未获答复；不把无答复当授权。

make lean EXIT=0，10.469秒，12840 jobs，本机 macOS ARM 热树。
该命令只构建现存 D5 项目；报告目录 Bridge.lean 的通过凭独立热树检查，
不是由本次 make lean 冒领。原始收据为 attempt-2/make-lean-receipt.json。

## 扩展 API 检索收尾

按 superincreas、binary.partition、distinct/partition 两种次序及 suffix/sum 粗筛
D5 与 mathlib Combinatorics/NumberTheory，再逐条读命中公共面：

- TrimmedAlternatingPartitions 的 sumsFrom、trimmedSums 与两条公开 theorem，
  其中通用 trimmedSums_nodup_iff_strict_tail 比较的是交错和与尾部严格递减，
  并未给出每部件≥后缀总和的计数。
- ZeroPrependedFirstSumsOddParts 的 IsZeroPrependedFirstSums 和两条基数 theorem，
  描述前缀变换的像到奇部件/互异部件分拆，未提供本题限制的传递定理。
- ConstantBlocksDistinctRunSums 的三个定义和两个公开 theorem，比较常值块和的
  互异性与排列后的 run sums，未给本题后缀不等式。
- SignedCatalanCubicSubstitutionModThree 的所有公开定义和 theorem 签名，
  唯一一般解唯一性定理有特定三次幂级数方程前提；无二进制分拆计数桥。
- 重新读 mathlib Partition.Glaisher 的全部公开面及 Basic 的 restricted、
  countRestricted、distincts、partitionWithPartEquiv 接口。它们能支持将来移植，
  但不能直接给当前八个 goal。没有根据文件题名排除它们。

首个扩展 rg 命令误含不存在的 Mathlib/Data/Nat/Partition 路径，诊断已显示；
随后在正确 Combinatorics/Enumerative/Partition 路径重查成功。未把坏路径零命中
算作检索证据。关键词粗筛不冒充符号依赖证明。

make lean-report EXIT=0，31.033秒，source-bound report 已产于
.lake/build/stratalint/raw-lean-report.json。候选报告不包含 docs/reports 的探针，
其通过不扩大成主目标已证明的主张。

make emit 首轮 EXIT=2，18.908秒；真实判词 invalid-doi：本仓 A12 要求 DOI/URL
二选一，note frontmatter 同时列两者被拒。修为仅 DOI，Verified locator 正文
仍保留 DOI 与访问 URL 的原文。此为叙事元数据修正，不是数学停止理由。

修正后 make emit EXIT=0，51.389秒；emitted=0 changed blueprints，工作树无新增
投影 diff。GitHub 额外检索 `"A088567" language:Lean`、`"nonsquashing" language:Lean`、
`"A073089" language:Lean`，全部成功返回 []；不作全生态不存在的断言。

## 声明级账目

公开 D5 theorem 为0，无冻结候选；下面连报告中的私有结果也列出，避免把条件定理
混成用户目标。所有行 direct_frozen_dependencies=[]（不存在可列的 GID/statement_id），
钉版 mathlib 依赖不冒作冻结依赖。以下 admission_basis=null 表示不申请冻结。

| 声明 | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| c_four, c_four_two, c_eight_three, c_eight_seven, c_sixteen_five, c_sixteen_thirteen, c_halving | bind-only | null | null |
| complement_of_halving | content | 对所有正 r 的具名强归纳构造本身 | null |
| parity_halving | bind-only | null | null |
| parity_complement | content | complement_of_halving | null |
| diff_four, diff_four_one | content | parity_complement | null |
| diff_four_two, diff_four_three | bind-only | null | null |
| signed_diff_of_parity | content，显式条件结果 | parity_complement | null |
| zero_one, target_at_two, target_at_three | content，private有限回声 | 相应具体 kernel 计算 | null |
| printed_odd_rule_false | content，private反驳 | n=1 的直接有限集合基数 | null |
| signed_nonsquashing_diff（用户原目标） | null，未证明 | null | null |

这里 c 分支和 parity_halving 是定义/输入的规范化；diff_four_two/three 只投影给定
奇偶前置并规范化。不是用同文件有反例来让这些结果取得新模块准入。
主目标拟议的 admission_basis 仍为 escape-witness，但尚未取得无条件证明，故未申请。

对条件结果 signed_diff_of_parity 的具名见证 parity_complement 逐项核对第3.2条：
1. 依赖闭包内：signed_diff_of_parity→diff_four/diff_four_one→parity_complement→
   complement_of_halving，最后核验直接读取 elaborate 后 proof term 的常量依赖。
2. 非投影可得：Corollary 4 输入仅含 B 的各分支，c 以独立递归定义；两者互补
   是对任意正指标的强归纳结论，不能靠有限次实例化已有分支产生全称桥。
3. 非定义等价：见证是正 r 上 B(4r)%2+c(4r+1)=1，结论是全部 n≥2 的有符号
   相邻差分；左侧对象和右侧递归各自独立，见证不是结论的别名。
4. 活推导路径：n≡0 与 n≡1 两支使用该互补关系分别消去 c 或计算奇项翻转；
   它不在被投影丢弃的合取中，删去归纳桥则这两支失去对 c(4r+1) 的控制。
   此项是证明项阅读与数学路径判断；常量依赖检测本身不冒作一般活性判官。

对 complement_of_halving 本身采用第3.2条允许的“结论由具名非绑定构造直接产生”
形态：strong_induction_on 是该构造，正偶数递归下降到 r/2、两个奇分支分别闭合；
不另造只为准入的中间引理。计算性私有回声不作普通正向实例冻结；原文反驳的
独立问题是 printedOddRule，目标差分不依赖它，本模块准入从未由它承担。

## 未主张（当前交付边界）

本席没有证明或反驳用户 n≥2 的原目标；没有证明具体 B 的 Sloane–Sellers 前置；
没有证明原目标已在文献中解决。强归纳与四分支已闭合，不把它们说成数学失败。
没有新增 D5、Blueprint、atom、coverage 或冻结状态片；没有 make deposit，
因为未取得主定理的 kernel 证明。没有开 PR，不用报告/条件桥的 PR 冒作原目标完成。
没有重建理论卷或反向摄入。所有未打开页面仍 ASSUMED-UNVERIFIED。

## 最终检查与可恢复工件

- Bridge.lean 最后含七条 elaborate 后依赖断言的检查：EXIT=0，40.504秒。
  五组 #print axioms 全为标准三公理；七条 ELABORATED_DEPENDENCY 全部出现。
  最后只调整文件说明注释，未改任何定义、陈述或证明项。
- scribe-content-checks：EXIT=0，13.318秒；BASE 精确为
  82938786158c163b50350c14c948e63df61107a8。实际执行 describe-report --check，
  summary red=0。该 delta 没有 Blueprint/Projection 变化，故脚本没有执行
  projections --check 或 markdown-check；不把路径判为无需执行冒称三项均真跑。
  既有全库 Observe 不变成本题错误，原日志完整保留。
- make lean EXIT=0 / 10.469秒；make lean-report EXIT=0 / 31.033秒；
  make emit 修正轮 EXIT=0 / 51.389秒。未运行 make preflight 或冷树裸 lake。
- 本轮新增仅 Library note、Bridge.lean 和本报告；attempt 1 工件仍在原目录。
  每个已验证单元、检索批次和报告修正均 commit + push 到 lane/math/a110037。
- runner 的 result.json 和 completion.sentinel 将由 worker 依次临时写入并原子改名。

本轮 make lean 的 LEAN_CACHE 原始收据：

```text
LEAN_CACHE {"status":"present","worktree":"/Users/chronoai/trureturing-a110037","donor":null,"method":"none","reason":null,"stamp_miss":null,"pin_sha256":"sha256:6c4c682ffba051b5744fe7a75ccc99d7f3b20227b3b026f392f3315be0adaa4e","clonefile_errno":null,"clonefile_errnos":[],"clonefile_attempts":0,"clonefile_cleanup_error":null,"mathlib_missing_olean_files":0,"mathlib_missing_olean_samples":[],"archive_status":"not_attempted","archive_mode":null,"archive_skip_reason":"project olean state is warm","archive_reason":null,"archive_producer_commit_sha":null,"archive_workflow_run_id":null,"mathlib_olean_state":"warm","mathlib_olean_probe_error":null,"project_olean_state":"warm","project_olean_probe_error":null}
```

## 数学推导的可读对应

以论文奇偶定理为已知数学前置，令 f(r)=B(4r)%2。r 偶数时用 (24) 的
B(16s)≡B(8s)；r≡1/3 mod4 时分别配对 (23) 与两个 32 进展式，得 f(2r)=f(r)。
奇 r 的两支与 c(16s+5)=1、c(16s+13)=0 互补，正偶数同时减半；强归纳即
f(r)+c(4r+1)=1。令 ε=r%2，其后的计算如下（0/1项均视为整数）：

| n | B(n)%2 | c(n)−c(n+1) | (-1)^(n/2) |
| --- | --- | --- | --- |
| 4r，r>0 | 1−c(4r+1) | 1−c(4r+1) | 1 |
| 4r+1，r>0 | c(4r+1) | c(4r+1) | 1 |
| 4r+2，r≥0 | 1−ε | ε−1 | −1 |
| 4r+3，r≥0 | ε | −ε | −1 |

这个表对应四条已核验私有 theorem，不是新增有限枚举。数学引用的合法性不改变
Lean 的事实：仍须给具体直接计数提供 SloaneSellersParity 的证明项。
