# OEIS A398189 implementation record

产地：`lean4` skill；Codex 主循环单席实施、单点自查，尚无独立评审。
用户转述的 orchestrator/分诊席读数不冒充本席亲验。
工作树 `/Users/chronoai/trureturing-a398189`，分支 `lane/math/a398189`。
初始 base：`343718ed191002a4708ccf381081f9b0c7a58e1a` (`origin/dev`)。
以下按时间顺序保留工作记录；早期「尚未」状态以文末的最终收据为准。

## 预登记与边界

第一档。目标是定义中的自然数截断和
`S(n,k) = ∑ j ∈ range (n-k+1), (n-k)! / j! * n^j`，
奇 `n ≥ 1`、`1 ≤ k ≤ n` 时：奇 k 的二进估值为零；
偶 k 且 `k % 16 ≠ 14` 时估值为 `padicValNat 2 (k+2)`。
不把 `k=0` 或偶 n 已证背景当成剩余目标。

拟议见证沿用 brief：递推 `H₀=1`、`Hₘ=n^m+m Hₘ₋₁` 六步展开，
连续六个整数的乘积模16消失，奇数幂的模16周期，以及向全部参数的提升。
该见证尚未 Lean 编译；56/45 个格子的上游结构探针为 ASSUMED-UNVERIFIED。
有限枚举只作私有余数引理或探针，不能单独冻结。
停止条件：目标范围的精确反例、找到剩余公式的已有证明、或只剩已证背景。
无 atom；不新造理论卷、不 ingest。使用现役无 atom 冻结入口。

## 检索收据（持续追加）

1. 本仓 D5/Library/Blueprint/docs：`rg -n -i 'A398189|A063170|Schenker|Amdeberhan|truncated.*(factorial|exponential)'`。
   未命中目标；命中的是其它截断指数估计与文献分诊条目。
   按文件名筛出 factorial/valuation 模块，公开面阅读待完成。
2. 钉版 mathlib、第三方 Lean 生态与文献：待完成，不作 search-complete 主张。
3. 已下载 OEIS A398189 internal HTML；论文下载中，尚不主张已读。

## 声明与门收据

尚无新增公开定理；`proof_shape`、直接冻结依赖（GID/statement_id）、
`escape_witness`、`admission_basis` 待真实证明后逐条填写。
尚未跑 Lean；无构建成功主张。最终须记录 `LEAN_CACHE`、make lean 退出码/耗时、
lean-report、emit、Scribe 内容检查及 freeze 收据。

## 未主张

未主张 `k ≡ 14 mod 16` 例外公式；未主张有限核对证明全称；
未主张 A063170 的已证性解决剩余目标；未主张已解决、已冻结、已开 PR 或已合并。
所有未真正打开的外部页均为 ASSUMED-UNVERIFIED。

## 第二批亲读收据

- 已完整读 A398189 及其全部直接序列引用 A398187、A063170、A000120 的 internal 条目；主条目唯一论文链接的摘要入口亦打开。
- Amdeberhan–Callan–Moll，Integers 13 (2013) A21，16 页全文已逐页提取阅读，另亲看第5页原图。§2 pp4–5 证明 k=0：奇 n 估值1；偶 n 估值 n-s₂(n)。Lemma 2.2 的式(2.11)–(2.14) 给正 j 项相对零项的严格估值差 s₂(j)+j v₂(n/2)>0；截到 n-k 并缩放后仍给所有偶 n 背景。§3–4 讨论 k=0 的奇素数估值，§5 为 Abel/树组合恒等式。未见奇 n、正 k 的目标公式证明。
- 文献裁决（按 brief 原边界）：k=0 已证、所有偶 n 分支为已证背景；未因 A063170 已证而降低剩余目标档位。未打开直接引用条目所进一步引用的二级文献，均 ASSUMED-UNVERIFIED，不作为判据。
- 本仓候选模块公开面：FactorialQuotientRecurrence 的 positivity/triple-product/Mathar recurrence 针对另一递推；FactorialProductSumCatalanParity 的一般系数消失、唯一性、模2函数方程与 Catalan support 不提供本截断和递推或估值。未发现可直接复用的目标/抵消引理。
- 钉版 Mathlib `rg -i 'schenker|truncated.*exponential|A398189|A063170' Mathlib` 零命中；`PadicVal/Basic.lean` 提供 `padicValNat.eq_zero_of_not_dvd`、`padicValNat_dvd_iff_le` 等通用估值接口，不提供抵消。Lean pin 已对齐。
- GitHub code search 实测可用：`Schenker language:Lean`、`A398189 language:Lean`、`"truncated exponential" language:Lean` 均 total_count=0。搜索范围无命中并不阻塞本地证明。
- `make lean-cache-ensure`：`status=seeded, method=clonefile, clonefile_attempts=1, stamp_miss=null, mathlib_olean_state=warm, project_olean_state=warm`；原始收据 `/tmp/a398189-cache.log`。
- 首次报告目录计数为48；已把本题报告放入独立任务子目录，未向已满的平桶继续添加文件。

## 首个 Lean 单元

热树 `lake env lean /tmp/A398189.lean`，修正 `Nat.div_self` 要求正数（而非非零）后 EXIT=0。
已验证全称 `h_sum`（任意 n,m 的定义求和/递推等价）、`six_zero`（模16连续六因子为零）与 `six`（任意 n,m 的六步截断恒等式）。
尚未得到目标估值公式；这不是把有限核对算作目标进展。
检索更正：英文 `"truncated exponential" language:Lean` 实际 total_count=1，前段写0是并行结果到达前的记录错误。
命中 `kim-em/hex-dev/HexTruncatedSeriesMathlib/Newton.lean` 的 `ofPowerSeries_exp`，已读声明及上下文；
它陈述形式幂级数截断与可执行 exponential 的交换，不是整数截断和抵消/估值公式。

第二个已编译单元：`val_mod`、`odd_four`、`odd_pow`、`large_table` 全部 EXIT=0。
`odd_pow` 直接使用 Mathlib `pow_eq_pow_mod`，未重建已有周期接口。
`large_table` 为私有有限环引理，`decide +kernel` 经 kernel 归约，不用 native_decide；尚须全称提升。
当前 Lean 源同步保留这些单元；无首次冻结，最终目标仍待完成。

## 目标证明闭合（正式门之前）

`all_residues` 与 `full_val` 通过，把 m≥6 的六步式与 m<6 的短截断式覆盖全部参数；
`odd_positive_branches` 同时证明 brief 两分支。热树文件编译 EXIT=0，
`#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`。
完整落地门尚未运行，不把此文件级成功称作交付完成。
正式落点按 route 调整到 `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic`：
Congruence 桶原有 Lean 21 / Blueprint 42 文件；Library/Arith 已满48，注记放 ArithSums（原9）。
原 Arith 平桶的临时未冻结模块移走；未改任何已冻结模块。

## 逐声明判形与用途

- `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.S`：定义，非定理，proof_shape 不适用；直接冻结依赖 `[]`；escape_witness `null`。自然除法的范围由 `h_sum` 中阶乘整除证明连接到递推。
- `D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.odd_positive_branches`：`proof_shape: content`；直接冻结依赖 `[]`（无 D5 imports，因此无 GID/statement_id 对）；`escape_witness: six`；`admission_basis: escape-witness`。
  见证逐项：① `six` 在 `odd_positive_branches → full_val → all_residues → six` 的已编译常量依赖中；
  ② 任意 n,m 的模16六步抵消式由递推展开及连续六因子零式新建，冻结前置为空，不是冻结公式的实例/投影；
  ③ 它是 ZMod16 中递推值与六项多项式的等式，既不是自然数估值结论的定义等价，也不是别名；
  ④ m≥6 分支用它改写实际的 H 值，后续取 val 再用 val_mod 得精确估值，不是死项或丢弃分量。
  奇 k 子句通过同一全称估值链和 k+2 奇性得到零；没有旁路只用 Legendre 公式。

`utility: none`：唯一公开定理量化无上界的 n,k，新增内容是递推消尾、周期和全称提升；
不是有界实例集合、检查器 API、附带未履行数值前提的归约或普通正向实例。
有限环与短长度枚举全部 private，并在全称证明的实际分支内使用；不独立冻结、不作为数值范围推进。
consumer/instance/premises/result/claim 均为 not-applicable(kind=none)。
`generality: I` 的具体性是二进估值和模16，不主张推广到任意素数。

question_answered：本报告开头预登记的 A398189 奇 n、正 k 两分支，含模16例外边界。
dominating_theorem_search：本仓 → pin Mathlib → GitHub Lean/OEIS/指定论文，not-found-in-searched-scope；
已证背景与未读二级文献的边界见上。形态 deposit，无 source_id/atom_id，不做 cover。

## 正式构建首轮

`make lean` EXIT=0，72.072 s；本机 macOS ARM，pin 不变，双层热缓存。
本模块增量构建行 `Built D5.S3.Arith.Congruence.TruncatedExponentialTwoAdic (7.8s)`；
全项目 `Build completed successfully (12845 jobs)`。make receipt 在 runner attempt 的
`make-lean.receipt.json`，完整原始日志 `make-lean.log`。
LEAN_CACHE：`status=present, method=none, stamp_miss=null, clonefile_attempts=0,
mathlib_missing_olean_files=0, mathlib_olean_state=warm, project_olean_state=warm`。
这次没有重新播种；最初显式 ensure 的 seeded/clonefile 收据见前文。

首轮 `make lean-report` EXIT=0，增量计划 added=3/recheck=3；
原报告 hash `66c733ba1c4b9d6586bb89eaefca7f3083f7827302c41b484a09b12550ec3fd9`。
编译器指出本模块三处 whitespace warning；仅补空格和声明间距，
因此按最终字节重跑 lean → lean-report，旧轮成功仍仅作为旧字节的历史收据。

最终 Lean 字节的 `make lean` EXIT=0，11.308 s；本模块 whitespace warning 已消除。
两份首轮/最终轮收据均保留，不把 72.072 s 说成最终增量成本。
语义回声 `/tmp/A398189Echo.lean` 已编译：按定义 S(9,4)=112494，
用公开定理推出估值1；端点 (1,1) 亦由公开定理推出估值0。回声不入冻结模块。
开 PR 前再查 base：origin/dev=`45ca4ae3b012cb1f59ff74a84e845691a3f0c99c`，
merge-tree 无冲突，合成树 `c709569368d43dd4b4936158bc4364c3454cec50`；
本轮更新的 dev D5/Library/Blueprint 搜索未见目标重复。原构建基线未变更。

## 最终报告与 Scribe 修复

最终字节 `make lean-report` EXIT=0，61.098 s。
公开定理 statement_id 为 `sha256:2e736644e8d10de8ac10b8f0119891f2e59157d3122789f10da2fede6452aa8a`，
axiom 闭包仍只有 Classical.choice、Quot.sound、propext。
首轮 `make emit` EXIT=2，8.137 s：`FromLean` 报 `missing:...TruncatedExponentialTwoAdic.S`。
已读 projector 实现：它只消费两份固定 Golden/Projection fixture，不能从新 raw report 动态投影；
且 def 的 type 不含定义体，本来应走 authored presentation。
因此两处改为现役 FromAuthor，写完整自然数求和定义和带全部前提的两分支公式，
由 Scribe 自动记录 projection gap。未改 projector、fixture、Lean 或任何门槛。
早先 GitHub 第三查询的正确读数是1（已更正），不是0；后续阅读已排除该命中。

手写 Formula 首次补写有一个 C# 右括号遗漏，第二次 emit 编译失败；补齐并将分支公式拆成局部变量后，
`make emit` EXIT=0，85.984 s。生成的数学式已逐项对照 Lean 陈述。
首轮内容检查 EXIT=1，32.563 s，唯一 RED 为 `code=suspected-novel`：
`production Describe corpus must not contain suspected-novel nodes`。
按 CLAUDE §3.7 的「确系本仓推导 → repo-derived」，改用 FromRepo 并明确这是本模块内的证明，
同时保留 OEIS 猜想出处、全部检索收据和第一档定位；没有声称文献已经证明剩余目标。
文献新颖性仍仅为搜过范围内未发现已有证明，不作全球优先权主张。

最终 Scribe 字节 `make emit` EXIT=0，76.486 s。
最终 Lean report 的 SHA-256 为 `ccf0b90ac6958b535551bbfdf45a9ea5a375fed8743acc7acb99bd1d2807445f`；
报告输入地址为 `sha256:11283650196375dc7d1fb37295d23ce38e371c32e4986cb390e8071e72450571`。

`scribe-content-checks.sh <report> "" <初始40位base>` 最终 EXIT=0，25.616 s；
describe-report 无 RED，真 KaTeX 判词 `markdown: judged=1 formula(s)=2 red=0`。
projections --check 按脚本变更面判定未触发（本席没有改 Golden/Projection 或 projector）；
没有把该未触发子项冒称运行成功。FromAuthor 的 missing projection gap 是显式 OPEN 展示能力，
不影响 Lean 内核已证状态或原始 statement_id 的声明绑定。

## 冻结完成

`make deposit-uncovered GID=D5/S3/Arith/Congruence/TruncatedExponentialTwoAdic.odd_positive_branches
BASE=343718ed191002a4708ccf381081f9b0c7a58e1a` EXIT=0，92.742 s。
此入口按序复用同输入的 lean-report、检查头、emit，再执行 `ledger-align --add`。
`LEDGER_ALIGN selectors_considered=3959 changed=0 added=1 unchanged=3958 conflicts=0`；
`PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED ... reason=NO_ATOM` 是本题无 atom 路径的成功判词。
模块冻结 statement_id：`sha256:f4ac79eb3331d669eb36b6e73501e5acf62ce5c5de1e7ac7d93cb745f5430a04`；
公开定理 statement_id 保持上文 `sha256:2e736644e8d10de8ac10b8f0119891f2e59157d3122789f10da2fede6452aa8a`。
接受事件：`Golden/Frozen/accepted/c9afbf1136a213d622f37bbf714f338caba8243879b3fdeb78bce16a165c23a4.json`。
没有理论卷、atom 或 backfill 变更。未把私有余数枚举另做公开正向实例。
