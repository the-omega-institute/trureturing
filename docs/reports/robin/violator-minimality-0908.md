# Robin 违例数的极小性: bind-only 停止报告

skill: consensus-rnd:sshx
producer: one codex-cli implementation worker
independent_review: ASSUMED-UNVERIFIED
stage: implementation
verdict: no-verdict-required
lane: https://github.com/the-omega-institute/trureturing/issues/6160
branch: lane/math/robin-violator-0908

## 结算与范围

第一条硬要求的首次受限 Lean 尝试成功，`proof_shape: bind-only`。
因此停止数学实施，不建新的 D5 模块，不 deposit，不新增 Scribe、冻结状态片或 coverage。
唯一 tracked 交付为本报告。本报告中的源码是归档，不是新冻结节点。

预登记来源是本次用户 brief 的第一条硬要求及主定理语句。
`question_answered`: 给定一个在 5040 以上的最小 Robin 违例数 n，是否能只靠
钉版 Mathlib 实例化、逻辑投影/重组和规范化得到
`∀ m, 5040 < m → m < n → σ(m)/m < σ(n)/n`？答案是能。
本次无需 `sq_nonneg` 或 `linarith only`；许可操作集的更小子集已经闭合。
没有失败目标，没有编译修复轮，不能为继续 deposit 虚构失败诊断或逃逸见证。

构建起点 HEAD 为 `1a27fa2561a800fca52ddaaa48967b687d92ac35`。
检索所用 `origin/dev` 为 `6afda94321f0df5090c2ea0a531b793455d922e0`，
开始及结束读取一致；二者 diff 只有 `Library/notes/pntplus2026mertens.md`，
本次检索的 D5 源码在两个修订相同。Lean 为 `leanprover/lean4:v4.33.0`，
Mathlib pin 为 `db584cd6d46c92f209a44c0f1c829460d327499d` (`v4.33.0`)。

`violates_robin_iff_margin_nonpos` 与素数赋值无界伴随的实施状态都是
`not-attempted(first-requirement-stop)`，不声称它们已被本轮证明或判形。
brief 为后者预登记的边仍是“违例数赋值无界 → bounded_prime_valuation_robin_margin_gap”
(消费者 → 前置)，本轮没有把这条拟议边写成冻结事实。

## 逐声明判形

本轮归档中只定义一个谓词并证明一条公开定理，均在 `RobinViolatorBindOnly` 命名空间。

| 声明 | proof_shape | 直接冻结依赖 (GID + statement_id) | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| `ViolatesRobin` | not-applicable(definition) | `[]` | none | not-applicable(no deposit) |
| `least_violator_abundancy_above_5040` | bind-only | `[]` | none | none: mandatory bind-only stop; no exception claimed |

直接冻结依赖为空不是漏填：本证明不调用任何 D5 定理。
实际用到的分析结果来自钉版 Mathlib，按第 3.2 条不列入冻结前置。
原构建根的既存 D5 imports 出现在完整编译输入中，不充当本证明的前置。

展开局部别名和 tactic 后，承重步骤如下：

| 步骤 | 来源与判形 |
| --- | --- |
| m 和 n 的实数正性、`1 < (m : ℝ)`、`(m : ℝ) < n` | 给定自然数不等式，常量规范化与 `exact_mod_cast` |
| `hsmall`: `σ(m)/m < exp γ * log(log m)` | 应用 `hmin m hm hmn`，逻辑重组 `⟨hm, h⟩`，`lt_of_not_ge`、`div_lt_iff₀`、`mul_right_comm` |
| `hlarge`: `exp γ * log(log n) ≤ σ(n)/n` | `hn.2`、`le_div_iff₀`、`mul_right_comm` |
| `hlog`: `log(log m) < log(log n)` | `Real.log_pos` 和两次直接实例化 `Real.log_lt_log` |
| 主结论 | `Real.exp_pos`、`mul_lt_mul_of_pos_left`、严格/非严格序的传递性 |

`hlog` 不能充当逃逸见证，因为它完全由上游引理实例化得到。
`hsmall`、`hlarge` 也只是逻辑和有正分母的规范化；没有新的数论估计、
有限计算或独立构造。判形是本 worker 的语义判断，Lean kernel 验证命题，
不把编译成功冒充仓库已有判形机器或独立评审。

## 逐声明 Utility

| 声明 | utility | 为何不命中四类计算性内容 |
| --- | --- | --- |
| `ViolatesRobin` | none | 是对任意自然数的符号谓词定义，无有界枚举、检查器/反射基础设施、数值归约或已认证具体实例。 |
| `least_violator_abundancy_above_5040` | none | 是对任意 n、m 的条件式一般定理；未穷举有限域，未实现 checker，未归约到待履行的数值前提，未认证某个给定 n。 |

其余计算性用途字段为 `not-applicable(kind=none)`。
证明中规范化 `0 < 5040`、`1 < 5040` 不使交付语义成为数值实例。
没有采用 `certified-instance` 或 `bounded-enumeration`，
也没有利用 consumer/terminal 标签规避“普通有限实例只能走经验证 refutes”的限制。
本次不 deposit，故没有需要 SL-031 头部的新增 Lean 内容文件。

## 撞题收据

以下命中数都是匹配行数，不是声明数。阴阳对照同用 `git grep -P` 的
`\b` 词边界；没有使用 `-E` 冒充支持相同正则特性。

| 检索 | 命中行数 | 结论 |
| --- | ---: | --- |
| 原始大小写敏感超丰名阴性 | 0 | 没有该拼写；不能把它解释成没有小写注释 |
| 原始违例名阴性 | 0 | 未命中 |
| `IsColossallyAbundant` 阳性 | 7 | GoldenColossalClosure 3 / GoldenDepthForcesPrimeSupport 1 / GoldenResourcePriceInterval 3 |
| 超丰名加 `-i` | 7 | 全为注释或检索留痕，没有定义 |
| 违例名前缀加 `-i`、`\w*` | 0 | 扩大拼写后仍未命中 |
| 指定族的词边界阴性 | 7 | 全为 superabundant 注释/检索留痕 |
| 同一指定族、同一 `-i -P` 的阳性 | 7 | 与全 D5 阳性分布一致 |

原始三条命令：

```sh
git grep -n -P '\b(IsSuperabundant|Superabundant)\b' origin/dev -- D5
git grep -n -P '\b(RobinViolat|robin_violat|least_violat|violates_robin)\b' origin/dev -- D5
git grep -n -P '\bIsColossallyAbundant\b' origin/dev -- D5
```

扩大后的成对命令及全 D5 补查：

```sh
git grep -n -i -P '\b(IsSuperabundant|Superabundant|(RobinViolat|robin_violat|least_violat|violates_robin)\w*)\b' origin/dev -- 'D5/S3/Arith/GoldenResource*' 'D5/S3/Arith/RobinExponentSwap.lean' 'D5/S3/Arith/ExponentExchange/IntegerSwap.lean' 'D5/**/*GoldenCell5040*'
git grep -n -i -P '\bIsColossallyAbundant\b' origin/dev -- 'D5/S3/Arith/GoldenResource*' 'D5/S3/Arith/RobinExponentSwap.lean' 'D5/S3/Arith/ExponentExchange/IntegerSwap.lean' 'D5/**/*GoldenCell5040*'
git grep -n -i -P '\b(IsSuperabundant|Superabundant)\b' origin/dev -- D5
git grep -n -i -P '\b(RobinViolat|robin_violat|least_violat|violates_robin)\w*\b' origin/dev -- D5
```

另查 `GoldenCell5040Certificate`：

```sh
git grep -n -P 'GoldenCell5040Certificate' origin/dev -- D5 Blueprint Library docs
git ls-tree -r --name-only origin/dev -- D5 Blueprint | rg -i '(GoldenCell.*5040|5040.*Certificate)'
```

前者 3 行，分别在 `RobinRationalBasis.lean`、其 Scribe 和发射 md 的叙述中；
后者 0 条路径。当前被检修订没有这个名称的模块，不能把这些文字当作声明。
实际的 `robinLogMargin` 所有者是 brief 指出的 `GronwallLowerEnvelope`。
已读取的四个冻结状态片路径均存在；它们未用于本次主证明。

扩大检索还使用
`git grep -l -P '(GoldenResource|RobinExponentSwap|ExponentExchange\.IntegerSwap|GoldenCell5040Certificate)' origin/dev -- 'D5/**/*.lean'`，
得到 31 个文件候选，并核读相关公开语句：
`GoldenResource*` 的全局最优性是
`log(σ(n)/n) - lambda * log n` 在给定价格下的最优性；
`colossally_abundant_iff_price_interval_nonempty` 是巨丰性的价格刻画；
`reciprocal_geom_sum_swap_strict` 与 `prime_exponent_swap` 是素数指数交换，
后者还给出一个特定较小整数及其丰性改进。
这些语句的前提和比较域与本靶不同，没有把其中任一条重新证明成别名。
`RobinRationalBasis.robinPositiveJudge_sound` 是有数值区间前提的正 gap 检查器，
`robin_delta_10080_pos` 是特定实例，也不是本靶。
`dominating_theorem_search: not-found-in-searched-scope`；
这不是机器证明“全库不存在任何等价语句”。

## 上游与文献

Loogle 的 HTTP JSON 接口实测可用；未改动宿主 Codex 配置。
联网索引不能替代本地 pin，故同时读取钉版源码核对：

| 查询 | Loogle count | 判断 |
| --- | ---: | --- |
| `"Robin"` | 0 | 无此名字 |
| `"superabundant"` | 0 | 无此名字 |
| `ArithmeticFunction.sigma, _ ≤ _` | 7 | `sigma_mono` 比较 k 与 k'，并非随 n 的丰性单调性 |
| `ArithmeticFunction.sigma, _ / _` | 7 | 除数和/q-expansion 结果，未找到本靶或其一般化 |

调用分别为
`curl --max-time 30 -sS --get --data-urlencode 'q=<查询>' https://loogle.lean-lang.org/json`。
原始查询及响应存于 attempt 目录的 `search-receipts.json`。
本地补查
`rg -n -i '(robin.{0,40}(inequal|criter|violat)|superabundan|colossally.abundan)' .lake/packages/mathlib/Mathlib`
为 0 行。钉版 `Misc.lean` 中的 `sigma_mono` 语句为
`(k k' n : ℕ) (hk : k ≤ k') : sigma k n ≤ sigma k' n`。
实际复用的 `Real.log_lt_log` 在
`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:155`，
`Real.strictMonoOn_log` 在同文件 249 行。

档位为第三档，核心问题为 Robin 判据 / 5040 / RH。
交付只是一条经典观察的形式化地形记录，不是新数学，不是开放问题的解决。

文献核对于本轮联网完成：
[Wolfram MathWorld, Robin's Theorem](https://mathworld.wolfram.com/RobinsTheorem.html)
明确列出 5040 是 Robin 不等式的例外，并引用
G. Robin, “Grandes valeurs de la fonction somme des diviseurs et hypothèse de Riemann”,
J. Math. Pures Appl. 63, 187–213 (1984)。
[Superabundant number](https://en.wikipedia.org/wiki/Superabundant_number)
将“不限比较范围的最小反例是超丰数”引至
A. Akbary and Z. Friggstad, “Superabundant numbers and the Riemann hypothesis”,
American Mathematical Monthly 116(3), 273–275 (2009),
[DOI 10.4169/193009709X470128](https://doi.org/10.4169/193009709X470128)。

出处边界须分清：已核对上述在线二手文献及其书目信息；
没有读到 Robin 1984 原文中本靶的具体引理编号，
brief 的该项精确归属记 `ASSUMED-UNVERIFIED`。
2009 引文涉及更强陈述，本轮没有形式化它，不能据其名称扩张 Lean 结论。
初始 Crossref 宽查询返回了 Robin 1983 的另一篇论文，已排除为误命中；
尝试的 Numdam 路径返回 “Page inexistante”，没有拿它作原文验证。
这不影响本轮主定理的实际 Lean 检验。

## 5040 边界与未主张

结论只在 `5040 < m < n` 上成立于本次论证。
brief 中 orchestrator 给出的读数为
`σ(5040)/5040 = 19344/5040 = 3.83809…`，
`exp(γ) * log(log 5040) = 3.8164…`；
因此 5040 本身不满足 Robin 的严格不等式。
这些小数是 brief 的已给读数，不冒充本 worker 的独立数值复算。

按本次带有定义域门槛的 `ViolatesRobin` 定义，
`ViolatesRobin 5040` 本身为假，因为它还要求 `5040 < 5040`；
“5040 自己违例”只指不带域门槛的 Robin 不等式失败。
极小性前提不能用于 m ≤ 5040，本证明的 `hsmall` 在该处没有来源。
因此准确表述为“在 5040 以上超丰”，不是通常意义下的“超丰”。
本报告只说不能由此论证扩域，不宣称扩域陈述在数学上为假。

明确未主张：

- 未证 RH。
- 未证 Robin 判据。
- 未证“最小违例存在”。
- 未把结论扩到 m ≤ 5040。
- 未主张 5040 以上存在任何违例数。
- 没有报告新数学结果或解决开放问题；本轮定理全为条件式。

orchestrator 的亲验范围只采用 brief 所列：
冻结件位置与语句、既有撞题读数、上述两个 5040 数值和主定理纸面骨架。
Lean 编译、公理输出、扩大的检索与本报告均由本 worker 自跑；
零评审席，无独立评审结论，无多模型共识。

## 构建与公理

唯一 Lean 编译命令：

```sh
/usr/bin/time -l make lean > /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/robin-violator-0908/attempt-1/bind-only-make-lean.log 2>&1
```

| 读数 | 值 |
| --- | --- |
| local_make_lean_EXIT | 0 |
| Lake build jobs | 12585 |
| 实际新增编译项 | `Built Trureturing (30s)` |
| real / user / sys 秒 | 41.97 / 11.54 / 51.19 |
| maximum resident set size | 5880266752 bytes |
| 宿主 | macOS, Mac15,14, 28 logical CPUs, 103079215104 bytes RAM |
| cache | present; method=none; project=warm; mathlib=warm; stamp_miss=null |

12585 是 Lake 报出的构建任务数，不是同时运行的进程数。
本轮未传并发覆盖参数；实际并发进程数未采样。
RSS 采用 macOS `/usr/bin/time -l` 的原始字节数，不套用 Linux 的 KiB 换算。
日志含既存模块的回放信息和警告，不把它说成“全仓零 warning”。
未提高 `maxHeartbeats` / `maxRecDepth`，未改任何数学或构建常数，
未执行裸 `lake build` / `lake env lean`。

实际 `#print axioms` 输出：

```text
'RobinViolatorBindOnly.ViolatesRobin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RobinViolatorBindOnly.least_violator_abundancy_above_5040' depends on axioms: [propext, Classical.choice, Quot.sound]
```

主定理没有 sorry 或新增 axiom。没有运行 `make lean-report`、deposit、admission 或 PR CI：
第一条停止规则选择的是源码归档报告，本轮没有新的 D5 准入对象。
`make lean` 通过只证明所归档输入编译成功，不冒充三 required check 或冻结准入通过。

## 源码逐字节归档

下面单个 Lean 代码块是本次实际编译的完整 `Trureturing.lean` 输入，
包括原有 imports 和临时追加的受限证明；保留 UTF-8、LF 和末尾换行。
其 SHA-256 为
`d97c98e9bfb54e5fd99e76402b3f7575264b99353a95339f093d6386b6731106`。
构建通过后只撤去本 worker 的临时追加，`git diff --exit-code -- Trureturing.lean` 为 0。

独立的证明后缀存于 `/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/robin-violator-0908/attempt-1/bind-only-attempt.lean`，
41 行、1747 bytes，SHA-256 为
`5384739bf2ecf085e8d567bdddb846df937be7ab1d62cbcd3a53262931589e57`。
该后缀在下面完整输入内逐字节出现，未声称另做过一次独立文件编译。

```lean
import D5.S0.Carrier.Ring
import D5.S0.Carrier.Conj
import D5.S0.Carrier.Norm
import D5.S0.Carrier.Units
import D5.S0.Conventions.WDigits
import D5.S0.Conventions.Notation
import D5.S0.Diagonal.EscapeCount
import D5.S0.Diagonal.CaptureCount
import D5.S0.Diagonal.DistanceProfile
import D5.S0.Diagonal.MarginBound
import D5.S0.Diagonal.MarginVanishing
import D5.S0.Diagonal.EscapeAsymptotics
import D5.S0.Diagonal.EquivariantEscape
import D5.S0.Naming.NamingSystem
import D5.S0.Tower.ConstantArms
import D5.S0.Tower.ChampionExtremality
import D5.S0.Tower.GoldenGapFrequency
import D5.S1.Digit.Raw
import D5.S1.Digit.Carry
import D5.S1.Words.GoldenGapPrefix
import D5.S1.Words.GoldenWord
import D5.S1.Words.GoldenBalance
import D5.S1.Words.GoldenDensity
import D5.S1.Words.GoldenSubstFixed
import D5.S1.Words.ReturnWords.GoldenGapFirstReturn
import D5.S1.Words.ReturnWords.GoldenArcFirstReturn
import D5.S1.Words.Palindromes.GoldenPalindromicFactorComplexity
import D5.S1.Scale.Embedding
import D5.S1.Scale.Log
import D5.S1.Phase.Basic
import D5.S1.Phase.SeatTowerArithmetic
import D5.S1.Phase.SeatTowerCombinatorics
import D5.S1.Phase.SeatTowerConsequences
import D5.S1.Depth.StationingCombinatorics
import D5.S1.Depth.TwelveScaleReduction
import D5.S1.Depth.PartialQuotientExtraction
import D5.S1.Phase.WalkFormula
import D5.S1.Phase.ZeroOrbitCongruence
import D5.S3.Constants.MidslopeCurvature
import D5.S3.Constants.MidslopeCurvatureValues
import D5.S3.Constants.RecordEntropy
import D5.S3.Divergence.LogDerivTrace
import D5.S3.Quantum.EnvironmentRecords
import D5.S3.Quantum.ObserverCommutator
import D5.S3.Quantum.PointerBasis
import D5.S3.Quantum.CloningMachine
import D5.S3.Zeros.ZetaIdentities
import D5.S3.Zeros.ZetaUpgrade

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum

namespace RobinViolatorBindOnly

def ViolatesRobin (n : ℕ) : Prop :=
  5040 < n ∧ Real.exp Real.eulerMascheroniConstant * n *
    Real.log (Real.log n) ≤ (ArithmeticFunction.sigma 1 n : ℝ)

theorem least_violator_abundancy_above_5040 {n : ℕ}
    (hn : ViolatesRobin n)
    (hmin : ∀ k : ℕ, 5040 < k → k < n → ¬ ViolatesRobin k) :
    ∀ m : ℕ, 5040 < m → m < n →
      (ArithmeticFunction.sigma 1 m : ℝ) / m <
        (ArithmeticFunction.sigma 1 n : ℝ) / n := by
  intro m hm hmn
  have hm1 : (1 : ℝ) < m := by
    exact_mod_cast (lt_trans (by norm_num : (1 : ℕ) < 5040) hm)
  have hm0 : (0 : ℝ) < m := zero_lt_one.trans hm1
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℕ) < 5040) hn.1)
  have hsmall : (ArithmeticFunction.sigma 1 m : ℝ) / m <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log m) := by
    apply (div_lt_iff₀ hm0).mpr
    have h := lt_of_not_ge (fun h => hmin m hm hmn ⟨hm, h⟩)
    simpa only [mul_right_comm] using h
  have hlarge : Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) ≤
      (ArithmeticFunction.sigma 1 n : ℝ) / n := by
    apply (le_div_iff₀ hn0).mpr
    simpa only [mul_right_comm] using hn.2
  have hlog : Real.log (Real.log (m : ℝ)) < Real.log (Real.log (n : ℝ)) :=
    Real.log_lt_log (Real.log_pos hm1)
      (Real.log_lt_log hm0 (by exact_mod_cast hmn))
  exact hsmall.trans
    ((mul_lt_mul_of_pos_left hlog (Real.exp_pos _)).trans_le hlarge)

#print axioms ViolatesRobin
#print axioms least_violator_abundancy_above_5040

end RobinViolatorBindOnly
```

## 交接

本次提交/推送只含本报告；完整提交 SHA 在推送成功后记录于
`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/robin-violator-0908/attempt-1/result.json` 的 `conclusion.pushed.commits`。
未开 PR，后续 PR 由 orchestrator 处理。
`completion.sentinel` 由 worker 在严格 JSON 结果原子发布之后原子发布。
