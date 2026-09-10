# Robin judge 下一格量测报告（2026-09-11）

本轮先做精确有理量测，再决定是否实施。没有新增 Lean 模块，也没有重做已有的 `n = 10080` 实例。

## 量测范围与方法

有限纤维取

```text
2^a 3^b 5^c 7^d，0 ≤ a < 17，0 ≤ b < 11，0 ≤ c < 8，0 ≤ d < 7，5040 < n < 131072。
```

去重后共有 **482** 个 `n`。判词直接按 `RobinPositiveJudge` 的 `Decidable` 实例计算；γ、`logLog` 端点、幂、阶乘和截断指数全部使用 `ℚ`，没有浮点运算。Lean 复核脚本输出依次为：`482`、`480`、`480`、`482`，以及失败集合 `[7560, 75600]`。

实验用的 `logLog` 下界沿用仓内已证明的分段下界：`1071/500`（5040–9999）、`111/50`（10000–19999）、`229/100`（20000–131071）；上界只用于满足区间一致性。它们来自 `SevenSmooth.lean` 的 `loglog_5040`、`loglog_10000`、`loglog_20000` 和 `logLog` 尾界路径。10080 的冻结区间仍为 `55529789/25000000 ≤ log(log 10080) ≤ 222119157/100000000`。

## 三个问题的读数

### 1. 当前瓶颈

以两个四项失败点为诊断样本，固定其余输入逐项改变：

| n | γ 七位、`terms=4`、当前 `logLog` | γ 十位（其余不变） | 收紧 `logLog.lower` | `terms=5`（其余不变） |
|---:|:---:|:---:|:---:|:---:|
| 7560 | false | false | true（`1071/500 → 1073/500`） | true |
| 75600 | false | false | true（`229/100 → 2291/1000`） | true |

因此 γ 区间宽度不是翻转因素。四项截断和 `logLog.lower` 都能成为局部瓶颈；在当前分段界下，四项截断留下的两个失败正是 7560 与 75600。

### 2. γ 七位收紧到十位是否解锁新 n

在全部 482 个有限纤维值上，七位 γ/四项通过 **480** 个，十位 γ/四项仍通过 **480** 个，失败集合均为 **`{7560, 75600}`**。所以在本轮目标范围内不存在“最小的新 n”：十位 γ 没有解锁任何此前判不动的值。把截断项数从 4 增到 5 才得到 **482/482**；这说明可行动的下一靶是截断或 `logLog` 界，而不是 γ 精度。

### 3. `logLog` 区间的来源与限制

冻结 `RobinRationalBasis` 只提供 10080 的 `logLog_10080_bounds` 与对应区间。7-smooth 通用证明中的其它下界是 `SevenSmooth.lean` 内部私有引理，按四个分段点给出单侧界；没有面向任意 `n` 的公开严格有理 `log(log n)` 区间 API。故当前 7560、75600 的失败对 `logLog.lower` 敏感，且这个界面确实是后续可做靶点。

## bind-only 结论

直接复用冻结的 `RobinPositiveJudge`、`expPartial_eq_sum` 和 `decide` 已足以复核上述有理判词；现有 soundness 定理需要同一个 `n` 的 `logLog.Contains` 见证。对新点没有冻结的对应 `Contains` 定理，且仅改变 γ 不产生新通过点。因此 bind-only 在本轮以“无 γ 新靶”结束；不建立模块。

## 构建与成本读数

`make lean-cache-ensure`：`status=present`，`project_olean_state=warm`，`mathlib_olean_state=warm`。

随后 `make lean` 退出 0（12999 jobs）。临时精确判词探针用要求的 profiler 命令量得：墙钟 **8.71 s**，profiler 的 `type checking` **0.75 ms**；`/usr/bin/time -l` 的峰值 RSS **2,669,543,424 bytes**。这是探针而非新生产模块；没有进行有限枚举的巨型 `decide` 证明，也没有调整 timeout 或预算。

## 库检索收据

- D5 检索命中 `robinPositiveJudge_sound`、`RationalBracket`、`logLog_10080_bounds`、四阶 γ 文件及 7-smooth 分段下界。
- 钉版 Mathlib 直接命中 `Real.eulerMascheroniSeq_lt_eulerMascheroniConstant`、`Real.eulerMascheroniConstant_lt_eulerMascheroniSeq'`、`Real.tendsto_harmonic_sub_log`（位于 `Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean`）。
- 没有新增 Blueprint 或 `.scribe.cs`，所以治理词扫描对本轮新增散文不适用；未运行 `make emit`。

结论：本轮按“收紧 γ 无助于解锁新 n”的分支停手。下一步应先提供任意 n 的严格 `log(log n)` 有理界，或把四项截断误差纳入一般结论；本轮不提交 Lean 实现。
