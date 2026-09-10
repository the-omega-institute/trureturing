# Robin judge 新 n：log-log 有理界路线读数与 bind-only 结算

- 日期：2026-09-11（Asia/Singapore）
- 分支：`lane/math/loglog-rational-bounds-0911`
- 结论：第一条硬要求的 bind-only 探针成功；停止，不新增 Lean 模块、Scribe、冻结状态、coverage 或 deposit。
- 交付形态：本报告是唯一 tracked 产物；临时 Lean 探针位于 `/tmp`，不属于仓库真值。

## 结算

对新具名伴随物 `n = 7560`，只导入冻结的
`D5.S3.Arith.GoldenResource.RobinRationalBasis`，展开 `RobinPositiveJudge`，用冻结的
`rational_log_bounds`、`log_interval_bounds`、`expPartial_eq_sum`，并以 `norm_num` 完成了
`RobinPositiveJudge 7560 5 ...`。使用的严格区间是

- `893/100 < log 7560 < 447/50`；
- `2189/1000 < log (log 7560) < 2191/1000`；
- `sigma(7560) = 28800`（七光滑分解 `2^3·3^3·5·7` 的乘法性计算）。

这只是具名伴随物的可复现实证，不是新硬编码模块。一般结论已经由冻结的
`rational_log_bounds` 给出：任意 `x = 2^k·y`（`1 ≤ y < 2`）和任意 `K` 都得到严格有理端点；把两个有理端点再送入同一构造并用 `log_interval_bounds`，即可机械构造
`Contains` 所需的 `log (log x)` 区间（对 `x > 1`）。因此路线 B 的一般性来自冻结定理本身，未复制或改写冻结证明。

## 路线 A：增加截断项数

`expPartial q terms` 是 `NormedSpace.expSeries` 的 `partialSum`，展开后为
`∑ i ∈ range terms, q^i / i.factorial`。所以 `terms = 4` 保留 0、1、2、3 次项；`norm_num`
的证明负担随新增有理项线性增加（分式乘方、阶乘和大整数归约），而判据的其它部分不变。
`terms = 4` 是原实例在已给 `logLog10080Bracket` 下的最小已用截断；上一轮纤维读数显示它漏掉 7560、75600，`terms = 5` 覆盖 482/482。

本次用同一钉版环境、同一 10080 目标、同一 `sigma` 重写，分别运行：

```sh
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=1000 /tmp/RobinTerms4.lean
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=1000 /tmp/RobinTerms5.lean
```

三轮交错热缓存读数（墙钟 / profiler `type checking` / 峰值 RSS）如下；RSS 为 `/usr/bin/time -l` 的 `maximum resident set size`：

| terms | 墙钟（s） | type checking（ms） | 峰值 RSS（bytes） |
|---:|---:|---:|---:|
| 4 | 2.69, 2.76, 2.44 | 10.8, 10.8, 10.2 | 2,674,081,792；2,673,311,744；2,674,491,392 |
| 5 | 2.45, 2.46, 2.45 | 10.8, 10.3, 10.2 | 2,673,917,952；2,674,376,704；2,673,950,720 |

`norm_num` 局部成本没有在这个噪声范围外增加；导入与环境初始化占主要墙钟。这个路线不能推出对所有 `n` 的判定：增加一项只提高指数下界，仍依赖每个 `n` 的 `log log n` 下界和最终严格余量，余量可以在别的 `n` 消失。它解释了 482 个纤维的读数，不解决数值前提的可扩展性。

## 路线 B：机械化 `log log n` 有理界

检索收据（钉版 `.lake/packages/mathlib/Mathlib` 与 Lean `#check`）：

| 查询 | 结果 |
|---|---|
| `Real.log_two_gt_d9`, `Real.log_two_lt_d9` | 存在，`Mathlib/Analysis/Complex/ExponentialBounds.lean`；十位小数界。 |
| `Real.log_three_gt_d9`, `Real.log_three_lt_d9` | 存在，同文件；`1.0986122885 < log 3 < 1.0986122888`。 |
| `Real.log_five_gt_d9`, `Real.log_five_lt_d9` | 存在，同文件；`1.6094379123 < log 5 < 1.6094379126`。 |
| `Real.log_seven_gt_d9`, `Real.log_seven_lt_d9` | 不存在；`#check` 返回 unknown identifier。 |
| `Real.log_le_sub_one_of_pos`、`Real.add_one_le_exp`、`Real.log_lt_log`、`Real.log_lt_log_iff` | 均存在，分别在 `Analysis/SpecialFunctions/Log/Basic.lean` 等文件。 |
| 连分数/通用有理 log 逼近 | 未找到可直接消费的 `Real.log 7` 专用界；Mathlib 的 continued-fraction API 是结构性展开，不是本目标的现成误差证书。 |

冻结模块已经提供更干净的级数切片：`atanhPartial`、`log_expansion_remainder_bound`、
`rational_log_bounds`。它只需 `log 2` 的十位界，再把输入写成 `2^k·y`；不需要
`log 3/5/7`。第二次 log 的输入是一般有理端点，但仍可用同一个 `2^k·y` 分解，
所以不必为每个 `n` 手写超越常数。需要手工选择的是有限整数参数 `k,K` 与外舍入端点；
端点的有理算术由 `norm_num` 机械检查。故路线 B 具有一般构造，且本次 bind-only 已直接验证了
一个新 n。

## bind-only 的直接依赖与判形

临时探针中没有新增公开声明；下表列出探针声明及其直接冻结依赖。冻结模块状态片的
`statement_id` 是 `sha256:6dcafd483a23c78180a3518807013e46c0dccfcb211d2d5f442207eb1ee621c2`。

| 探针声明 | `proof_shape` | 直接冻结依赖 | `escape_witness` | `admission_basis` |
|---|---|---|---|---|
| `log_7560_bounds_local` | bind-only | `RobinRationalBasis.rational_log_bounds` | none（直接调用冻结级数余量） | none（mandatory bind-only stop） |
| `logLog_7560_bounds_local` | bind-only | `rational_log_bounds`, `log_interval_bounds` | none（区间端点与单调性） | none（mandatory bind-only stop） |
| `RobinPositiveJudge 7560 5 ...` | bind-only | `RobinPositiveJudge`, `expPartial_eq_sum`；sigma 乘法性来自 Mathlib | none（仅有理归约） | none（mandatory bind-only stop） |

`RobinPositiveJudge_sound` 没有在探针中重新证明；本轮只证明 checker 命题，避免把伴随物冒充新的冻结节点。

## 成本坐标

上述命令就是 CLAUDE.md 10.2 要求的 profiler/time 形式。bind-only 探针热缓存的最大 RSS 为
2.674 GB，`type checking` 为 10.2–10.8 ms，墙钟为 2.44–2.76 s；首次冷导入曾读到
15.33 s、2.662 GB RSS，随后缓存稳定。由于第一条硬要求成功，没有新仓库模块需要运行
`make lean`/`make lean-report`，也没有把临时探针写入冻结树。

## Blueprint 词表自扫

本次没有改动 `Blueprint/`。仍按要求在推前执行了边界扫描：

```sh
ggrep -n -P '\b(issue #[0-9]+|PR #[0-9]+|pull request|panel brief|dispatch brief|orchestrator|six-route|proof_shape|admission_basis|escape[ _-]witness|bind-only|postmortem|git-history|accepted-event receipts)\b' Blueprint >/tmp/blueprint-governance.scan || true
ggrep -n -P '\b(search(es)?|duplicate)\b' Blueprint >/tmp/blueprint-pattern.scan || true
ggrep -n -P '\bMathlib\b' Blueprint >/tmp/blueprint-mathlib.scan || true
```

由于本次没有任何 `Blueprint/` 路径进入 diff，改动集扫描为 0 行。作为基线收据，当前整棵 `Blueprint/` 的精确词表命中 74 行，独立的 `search(es)`/`duplicate` 模式命中 1010 行，`Mathlib` 阳性对照命中 2194 行；这些都是既有内容，不是本次新增。

## 未执行项

没有新模块、Scribe 或冻结节点，故不运行 `make emit`、`make lean-report`、`make gate`、
`make deposit*` 或 `make cover`，也不开放 PR。下一次若需覆盖更多 n，应复用冻结的
`rational_log_bounds` 构造端点，而不是新增 `logLogXXXXBracket` 常量。
