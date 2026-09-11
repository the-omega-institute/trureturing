# Zhao Assumption 1 与冻结 Gronwall 链的形式化地形图

**第一条硬要求：先试 bind-only。** 本报告点名的候选 C1--C8 先在钉版环境中只作 Mathlib 实例化、冻结件投影、定义展开和规范化；包含 `sq_nonneg` 与 `linarith only`。成功者如实记 `bind-only`，不建模块。C9 的有限受限尝试未得到所需支配关系，不把失败冒充不可证明性。

**原文差异先报：** brief 的引句是准确转述，不是逐字引文。已取回的 arXiv:2411.18903v2，§8(1)，印刷页 **19** 原文为：

> “Unsatisfactorily, the proof of Theorem 2 relies on Assumption 1 in the case where Θ = 1. Is it possible to further simplify, or even completely remove this assumption?”

编号、页码和所问依赖均相符；原文多了 “Unsatisfactorily”“in the case where”“further”等措辞。

产地（CLAUDE.md §5.2）：runner 的 `consensus-rnd/sshx` thinking 席；本 worker 未另调用 skill，Codex 主循环直接取证、写报告及单点自查。承接本会话已有工具产物继续核验，没有增加独立来源；零独立评审席、无盲评或共识票。本文读数由本 worker 采集，不冒称 orchestrator 亲验。用户 brief 与研究席转述是任务输入，不算独立验证结果。

- 档位（§3.6）：**第三档，核心问题 Robin 判据 / RH；产出是形式化地形图，不是定理。** 标出外部假设与冻结链之间有无对应输入，不主张解决假设，也不主张新数学。
- LANE：<https://github.com/the-omega-institute/trureturing/issues/6160>。
- 固定源码基准：`bc8d784d6a331a985c758bdbf6cf22bcd41ac873`，分支 `lane/math/zhao-assumption1-map-0909`。本文所有仓内行号均指该基准，交付仅新增本报告。
- 钉版：Lean `leanprover/lean4:v4.33.0`；Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`。
- 检索日期：2026-09-09，Asia/Singapore。文献与编译原始证据目录下文记作 `A`：`/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/zhao-assumption1-map-0909/attempt-1`。

## Q1：论文侧取证

### 版本、定义与 Theorem 2

已打开 arXiv [摘要页](https://arxiv.org/abs/2411.18903)、[v2 PDF](https://arxiv.org/pdf/2411.18903v2)、[v2 HTML](https://arxiv.org/html/2411.18903v2)，并下载 [TeX 源包](https://arxiv.org/src/2411.18903v2)。作者 Tianyu Zhao，题名 *On the mean values of the error terms in Mertens' theorems*；版本历史为 v1 2024-11-28、v2 2025-06-24。PDF 共 23 页，本文页码是 PDF 中的印刷页码；PDFKit 页段与 TeX 数学式交叉核对。

p.1 定义（下面以 `Z` 上标区分论文与仓内同名量，原文没有此上标）：

\[
\mathcal E_1=-\gamma_E-\sum_p\sum_{n=2}^{\infty}\frac{\log p}{p^n},\qquad
\mathcal E_2=\gamma_E-\sum_p\sum_{n=2}^{\infty}\frac1{np^n},
\]
\[
E_1^Z(x)=\sum_{p\le x}\frac{\log p}{p}-\log x-\mathcal E_1,\quad
E_2^Z(x)=\sum_{p\le x}\frac1p-\log\log x-\mathcal E_2,
\]
\[
E_3^Z(x)=\frac1{\log x}\prod_{p\le x}(1-p^{-1})^{-1}-e^{\gamma_E}.
\]

**Theorem 2，p.2，完整陈述**（数学排版转写）：

> “Let \(\Theta:=\sup\{\Re(\rho):\zeta(\rho)=0\}\). If \(\Theta=1/2\), then \(\int_2^X E_3(x)\,dx>0\) for all \(X>2\). If \(1/2<\Theta<1\), or if \(\Theta=1\) and Assumption 1 holds, then \(\int_2^X E_3(x)\,dx\) changes sign infinitely often.”

这里 \(\Theta\) 是零点实部的上确界。p.5 §1.4 原文约定：

> “Throughout the text \(\rho=\beta+i\gamma\) will denote a non-trivial zero (that is, \(0<\beta<1\)) of \(\zeta(s)\) or \(L(s,\chi)\) depending on the context.”

因此 \(\Theta=1\) 是非平凡零点从左侧任意接近 1 线，并不声称 1 线上有零点。\(\Theta=1/2\) 对应 RH。p.2 对困难的原文说明是：

> “However, complications arise in the hypothetical scenario where \(\zeta(s)\) has zeros arbitrarily close to the 1-line, in which case we have to rely on Assumption 1 (see §5).”

该假设谈的是实际零点边界能否由足够规则且贴近的函数描述。一个已知的零点排除区只给一侧信息，不能自动提供下面 (ii) 的无穷零点见证。

### Assumption 1 的四个子句

**Assumption 1，p.14，完整陈述：**

> “There exists a differentiable function \(\eta(t):[0,\infty)\to(0,1/2]\) with the following properties:
>
> (i) \(\zeta(s)\) has finitely many zeros in the region \(\sigma>1-\eta(|t|)\).
>
> (ii) \(\zeta(s)\) has infinitely many zeros in the region \(\sigma>1-K\eta(|t|)\) for some constant \(K>1\).
>
> (iii) \(\eta'(t)t\) strictly increases to 0 as \(t\to\infty\).
>
> (iv) \(\eta(t)/|\eta'(t)|\gg t\log t\).”

其中 \(s=\sigma+it\)；(i) 允许有限多个例外，不能转写为处处无零点；(ii) 的量词是某个固定 \(K>1\) 下有无穷多个零点；(iv) 是渐近下界，隐常数与充分大阈值不能删掉。

### 在证明中用来保证什么

困难首先在 p.12 被明确点出：

> “However, the previous line of reasoning breaks down if \(\Theta=1\) since \(\int_2^X(E_2(x))^2\,dx\) and the large values of \(\int_2^X E_2(x)\,dx\) are of comparable magnitude, making it unclear whether there still exists arbitrarily large \(X\) where the first moment dominates the second moment.”

§5 从 p.13 开始，定义
\(\Delta_1(x)=\int_2^x E_2(t)\,dt\)、\(\Delta_2(x)=\int_2^x E_2(t)^2\,dt\)，并写下
\[
\Delta_1(x)<e^{-\gamma_E}\int_2^x E_3(t)\,dt<\Delta_1(x)+\Delta_2(x).
\]
接着原文说：

> “We already know from (20) that there exists arbitrarily large \(x\) with \(\Delta_1(x)>0\), so our goal is to show that \(\Delta_1(x)<-\Delta_2(x)\) infinitely often.” (p.13)

这是作者所用的比较框架；其前置等式的忠实转写限制另见 Q2 的有限尾项核对，本报告没有把这组积分不等式当成仓内已证件。

| 论文步骤 | 输入与实际用途 | 原文位置 |
| --- | --- | --- |
| 得到一阶矩负向振荡 | Lemma 10：给零点 \(\rho_0=\beta_0+i\gamma_0\)，\(\beta_0>1/2+\epsilon\)、\(\gamma_0>C_1(\epsilon)\)；每个 \(X>\gamma_0^{C_2(\epsilon)}\) 都有 \(x_1,x_2\in[X,X^{1+\epsilon}]\)，且 \(\Delta_1(x_1)>x_1^{\beta_0}/(\gamma_0^{2+\epsilon}\log x_1)\)、\(\Delta_1(x_2)<-x_2^{\beta_0}/(\gamma_0^{2+\epsilon}\log x_2)\)。 | p.13，Lemma 10，(28) |
| 得到二阶矩上界 | Lemma 11：连续递减 \(\eta\) 的零点排除条件（\(\Theta=1\) 可有有限例外），令 \(\omega(x)=\min_{t\ge1}(\eta(t)\log x+\log t)\)，则 \(\Delta_2(x)=O_\epsilon(xe^{-2(1-\epsilon)\omega(x)}/(\log x)^2)\)。Assumption 1(i) 在 p.15 明确传入这里。 | p.14 Lemma 11；p.15 “as a consequence of Lemma 11 and assumption (i)” |
| 反复选择靠近边界的零点 | (ii) 提供无穷多个 \(\beta_0>1-K\eta(\gamma_0)\) 的零点，用于 Lemma 10，并最终让比较尺度无界。 | p.15：“Such \(\rho_0\) exists and there are infinitely many of them due to assumption (ii).” |
| 将两个估计安排在同一尺度 | (iii) 控制极小化参数的唯一性；选 \(\log X_0=1/(|\eta'(\gamma_0)|\gamma_0)\)，使 \(\omega(X_0)=\eta(\gamma_0)/(|\eta'(\gamma_0)|\gamma_0)+\log\gamma_0\)。 | p.15：“It follows from assumption (iii) that such \(t_0\) is unique if exists.” |
| 跨过阈值并压过二阶矩 | (iv) 令 \(X_0>\gamma_0^{C_2(\epsilon)}\)，再使 \((2(1-\epsilon)-K(1+\epsilon))\eta(\gamma_0)/(|\eta'(\gamma_0)|\gamma_0)>3\epsilon\log\gamma_0\)，选定的 \(\epsilon\) 不随零点改变。 | p.15：“By assumption (iv) …”；“assumption (iv) guarantees that we can choose \(\epsilon\) (depending only on \(K\), not \(\gamma_0\)) small enough …” |

最后的原文结账是：

> “Finally, the infinitude of such zeros \(\rho_0\) yields arbitrarily large \(x_2\) with \(-\Delta_1(x_2)>\Delta_2(x_2)\), thereby concluding the proof.” (p.15)

**陈述与证明的边界：** p.15 另写 “Without loss of generality we may suppose that \(1<K<2\), since otherwise we can simply multiply \(\eta(t)\) by a suitable constant.” Assumption 1 原文仍只有 \(K>1\)。本席没有认证该缩放同时保持 (i)--(iv)，不把 \(K<2\) 偷换进精确陈述，也不据此裁定论文定理真假。

## Q2：与本仓的对应关系

### 判据与总体判词

**总体为 (d)，对不上同一条定理链。没有定位出一个与 Assumption 1 等价或更强的冻结输入。**

四选一判据如下： (a) 须在同一对象、参数和量词下提供双向推导；(b) 须有仓内输入推出 Assumption 1 所需控制的单向推导；(c) 指当前证明路线绕开其用途、没有走到零点边界上的矩支配步骤，不冒称已证逻辑强弱；(d) 指结论的对象或量词不同，尚无把两条链连接到同一目标的已证转换。下面每行只选一个。

设本仓标准化约数和比值
\[
R(n)=\frac{\sigma(n)}{e^{\gamma_E}n\log\log n}.
\]
冻结上包络是 \(\forall\epsilon>0,\exists N,\forall n\ge N,R(n)\le1+\epsilon\)；下包络是 \(\forall\epsilon>0,\forall N,\exists n\ge N,R(n)\ge1-\epsilon\)。它们给出极限包络，不给出 Robin 的逐点严格不等式 \(R(n)<1\)（所有 \(n>5040\)），也不陈述 \(\int_2^X E_3^Z\) 的符号。

| 对照输入 / 出口（Lean 声明名） | 文件:行号 | 选项与判据 |
| --- | --- | --- |
| `Mertens.E₁p.bounded`；`Mertens.E₂p.abs_le`、`Mertens.E₂p.bound` | `D5/S3/Weil/Mertens/Estimates.lean:386`；`D5/S3/Weil/Mertens/Third.lean:68`、`:98` | **(c)**。分别是有界误差、\(O(1/\log x)\) 点态控制；不提供零点见证或一阶矩的负向下界。仓内 `E₁`（Estimates:190）是常数，不是论文的 `E₁(x)`。 |
| `Mertens.log_zeta_eq_sum`、`Mertens.log_zeta_eq_integ`；`Mertens.γ.eq_eulerMascheroni` | `D5/S3/Weil/Mertens/LogZeta.lean:34`、`:356`；`D5/S3/Weil/Mertens/Gamma.lean:696` | **(c)**。前两条输入是实数 `s` 与 `1 < s`，通过 Euler 乘积/积分识别常数；不输入贴近 1 线的 \(\eta\) 或无穷零点分布。 |
| `Mertens.E₃.abs_le`、`Mertens.E₃.bound`、`Mertens.E₃.bound'`、`Mertens.E₃.bound''`、`Mertens.E₃.bound'''` | `D5/S3/Weil/Mertens/Third.lean:301`、`:324`、`:333`、`:335`、`:346` | **(c)**。分别提供对数误差的 \(O(1/\log x)\)、趋零、乘积渐近等价及乘积差的 \(O(1/\log^2 x)\)。没有关于 \(\Delta_1,\Delta_2\) 同尺度支配的结论。尤其 `bound''` 是上、下包络实际使用的 Mertens III 输入。 |
| `D5.S3.Weil.GronwallUpperEnvelope.small_prime_product_le`、`large_prime_count_le`、`large_prime_product_le`、`sigma_split`、`gronwall_upper_envelope`（本行后四名同一命名空间） | `D5/S3/Weil/GronwallUpperEnvelope.lean:37`、`:64`、`:87`、`:127`、`:189` | **(c)**。有限素因子分割和计数把 `bound''` 用在 \(y=\log n\)；上包络源码 :202 是该实例化，:230 消费 `sigma_split`。所有局部前提都是域、正性或 \(n\) 的条件，不是零点边界假设。 |
| `D5.S3.Weil.GronwallLowerEnvelope.gronwall_lower_envelope` 及 private `normalized_mertens`、`prime_power_error`、`loglog_primorial_power_le` | `D5/S3/Weil/GronwallLowerEnvelope.lean:157`、`:113`、`:51`、`:134` | **(c)**。用 primorial 的固定次幂和可求和倒数平方尾项构造达到下包络的整数；:139 用 Mathlib `primorial_le_four_pow`，:121 用 `Mertens.E₃.bound''`。不构造 \(\zeta\) 零点。 |
| `D5.S3.Weil.GronwallLowerEnvelope.gronwall_envelopes`、`robinLogMargin`、`robin_log_margin_eq_neg_log`、`robin_log_margin_liminf` | `D5/S3/Weil/GronwallLowerEnvelope.lean:236`、`:246`、`:251`、`:265` | **(d)**。`robinLogMargin` 是定义；\(n\ge5041\) 时等于 \(-\log R(n)\)，下极限为 0。对象是自然数上的 Robin margin，不是实数截断积分的无限变号。 |
| `D5.S3.Weil.PrimeValuationGap.bounded_prime_valuation_robin_ratio`、`bounded_prime_valuation_robin_margin_gap` | `D5/S3/Weil/PrimeValuationGap.lean:199`、`:223` | **(d)**。给定素数 \(p\)、上限 \(A\)、\(\epsilon>0\)，充分大且 `n.factorization p ≤ A` 的整数有 margin 下界 \(-\log(1-p^{-(A+1)})-\epsilon\)。这是局部算术限制；\(p,A\) 在阈值 \(N\) 之前固定，不能换成对所有素数同时的边界控制。 |

所有位置已用源码核对，声明身份、类型和依赖另由 Q3 的 Lean 环境读数验证。#6171 已用 GitHub 只读 API 核实为 MERGED，merge SHA `03141f40cdad702a382653a4c169803e2f7b8f44`；端口注明上游 `kimihiro64/PrimeNumberTheoremAnd` commit `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`。本席没有重新移植它。

### 先消除同名误差的假对应

仓内 `Mertens.E₃` 定义于 Third:205，实际是
\[
L(x)=\sum_{p\le x}\log(1-p^{-1})+\log\log x+\gamma_E.
\]
由冻结 `Mertens.prod_one_minus_div_prime_eq`（Third:207）和倒数规范化，\(x>1\) 时精确得到
\[
E_3^Z(x)=e^{\gamma_E}\bigl(e^{-L(x)}-1\bigr).
\]
这里没有额外的 \(\log x\) 因子。此换算是 C1 的 `bind-only`，它没有把点态渐近变成积分振荡定理。

另令 \(S(x)=\sum_{0<n\le\lfloor x\rfloor}\texttt{Mertens.M_eq_summand}(n)\)。冻结 Third:201 的 `Mertens.M.eq` 给出 \(M=\gamma+\sum'_p(\log(1-p^{-1})+p^{-1})\)（非素数项为零），Gamma:696 识别 \(\gamma=\gamma_E\)。C2 的精确有限和规范化得到
\[
L(x)=\bigl(S(x)-(M-\gamma_E)\bigr)-\texttt{Mertens.E₂p}(x).
\]
`Mertens.sum_M_eq_summand_le'`（Third:291）给出 \(x\ge2\) 时该括号的绝对值不超过 \(4/x\)。

这也暴露了不能直接照搬的源式：论文 p.12 将有限 \(-\sum_{p\le x}\log(1-p^{-1})\) 改写成 \(\sum_{p\le x}p^{-1}-\mathcal E_2+\gamma_E\)，随后写积分的精确等式 \(\int E_3=e^{\gamma_E}\int(e^{E_2}-1)\)。按有限/无限求和的定义核对，这个等式没有显式保留上述有限尾项。报告保留源文所述论证用途，同时把该等式的忠实转写登记为**待核对**；不主张已修复它或已判 Theorem 2 为假。Lean 探针从仓内 `M` 定义出发，也没有形式化论文双重无穷级数常数与 `M.eq` 的重排转换。

### 候选逐条 bind-only 账

以下是本席尝试的全部候选，不把论文的 Lemma 10/11 冒列为已实现候选。临时探针为 `A/MapProbe.lean`，不进入本仓 Lean 模块树。各成功行 `escape_witness: none`，`admission_basis: none (map-only; no module/deposit)`。

| 候选 | 首次受限操作与结果 | 直接冻结来源（模块 GID；声明见上文） |
| --- | --- | --- |
| C1：论文乘积误差与 `L` 的精确坐标转换 | `prod_one_minus_div_prime_eq` + `prod_inv_distrib`、`exp_neg`、`field_simp` 已闭合，尾随 `ring` 未执行；**bind-only**。首次编译因 `prod_inv_distrib` 的 `rw` 方向反了而失败；纠正方向，没有加数学输入。 | `D5/S3/Weil/Mertens/Third` |
| C2：带有限尾项的 `L = tail - E₂p` 恒等式 | 展开定义、有限和分配、`sum_filter`、`ring`；**bind-only**。 | Third 中的定义，不增加分析定理 |
| C3：有限尾项 \(\le4/x\) | `exact Mertens.sum_M_eq_summand_le' hx`；**bind-only**。 | `D5/S3/Weil/Mertens/Third` |
| C4：归一化逆素数乘积趋于 1 | `Mertens.E₃.bound''.inv` + Mathlib `isEquivalent_iff_tendsto_one` 及规范化；**bind-only**。 | `D5/S3/Weil/Mertens/Third` |
| C5：上、下两个 ε 包络 | `(gronwall_envelopes ε hε).1`、`.2`；**bind-only**。 | `D5/S3/Weil/GronwallLowerEnvelope` |
| C6：margin 的对数恒等式、下极限为 0 | 两个对应冻结定理的直接应用；**bind-only**。 | `D5/S3/Weil/GronwallLowerEnvelope` |
| C7：有界素数赋值的 margin 缺口 | `bounded_prime_valuation_robin_margin_gap hp A ε hε`；**bind-only**。 | `D5/S3/Weil/PrimeValuationGap` |
| C8：矩比较后的标量收尾；平方非负 | 给定 `I < d₁ + d₂` 和 `d₁ < -d₂`，`linarith only [hupper, hdom]` 得 `I < 0`；`sq_nonneg (Mertens.E₂p x)`；均 **bind-only**。这不提供两个给定前提。 | 无新增冻结依赖；Mathlib 与给定标量前提 |
| C9：从非负二阶矩得到负一阶矩支配 | 用 `0 ≤ d₂`、`sq_nonneg d₁` 运行 `linarith only`，由 `fail_if_success` 确认此尝试失败。再对照实际冻结端点类型，没有可投影的 `d₁ < -d₂` 或 η/零点见证。**not-found-in-tested-bind-only-scope**，不是全库穷尽搜索或逻辑独立性证明。 | 没有找到供应该前提的声明；不建 content 模块 |

关键受限收尾的原样代码：

```lean
example (d₁ d₂ I : ℝ) (hupper : I < d₁ + d₂)
    (hdom : d₁ < -d₂) : I < 0 := by
  linarith only [hupper, hdom]

example (x : ℝ) : 0 ≤ (Mertens.E₂p x) ^ 2 := sq_nonneg _

example (d₁ d₂ : ℝ) (hnonneg : 0 ≤ d₂) : True := by
  have hsq := sq_nonneg d₁
  fail_if_success have : d₁ < -d₂ := by linarith only [hnonneg, hsq]
  trivial
```

## Q3：不可消去性与真实依赖证据

`first_breaking_theorem: not-applicable`。Q2 没有 (a)/(b) 输入，所以不能声称删去 Assumption 1 会先破坏本仓某定理。本文的“缺输入”是尚未连接的论文侧目标，不是冻结定理的未履行前提。没有改动冻结件做删前提实验，也没有证明 Assumption 1 在数学上不可消去。

### 采集方法

先运行 `make lean`，再通过一次性外部 Make 扩展运行探针（没有裸 `lake` 调用、没有改根 Makefile 或预算）：

```sh
make lean > "$A/make-lean.log" 2>&1
make -f Makefile -f "$A/probe.mk" lean PROBE="$A/MapProbe.lean" > "$A/bind-only.log" 2>&1
```

`A/probe.mk` 的 `lean` 附加前置在仓库已有 `tools/scripts/worktree/lean-cache-run.sh` 环境内检查该临时文件。`#check` 读取端点完整类型；`#print axioms` 读取标准公理闭包。探针还用 `getEnv`、`getModuleIdxFor?`、`ConstantInfo.type.getUsedConstants` 以及 `.thmInfo` / `.defnInfo` / `.opaqueInfo` 的 **value** 递归读取真实常量依赖，不能用漏掉 theorem value 的便捷接口替代。完整产物为 `A/lean-semantics.json`。

这是编译器环境中的符号级读数，不是用 grep 猜引用。常量闭包是依赖证据，不自动证明每个节点均为不可替换的数学前提；import 闭包更只是可用环境。端点类型无 RH/Θ/η 假设与其证明公理闭包须一起读，单独 `#print axioms` 无法排除定理类型里显式写出的条件。

### 路径（消费者 → 前置）

GID 是模块头的规范地址；下列模块路径由声明级证明项中的边见证，不发明新的冻结 GID：

```text
D5/S3/Weil/GronwallLowerEnvelope
  → D5/S3/Weil/GronwallUpperEnvelope
  → D5/S3/Weil/Mertens/Third
  → D5/S3/Weil/Mertens/Gamma
  → D5/S3/Weil/Mertens/LogZeta
  → D5/S3/Weil/Mertens/Estimates

D5/S3/Weil/PrimeValuationGap
  → D5/S3/Weil/GronwallUpperEnvelope
  → D5/S3/Weil/Mertens/Third
```

其中与问题最近的声明级实际路径是：

```text
GronwallLowerEnvelope.robin_log_margin_liminf (:265)
  → GronwallLowerEnvelope.gronwall_envelopes (:236)
  → GronwallUpperEnvelope.gronwall_upper_envelope (:189)
  → Mertens.E₃.bound'' (Third:335)
  → Mertens.E₃.bound' (:333) → Mertens.E₃.bound (:324)
  → Mertens.E₃.abs_le (:301)
  → Mertens.E₂p.abs_le (:68) / Mertens.sum_M_eq_summand_le' (:291)

GronwallLowerEnvelope.gronwall_envelopes (:236)
  → GronwallLowerEnvelope.gronwall_lower_envelope (:157)
  → private normalized_mertens (:113) → Mertens.E₃.bound''

PrimeValuationGap.bounded_prime_valuation_robin_margin_gap (:223)
  → PrimeValuationGap.bounded_prime_valuation_robin_ratio (:199)
  → private fixed_boost_envelope (:134)
  → GronwallUpperEnvelope.gronwall_upper_envelope
```

两种 private helper 的环境真名分别是 `_private.D5.S3.Weil.GronwallLowerEnvelope.0.D5.S3.Weil.GronwallLowerEnvelope.normalized_mertens` 和 `_private.D5.S3.Weil.PrimeValuationGap.0.D5.S3.Weil.PrimeValuationGap.fixed_boost_envelope`。它们是冻结模块内部声明，不是独立冻结节点。`sigma_split → small_prime_product_le / large_prime_product_le → large_prime_count_le` 也在证明项读数中出现。

| 采集目标 | 传递常量数（含 Lean/Mathlib） | 其中本仓节点数（含内部生成常量） |
| --- | ---: | ---: |
| `Mertens.E₃.abs_le` | 58069 | 205 |
| `Mertens.E₃.bound''` | 58089 | 221 |
| `gronwall_upper_envelope` | 58199 | 228 |
| `gronwall_lower_envelope` | 58501 | 230 |
| `gronwall_envelopes` | 58526 | 238 |
| `robin_log_margin_liminf` | 58560 | 248 |
| `bounded_prime_valuation_robin_margin_gap` | 58262 | 259 |

编译 import 闭包为 6030 个模块。这些数量不是新定理数量。公理与最终编译结果见文末验证收据。

### 冻结状态和计数口径

已亲自 `ls Golden/Frozen/state/D5/S3/Weil/` 并逐个读取七个状态片；下表是模块级 `statement_id`，不能当作某条声明单独的 statement identity。

| 模块（均在 `D5/S3/Weil/`） | 模块 `statement_id`（`sha256:` 后内容） | 编译环境公开 theorem / def 数 |
| --- | --- | ---: |
| `Mertens/Estimates` | `6c959a98d7ca5757b045e2dc3e4e5f51f5b190cadf6563b609b85282c9b79996` | 34 / 5 |
| `Mertens/Third` | `673a069e2ca56dd5e4c756b4a45f46ca48585ce34e89bba9a8cfc0e7e50ec2e9` | 27 / 5 |
| `Mertens/LogZeta` | `9dbaec232f666647717dcfcfbea54cb332c52c1d152546ec055a8f61d06acc15` | 3 / 0 |
| `Mertens/Gamma` | `4f993fb2b76ccb6acfc59ce9eeaac6431c4ce3a04bccd66109afb3f59a8fd101` | 2 / 0 |
| `GronwallUpperEnvelope` | `5649f49b7a510331194224220fb89ddf3339817611eac068d46a8679c5424e27` | 6 / 1 |
| `GronwallLowerEnvelope` | `c60de55af3115013bec6914e8646e38d066c81c25fded53f1dc362ec12766da0` | 5 / 1 |
| `PrimeValuationGap` | `132c5eb1be40b0b38be20da4d6aa994f25ab2dae2e64f79ca2c261846f520e3d` | 5 / 0 |

计数条件是归属模块一致、非 `_private`、非 `Name.isInternal`；包含编译产生的公开 `eq_1`，`lemma` 与 `theorem` 都是 `thmInfo`。因此 Estimates/Third 与 brief 的 27/11 不能混用；上包络 6 中有 `largePrimes.eq_1`，下包络 5 中有 `robinLogMargin.eq_1`，不是把 def 算成 theorem。计数不影响对应关系。

候选直接绑定的定理级身份如下；与前表模块 GID 配对使用。由已有 Freeze JSON 的 `declaration_statement_ids` 读取，没有新增状态。C2 只展开定义，C8 只绑定 Mathlib/给定前提。

| 候选 | 直接冻结声明 | 单声明 `statement_id`（`sha256:` 后内容） |
| --- | --- | --- |
| C1 | `Mertens.prod_one_minus_div_prime_eq` | `f14fd811a11df4f39633f38e9995fe86263dfaea6d16706b4a874094674882d3` |
| C3 | `Mertens.sum_M_eq_summand_le'` | `d41650c62a6b94581bd2942ea47718c154b6c1311524bec9b316f6bf17ecbdf3` |
| C4 | `Mertens.E₃.bound''` | `d4c36eb2836729fdc7d27b8d61849d723fcc7cce45f668568c6fad517f95b817` |
| C5 | `D5.S3.Weil.GronwallLowerEnvelope.gronwall_envelopes` | `01d5d38a236c40e4ce1ce3e7fe76b6c1f1ef69009f5498845262c6f228467293` |
| C6 | `D5.S3.Weil.GronwallLowerEnvelope.robin_log_margin_eq_neg_log` | `e312c38cff0ca4957e770c02da32283ec8fcb33e34bf136fda65e1c3a9db83dc` |
| C6 | `D5.S3.Weil.GronwallLowerEnvelope.robin_log_margin_liminf` | `c87d805981b4faae9762314dd5e88987c8aff0aed2a46bde06299be0ac7495bb` |
| C7 | `D5.S3.Weil.PrimeValuationGap.bounded_prime_valuation_robin_margin_gap` | `04d107d4e7d20f8713cf69c368bbf7c186ba28f39731d7bf01caee75f2265278` |

来源分别为 `Golden/Frozen/accepted/54027e2d7e766354a0e3cc2c772b0ad669804c6d51ce306dca4770006be79672.json`（Third）、`c96dca6ca8759722b55d4763a3244f50cb191eefa742d548f34953a014b0e227.json`（Lower，同一目录）和 `775991cd67490e115770633d5214790d0857dddb12b2c65bf2cb513c6a622d0c.json`（Gap，同一目录）。

**已知陷阱复核：** `Library/notes/pntplus2026mertens.md:242` 起的 2026-09-08 勘误逐项宣布旧上包络表已闭合；:192 的 “No PNT or RH premise enters this upper-envelope route” 与端点类型相符。旧表不是待办清单，本报告不再派发其六行。

## Q4：六栏与停止判据

| from | steps | gap（数学缺陷） | escapes | payoff | cost_shape |
| --- | --- | --- | --- | --- | --- |
| 当前冻结 Mertens III、Gronwall 上/下包络及赋值缺口 | 先做 C1--C8 的坐标转换、实例化与投影，再检查是否供应作者的矩比较前提 | 这些端点没有供应 \(\Delta_1(x)<-\Delta_2(x)\) 的无界尺度见证；两条链尚无到同一结论的桥。不是缺一个 `simp` 引理，也不是旧上包络尚未闭合。 | 保持当前地图判词 (c)/(d)，停止新增数学模块；不能把渐近包络包装成 Assumption 1 已移除。 | 排除错误派工，明确本仓目前实际证明到哪里。 | 一次有限的文献、编译和依赖核验；零 deposit、零冻结、零新 Lean 模块。 |
| 论文 \(\Theta=1\) 分支，想去掉/减弱 Assumption 1 | 按作者框架需把 Lemma 10 的负一阶矩振荡与 Lemma 11 的二阶矩上界放在同一批趋向无穷的尺度；还须忠实处理有限尾项及 \(K\) 归一化 | **需要零点边界的真正解析进展，或能替代它的矩比较进展。** 当前只知道点态上界/一般零点排除区，缺少实际边界贴合、规则性及统一尺度支配。本文未证该进展在所有可能证明中都必要。 | 人类提供可核对的新解析结果；或已发表的替代路线。保留 Assumption 1 只会得到条件路线；另限 \(\Theta<1\) 改变问题范围，均不等于完成去假设。 | 条件地指向作者 \(\Theta=1\) 积分负值无界出现的步骤；仍须证明正值与其余前置，不能冒领完整 Theorem 2 或 RH。 | 解析研究成本未知；不是增加 Lean 预算即可解决，也不是当前可交给纯绑定实施席的任务。新文献输入出现后重新画图。 |

本轮停止判据：原文和版本核实、候选先库后证账结算、真实依赖路径可复查、搜索边界如实登记即完成地图席。当前没有由本报告支持的新实施席。此停止不宣称外部开放问题被解决或被证明无解。

## 文献检索留痕

| 来源与实际查询 | 返回、打开与判断范围 |
| --- | --- |
| arXiv `abs/2411.18903`、`pdf/2411.18903v2`、`html/2411.18903v2`、`src/2411.18903v2` | 均实际打开/下载；摘要版本历史最新列 v2。PDF、HTML、源包用于主文核对。 |
| [期刊 HTML](https://link.springer.com/article/10.1007/s40993-025-00640-y) 与 [期刊 PDF](https://link.springer.com/content/pdf/10.1007/s40993-025-00640-y.pdf) | 实际打开。Research in Number Theory 11，article 62 (2025)，published 2025-06-16。期刊 PDF 共 24 页：Theorem 2 p.2，Assumption 1 p.15，比较步骤 pp.15--16，§8(1) p.20，仍明确呈现同一依赖。不能把 arXiv 页码套到期刊版。 |
| Crossref `GET /works?query.title=On the mean values of the error terms in Mertens theorems&rows=10` | 实际读 JSON，10 条排名结果，精确题名命中 Zhao DOI；其余为模糊匹配。`total-results` 是模糊数据库计数，不作相关论文数量。 |
| OpenAlex `GET /works?filter=doi:https://doi.org/10.1007/s40993-025-00640-y`；再查 `filter=cites:W4405029842&per-page=100` | 精确作品 W4405029842，引用查询返回 0/0；目标记录更新时间 2026-08-26。仅说明该索引此次没有引用记录，绝非无人引用或没有后续论文的证明。 |
| arXiv API `search_query=all:Mertens AND (all:mean OR au:Zhao)`，`start=0&max_results=50&sortBy=submittedDate&sortOrder=descending` | 42/42 条；读完返回摘要，其中自 2024-11-28 起 10 条。相关近邻 2511.02745、2604.00047、2605.24504 的摘要分别谈 Mertens II 替代证明、Collision Transform、动力系统类比；没有在摘要中声称去掉本假设。未读这些全文。 |
| arXiv API `search_query=ti:Mertens AND submittedDate:[202411280000 TO 202609092359]`，`start=0&max_results=100&sortBy=submittedDate&sortOrder=descending` | 9/9 条，全部摘要已读。除目标外为 2608.01498、2607.07566、2607.04366、2603.24548、2602.05788、2512.07336、2505.08160、2502.21021。对最相关的两篇进一步打开全文 HTML，见下行。 |
| [2608.01498v1](https://arxiv.org/html/2608.01498v1)，*Bounds for Mertens sums*（2026-08-02）；[2603.24548v1](https://arxiv.org/html/2603.24548v1)，Kalyabin 的 Gronwall 极值论文（2026-03-25） | 下载全文 HTML，读摘要和主结果；前者 §1.1 Theorem 2 给素数倒数和的点态指数/对数误差界，后者 Theorem 1 给固定最大素因子类别下的 Gronwall 极值与改进 Mertens 余项关系。已读主结果均没有 Zhao 积分在 \(\Theta=1\) 时去假设的陈述。全文中 `Zhao`、`2411.18903` 的字面检索也未命中；这不等于逐一验证全文所有推论。 |
| OpenAlex `search=Mertens error terms mean values&filter=from_publication_date:2024-11-28&per-page=50`；`filter=title.search:Mertens,from_publication_date:2024-11-28,to_publication_date:2026-09-09&per-page=100` | 分别读到 50/4539、100/151 条排名记录；混入大量姓名和同名 Möbius 求和主题。没有翻页穷尽，作用仅为补充发现候选；不将它们包装成完整负面检索。 |
| Google `"2411.18903" "assumption"`、`"Tianyu Zhao" "Mertens" "assumption" removed`；DuckDuckGo `"Tianyu Zhao" "Mertens" assumption`；Bing `"2411.18903"` | 实际打开响应，但 Google 仅给启用 JavaScript 页、DuckDuckGo 给 challenge，Bing 返回无关旅行结果。均不计为有效负面检索；HTTP 200 本身不算检索成功。 |

独立搜索的结论限定为：**在上述实际读取的版本、索引结果、摘要和主结果中，未检出后来移除 Assumption 1 的结果；已打开期刊版仍保留依赖。** 这不是不存在性证明。 arXiv API 基址为 `https://export.arxiv.org/api/query`，Crossref 为 `https://api.crossref.org`，OpenAlex 为 `https://api.openalex.org`；参数由 `curl --get --data-urlencode` 编码，原始 JSON/XML/HTML 全部保存在 `A`。

## 仓内碰撞与验证收据

### 检索阴阳对照

以下都是固定基准、写入报告前的**命中行数**（不是声明数）。使用同一 `\b` 正则特性的 PCRE / ripgrep，无 `grep -E`。依赖结论由上面的编译器读数承担，文本搜索只粗筛或核对字面量。

| 完整命令 | 行数 / 退出码 | 解释 |
| --- | --- | --- |
| `git grep -n -P '\b(Zhao\|2411\.18903\|ZhaoAssumption\|zhao_assumption1)\b' -- D5 Library docs`（执行时各 `\|` 为普通 `|`） | 1 / 0 | 唯一项在 `docs/develop/theory/ZECKENDORF_CONSTELLATION_ORBIT_CUMULANT_THEORY.md:33354`，为文献 URL；不是 Lean 假设声明。 |
| `git grep -n -P '\b(Mertens\|GronwallUpperEnvelope\|GronwallLowerEnvelope\|PrimeValuationGap)\b' -- D5 Library docs`（同上，Markdown 竖线转义） | 168 / 0 | 已有端口及包络链，必须复用。 |
| `git grep -n -P '\b(gronwall_upper_envelope)\b' -- D5` | 5 / 0 | 阳性对照。 |
| `git grep -n -P '\b(zhao_assumption1_boundary_witness)\b' -- D5` | 0 / 1 | 阴性对照；不作语义不存在证明。 |
| `rg -n '\b(Zhao\|Mertens\|Gronwall\|Pintz)\b' .lake/packages/mathlib/Mathlib/NumberTheory`（同上） | 4 / 0 | 全是其他 Zhao 作者的版权行，不是所需矩比较 API。 |

原样可执行的两个主要命令另列，避免 Markdown 表格转义歧义：

```sh
git grep -n -P '\b(Zhao|2411\.18903|ZhaoAssumption|zhao_assumption1)\b' -- D5 Library docs
git grep -n -P '\b(Mertens|GronwallUpperEnvelope|GronwallLowerEnvelope|PrimeValuationGap)\b' -- D5 Library docs
rg -n '\b(Zhao|Mertens|Gronwall|Pintz)\b' .lake/packages/mathlib/Mathlib/NumberTheory
```

位置补查 `rg -n '^\s*(private )?(theorem|lemma|def) (normalized_mertens|loglog_primorial_power_le|gronwall_lower_envelope|prime_power_error|sigma_primorial_power|fixed_boost_envelope|bounded_prime_valuation_robin_ratio|bounded_prime_valuation_robin_margin_gap)' D5/S3/Weil/{GronwallLowerEnvelope,PrimeValuationGap}.lean` 得 8 行、exit 0，再用语义环境验证所指声明。查冻结记录时曾把不存在的 `Blueprint/D5/S3/Weil/Mertens` 传给 `rg`，exit 2 不作零命中；去掉该路径后在 `Golden/Frozen/accepted` 与既有报告中命中 2 行，并用 JSON 读取冻结记录。另一次探路的 inspector 文件路径不存在，也不作不存在性证据。

查声明级冻结身份的命令为 `git grep -l -P '"descriptor_selector": "D5/S3/Weil/(Mertens/Third|GronwallLowerEnvelope|PrimeValuationGap)\.lean"' -- Golden/Frozen/accepted`，命中 3 个文件、exit 0；随后用 `jq` 解析身份字段。

本报告自身会引入 `Zhao` 等命中。终检对前四条 `git grep` 在 `--` 前显式插入基准 `bc8d784d6a331a985c758bdbf6cf22bcd41ac873` 重跑，读数仍是 **1、168、5、0**，退出码 **0、0、0、1**；原始结果为 `A/*-final-base.txt`。最终提交只含本报告，不改上游、冻结账本、常数、预算、构建配置或其他工作树的内容。

### 离线材料与验证结果

`A` 内有源 PDF/TeX/HTML、搜索响应、`MapProbe.lean`、`probe.mk`、`lean-semantics.json`、`make-lean.log`、`bind-only.log` 和失败的 `bind-only-failed-rw.log`。失败日志中的 `sorryAx` 来自失败候选的错误恢复，不能作为成功证明引用。

| 原始文献工件 | SHA-256 |
| --- | --- |
| `zhao-2411.18903v2.pdf` | `db20602b1b53c56b06ccdb5b6e72f848ad804d27e6b5c1809f265af0d4b240b1` |
| `zhao-v2.tex` | `6f9b56cca105666bae0ac28438fe05daf9a257776dd0edf8f98664761dd5032d` |
| `zhao-journal.pdf` | `8cfd95061975ae434cccbf71d7140b142ca9ca5ea5996eeb94f9308c87c2d0fa` |
| `MapProbe.lean` | `a8393481f1c216c363c982f289388af38aed08259557339a0e76a9e243f19474` |
| `lean-semantics.json` | `14cab2a337eeea5bb098928dabb98374af92c73616b52005e05a9c09c0789bc1` |

验证状态：`make lean` 和最终 `make ... lean PROBE=...` 均 **exit 0**，均报告 “Build completed successfully (12634 jobs)”，缓存读数为 project/mathlib warm、method none。最终 `#print axioms` 检查 C1、C2、C4、`Mertens.E₃.bound''`、上/下包络、margin 下极限及赋值缺口，全部仅为 **`[propext, Classical.choice, Quot.sound]`**，没有 `sorryAx` 或新增分析公理。临时探针保留 unused simp/tactic/variable 警告，没有通过关闭 linter 掩盖它们。文档 `git diff --check` 通过；语义边、引用位置及冻结身份另作结构化终检，收据在 `A/verification.log`。

### ASSUMED-UNVERIFIED 与明确未主张

- 未打开的候选全文、未翻到的 OpenAlex 页、研究席先前检索过程：`ASSUMED-UNVERIFIED`；本文不依赖其负面结论。
- 论文 p.12 有限尾项的精确等式处理、p.15 的 \(K\) 缩放保条件、论文双重无穷级数常数与仓内常数的完整 Lean 桥：未认证，不充当冻结输入。
- 独立评审、orchestrator 亲验：未发生于本 worker 的证据范围，不冒领。
- **未解决或去掉 Assumption 1；未证明 Zhao Theorem 2；未证明 Robin 判据或 RH；未主张本仓链等价于论文的链；未证明该假设全局不可消去；未主张新数学。**
- 交付是单份地图报告，按授权提交、推送分支；不 deposit、不冻结、不开 PR。
