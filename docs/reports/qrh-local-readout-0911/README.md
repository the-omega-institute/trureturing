# 量子 RH 局部读出探针 · 2026-09-11

**判断：本席不建议新建 Lean 模块。第 1、2 步已用实际素数和实际权重编译证实为 bind-only；第 3 步的单席小切片仍有直接绑定路线，完整极限不能用 `lineDerivCLM` 冒充；第 4 步的微观隔离也有现成机制，正核恒等式则需要超过一个小切片的分析连接。没有获得足够依据把其中一个候选判成“既 content、又单席可及”。** 这是拒绝本次独立实施靶，不是再次宣判整条局部支路必须等待量子 RH 的另外两条支路。

证据等级有意分开：第 1、2 步是编译实测；第 3、4 步是读过声明、证明机制及理论定义后的判形与规模预估，未声称已 elaborate 的 content 见证。下文的工时是工程预估，不是编译耗时实测。“未找到”始终限于所列检索范围。

工作基线：`d81bf5f3906cce92a516c3ab67ad9936f56a4607`；分支 `lane/math/qrh-local-readout-probe-0911`。Mathlib pin 为 `db584cd6d46c92f209a44c0f1c829460d327499d`，Lean `v4.33.0`。以下 `M/` 指 `.lake/packages/mathlib/Mathlib/`，可按同一路径在 [钉版 Mathlib](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib) 定位；行号按本席钉版源码。

本席完整阅读了 `CLAUDE.md` 与 `agents/CONTEXT.md`。执行者为一个 Codex worker，独立评审数 0，未调用子 agent，未应用 skill。交付限于本目录报告；未新增 D5、Blueprint、L note 或冻结对象，未运行 `make deposit*` / `make cover`，不申请 PR。治理散文扫描与 L note locator 条件没有对应新增对象。

实际命令及退出码见 [收据索引](receipts.md)，未截断输出见 [原始收据](receipts.jsonl)，成功编译的完整文本及成本见 [绑定探针](bind-probe.md)。阴性正则使用 `git grep -P` / `rg`；R082→R083、R069/R074→R073、R092/R093→R100 提供相同正则特性的阳性对照，R099 验证 `\bMathlib\b`。未用文件名未命中替代机制检索。

## 1. 实际素数的局部有限性：一步绑定即得

**现成件。**

| 声明 | 出处 | 实际作用 |
| --- | --- | --- |
| `Set.finite_Icc` | `M/Order/Interval/Finset/Defs.lean:515` | 在局部有限序上取有限区间；这里实例化为 **ℕ** |
| `Set.finite_le_nat` | `M/Data/Set/Finite/Basic.lean:619` | 同一自然数上界路线的替代入口 |
| `Real.le_exp_of_log_le` | `M/Analysis/SpecialFunctions/Log/Basic.lean:170` | `log p ≤ b` 推出 `(p : ℝ) ≤ exp b` |
| `Nat.le_floor_iff` | `M/Algebra/Order/Floor/Defs.lean:140` | 把实数上界转成 `p ≤ ⌊exp b⌋₊` |
| `IsCompact.bddAbove` | `M/Topology/Order/Compact.lean:324`；`K.isCompact.bddAbove` 已实际编译使用 | 把任意紧集归到同一上界 |
| `primeSummand_hasFiniteSupport`、`primeSummand_summable` | [PrimePoleTerms.lean](../../../D5/S3/Weil/PrimePoleTerms.lean)，32、58 行 | 仓内同族机制：紧支集使 von Mangoldt 配对仅剩有限项 |

先枚举模块公开 API 的实际命令为 R018：

```sh
git grep -n -P 'theorem |def ' -- D5/S3/Weil/PrimePoleTerms.lean
```

其后完整读过该文件（R014）。它使用偶的 `WeilTestFunction`、`Λ(n)` 及正负对数两项，不能直接把该 `primeTerm` 当作本题的实际素数单侧分布。R008 同时枚举了 `Weil/TestFunctions`、`Convention`、`PrimeJumpDecomposition`、`PrimeOnlyNoGap`；后两者分别是有限素数幂能量和圆上 Fourier 能量，并未给出本题对象。

区间结论的成功 Lean 项只有：

```lean
example (a b : ℝ) : Set.Finite {p : ℕ | p.Prime ∧ Real.log p ∈ Set.Icc a b} :=
  (Set.finite_Icc 0 ⌊Real.exp b⌋₊).subset fun p hp ↦
    ⟨Nat.zero_le p, (Nat.le_floor_iff (Real.exp_pos b).le).2
      (Real.le_exp_of_log_le hp.2.2)⟩
```

注意：不是调用“实数区间有限”；实数区间通常无限。`a` 与素数性甚至不参与上界证明。因而这里也不需要素数定理、素数计数或 Dirichlet 级数收敛。

**缺什么。** 在 D5 的类型、素数配对与对数有限性检索（R004、R012、R042）中未找到本题的具名 `finite_prime_logs`；缺的是专用陈述的名字。通用机制已经齐全。R011、R019、R102 检索并核对了上述有限集、对数与 floor API。

**判形预估及规模。** `bind-only`，并且已实测；不是第一个有内容的步骤。任意紧集版仍只加 `bddAbove` 的见证提取。单席充分，最小交付就是这段绑定证据，不应另立模块。

## 2. 测试函数配对连续性：`limitCLM` 连线已足够

**现成件。** R001、R002、R010 先枚举三个分布模块的 `theorem |def `，随后读过 `lemma` 与构造器正文（R005–R007、R061、R086–R088）。

| 声明 | 出处 | 已覆盖的义务 |
| --- | --- | --- |
| `Distribution` | `M/Analysis/Distribution/Distribution.lean:161` | `𝓓(Ω, ℝ) →L_c[ℝ] F`，真连续线性泛函 |
| `Distribution.delta`、`delta_apply` | 同文件 196、203 行 | 点求值及其连续性 |
| `TestFunction.ofSupportedInCLM` | `M/Analysis/Distribution/TestFunction.lean:319` | 固定紧支集空间向测试函数空间的连续线性嵌入 |
| `TestFunction.continuous_iff_continuous_comp` | 同文件 335 行 | **线性映射**逐紧支集连续的泛性质 |
| `TestFunction.mkCLM` | 同文件 353 行 | 需给全局线性律与逐紧集连续性 |
| **`TestFunction.limitCLM`** | 同文件 370 行 | 给逐紧集 CLM 和兼容等式即可，连全局线性律也代办 |
| `ContDiffMapSupportedIn.zero_on_compl` | `M/Analysis/Distribution/ContDiffMapSupportedIn.lean:159` | 紧支集之外取值为零 |
| `TestFunction.integralAgainstBilinCLM`、`_eq_integral` | `M/Analysis/Distribution/TestFunction.lean:704,727` | 局部可积密度的积分配对；辨认实际积分须给局部可积性 |

取 `Ω = ⊤`，定义

\[
A(\phi)=\sum_{p:\mathbb N}'\mathbf1_{p\ {m prime}}
 \frac{\log p}{\sqrt p}\phi(\log p).
\]

对每个紧集 `K`，第 1 步给有限集 `F_K = {p | p.Prime ∧ log p ∈ K}`。令

\[
A_K=\sum_{p\in F_K}\frac{\log p}{\sqrt p}
  (\delta_{\log p}\circ\mathrm{ofSupportedIn}_K).
\]

这是现成 CLM 的有限和，自动连续。**唯一要自己填写的证明是兼容等式**

\[
A(\mathrm{ofSupportedIn}_K\phi)=A_K(\phi).
\]

成功快照中，该义务由 `tsum_eq_sum`、`zero_on_compl`、有限和求值改写闭合。`TestFunction.limitCLM ℝ A (fun K hK => A_K)` 随即给出真正的 `𝓓'(⊤, ℝ)`；`primeDistribution φ = primePairing φ` 为 `rfl`。使用的是题设全部实际素数与实际权重，不是假设已给某个连续泛函，也不是有限截断后的替代目标。此处证明的是全部测试函数上的配对公式，没有额外声称 Dirac 级数在 `→L_c` 拓扑中的 `HasSum`。

**缺什么。** R042/R064 在 D5、R069 在全部 Mathlib 搜索 `primeDistribution|primePairing|primeLogMeasure|primeRamp|…`，未找到该专用构造的已有 owner。缺的专用定义和兼容等式均已在临时探针中绑定完成，不再把“需自行写几行”报成基础设施缺口。

也可以先造原子测度再走积分构造器，但需证明对应的 `LocallyIntegrableOn`。构造器在局部可积条件不成立时被定义为零；只写出它的名字不能证明配对就是预期的素数和。本席直接使用 `limitCLM`，无需单独造测度 API。

**判形及规模。** `bind-only`，编译确认；不是第一个有内容的步骤。完整快照 51 行，`#print axioms primeDistribution` 仅有 `[propext, Classical.choice, Quot.sound]`。最小交付已完成，成功后停止该候选实施。

成功命令（R037）：

```sh
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean
```

读数：`EXIT=0`，墙钟 **18.31 s**，`maximum resident set size` **2,630,926,336 bytes**。输出**未产生 `checked` 标签**；实际 profiler 字段为 `type checking 28.3ms`，不能把两者混写或把缺失读数写成零。缓存戳已读（R029）；没有提高 timeout 或预算。首次语法/API 误用失败与最终成功均保留在收据中。

## 3. 平移、统一支集、分部积分、差商和归一化：缺具体极限桥，不能用导数定义代替

**现成件。**

| 声明 | 出处 | 覆盖边界 |
| --- | --- | --- |
| `TestFunction.lineDerivCLM` | `M/Analysis/Distribution/TestFunction.lean:564` | 测试函数的方向导数是 CLM |
| `Distribution.lineDerivCLM`、`_apply` | `M/Analysis/Distribution/Distribution.lean:229,233` | `D_v T(φ) = -T(D_v φ)`，且对 **T** 连续 |
| `ContDiffMapSupportedIn.mkCLM`、`monoCLM` | `M/Analysis/Distribution/ContDiffMapSupportedIn.lean:717,844` | 用光滑性、支集与半范数界构造固定支集间 CLM |
| `ContDiffMapSupportedIn.withSeminorms`、`seminorm_top_le_iff` | 同文件 649、688 行 | 固定支集拓扑及逐点导数界转半范数界 |
| `norm_iteratedFDeriv_apply_le_seminorm_top` | 同文件 701 行 | 全域高阶导数的现成上界 |
| `WithSeminorms.tendsto_nhds` | `M/Analysis/LocallyConvex/WithSeminorms.lean:399` | 逐半范数收敛转为该空间收敛 |
| `iteratedFDeriv_comp_add_right`、`iteratedFDeriv_comp_sub` | `M/Analysis/Calculus/ContDiff/FTaylorSeries.lean:968,978` | 平移与任意阶导数交换 |
| `norm_iteratedFDeriv_eq_norm_iteratedDeriv` | `M/Analysis/Calculus/IteratedDeriv/Defs.lean:250` | 实轴上标量导数与 Fréchet 导数范数一致 |
| `taylor_mean_remainder_bound` | `M/Analysis/Calculus/Taylor.lean:390` | Banach 值 Taylor 余项界；`n=1` 的现成界为 `C h²`，不是自动 `C h²/2` |
| `HasDerivAt.tendsto_slope_zero` | `M/Analysis/Calculus/Deriv/Slope.lean:87` | 已知可微性后的普通差商极限 |
| `HasCompactSupport.integral_Ioi_deriv_eq` | `M/MeasureTheory/Integral/IntegralEqImproper.lean:822` | `∫_(b,∞) f' = -f(b)` |
| `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` | 同文件 1385 行 | 半直线分部积分，须填写边界极限及可积性 |
| `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt` | `M/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean:111` | 有限区间分部积分 |
| `SchwartzMap.compSubConstCLM` | `M/Analysis/Distribution/SchwartzSpace/Basic.lean:1068` | **Schwartz 空间**的平移，不能直接当 LF 测试函数平移 |

阴性查询 R082 与阳性对照 R083：

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:testFunctionTranslate|testFunctionDifferenceQuotient|tendsto_testFunction_differenceQuotient|differenceQuotient|compSubConstCLM)\b' -- Mathlib/Analysis/Distribution/TestFunction.lean Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean Mathlib/Analysis/Distribution/Distribution.lean
git -C .lake/packages/mathlib grep -n -P '\b(?:compSubConstCLM|taylor_mean_remainder_bound|lineDerivCLM)\b' -- Mathlib/Analysis/Distribution/TestFunction.lean Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean Mathlib/Analysis/Calculus/Taylor.lean | head -14
```

前者退出 1，后者退出 0。另有整个分布目录的同族词查询 R009/R063、全 Analysis 的余项/一致收敛查询 R041/R048/R049，以及仓内相关模块的 R027/R028。并非只查想象出的专用名字。

**缺什么，具体到应填写的边。** 在上述范围未找到以下组合结论：

1. `testFunctionTranslate`：`τ_h φ(x)=φ(x+h)`，支持空间取 `Ω=ℝ`。一般开集的任意平移未必仍留在同一开集，不能漏掉此条件。
2. `testFunctionDifferenceQuotient` 及 `tendsto_testFunction_differenceQuotient`：令 `q_hφ=h⁻¹(τ_hφ−φ)`。对 `|h|≤1`，把 `φ`、其导数与所有 `q_hφ` 放到同一个紧区间 `L`，再证明每个阶数 `r` 的半范数趋零。
3. `primeRampDistribution` 与 `primeRamp_secondDeriv`：`Z(T)=Σ_p a_p(T−log p)_+` 的局部可积性、对应正则分布，以及 `Z''=ν_P`。单个 ramp 的配对恒等式 `∫(t−a)_+ φ''(t)dt=φ(a)` 可用上表 FTC/IBP 两次；不需再造分部积分理论。仍须把局部有限求和、积分与导数的这条具体等式接好。
4. `normalizedPrimeReadout_pairing_limit`：归一化的**整段算子组合**极限，不能只给各因子的标量极限。

这些是便于下次检索的候选名字，不是声称本仓已有的声明。`Distribution.lineDerivCLM` 只定义极限应当等于什么；它没有证明参数 `h ↦ S_h T` 可微，更没有自动证明除以趋零归一化常数后的余项消失。

符号约定必须固定：原文 `S_h f(T)=f(T+h)`；其分布作用为 `(S_hT)(φ)=T(τ_{−h}φ)`，所以转置测试函数差商趋于 **`−φ'`**，分布差商趋于 `DT`。归一化因子为

\[
\frac{S_h-E_h}{E_h-1}
=\frac{h}{E_h-1}\frac{S_h-1}{h}-1\ \longrightarrow\ 2D-1,
\qquad E_h=e^{h/2}.
\]

这里 `h/(E_h−1)→2` 是 `Real.hasDerivAt_exp` 与 slope API 的绑定；真正要核对的是测试函数误差经过另三个差商后仍趋零。

**判形预估。** 固定 `h` 的平移构造、一个标量差商极限、一次 IBP、以及下列基础估计，均有很强的 bind-only 路线：

\[
p_r(q_h\phi-\phi')\le |h|\,p_{r+2}(\phi),\qquad 0<|h|\le1.
\]

对 `iteratedDeriv r φ` 实例化现成 Taylor 界，使用平移导数恒等式与 `seminorm_top_le_iff`，即可取得该界的候选证明链。负 `h` 可对参数函数 `t ↦ φ(x−t)` 使用正向 Taylor。统一紧区间可取 `supp φ ⊆ [a,b]` 后的 `[a−1,b+1]`。**不能把这个估计仅因未有专用名字就登记为 content 见证**；它很可能只是现成机制的组合。预登记曾将这条界列为拟议见证，本次检索后不升级为已成立的逃逸内容。

完整 LF 参数极限/归一化组合是第一个需要继续审计的分析连接；本席没有一条已排除绑定反路线的 content 见证。写很多拓扑适配行也不会自动改变判形。

还须区分两种结论。原文“分布意义”先按通常的**逐测试函数配对收敛**理解，不能人为强加更强拓扑来夸大阻塞。而 Mathlib `Distribution` 本身用 `→L_c`（测试函数空间紧集上的一致收敛）；若公开陈述使用该类型的 `Tendsto`，必须额外处理测试函数的紧集族。固定 `φ` 或固定支集的收敛不能未经证明升级。R092/R093 在两个测试函数模块中未找到该紧集族/有界族极限接口，R100 为同正则阳性对照。这是强版本的另一个义务，**不是弱版本的必要前置**。

**规模。** 固定紧区间、任意阶 `r` 的差商界及固定 `φ` 的 LF 收敛，预估约一个席位，但判形仍偏绑定，最小交付应是继续排除绑定的探针。包含实际 `Z''`、三次差商后的归一化余项及最终配对极限，预估 1–2 席；不能承诺同席兼得 content 判形。再要求 `→L_c` 的紧集族版本应另拆席。没有把未编译的预估当成本读数。

外部检索也实际执行：R036 的 `"TestFunction" "translation" language:Lean`、R050 的 `"TestFunction" "difference quotient" language:Lean` 均退出 0。读取 [TauCeti 钉版 Translation](https://github.com/TauCetiProject/TauCeti/blob/0e1a5a76bc3e0a5e509cf31335e0b2227cbdb6b7/TauCeti/Analysis/Sobolev/Translation.lean) 的公开列表与正文，命中 `W1p.eLpNorm_value_comp_add_sub_value_le_mul_enorm_gradient` 等，内容为 Sobolev/Lp 平移增量；读取 [AINTLIB 钉版 AuxAdmissible](https://github.com/CBirkbeck/AINTLIB/blob/160e446617a2168c34c95bbe7a76c4105b392434/projects/DedekindResidue/DedekindResidue/ExplicitFormula/AuxAdmissible.lean)，其 `auxF_diffQuot_*` 是 `(1−F(x))/x` 的可容许性，不是 LF 平移差商。两者不补上本题组合接口。该检索是具名有限查询，不声称穷尽 Lean 生态。

## 4. 三个终点：定义已找齐，按具体对象判

### 4.0 定义与 atom 的完整定位

以下全部出自同一卷 [QUANTUM-RH.md](../../develop/theory/QUANTUM-RH.md)，不是从定理 6 的恒等式反推定义。已直接打开 atom 及理论正文（R016、R020–R022、R039、R043/R044、R071、R089/R090）。

| 对象 | 定义 | 卷内行号 / atom |
| --- | --- | --- |
| `a_p, Z, E_h, S_h, Q_h, D_h` | `a_p=log p/√p`；`Z(T)=Σ_p a_p(T−log p)_+`；`E_h=e^(h/2)`；`S_h f(T)=f(T+h)`；`Q_h(z)=(z−E_h)(z−1)^3`；`D_h=Q_h(S_h)Z` | 12600 起；[1c5fed…](../../../Meta/Digestion/atoms/sha256/1c5fed879b9efbeda741100af3697e756eeacd1a7f82b58514a8f75eb7090a7f) |
| `w_E` | `[0,4]` 上连续分段仿射，节点值 `(0,E,−1−E,1,0)`，区间外为零 | 12667 起；[5b0244…](../../../Meta/Digestion/atoms/sha256/5b0244d70b104c063d191f912199325d3d19c349d3370e19b8f28a94e59b5e9d) 含局部核证明 |
| `k_h` | `k_h(s)=h w_{E_h}(s/h)`；`D_h(T)=Σ_p a_p k_h(log p−T)` | 15042 起的核心重述；[cfbabd…](../../../Meta/Digestion/atoms/sha256/cfbabda410067208101851bc0835de96018e0764ae4329537d312a65946be867) |
| `c(h), 𝓑_h` | **`c(h)=h³(e^(h/2)−1)`**；`𝓑_h=D_h/c(h)`，`h>0` | 初定义 12839 附近；15568 起重述；[102ce8…](../../../Meta/Digestion/atoms/sha256/102ce887e1d6068e19a166f2726d8309f56a3a1f7eae1217732c5f766be2872e) |
| `r_H, κ_H` | `r_H(v)=e^(−v/2)/(2(1−e^(−H/2))) · 1_[0,H](v)`；`κ_H` 是三个 `[0,H]` 均匀密度与 `r_H` 的卷积，`H>0` | 15699 起、式 (21)–(22)；[28522f…](../../../Meta/Digestion/atoms/sha256/28522f623189702dc45a74125b482c7e1fe24fe76136dfa928dc7d41ab2ae3e6) |
| 分布极限目标 | `Z''=ν_P`；`𝓑_h→2ν_P''−ν_P'` | 13095 起；[2aa748…](../../../Meta/Digestion/atoms/sha256/2aa74802d1b3ab3281fc74cb12781b7ab0f1423ab4aabb4a72d53e18b2550e42) |
| 双侧尖峰目标 | 任意固定素数 `p`，在 `log p−h/2`、`log p−2h` 两处的公式和渐近 | 13022 起；[254dfa…](../../../Meta/Digestion/atoms/sha256/254dfabdd7e130616e87747669cd2a83414b47d9683668df324c0b33e0149f7b) |
| 正核导数恒等式 | `k_H/c(H)=2κ_H''+κ_H'`，整体分布延拓 | 16040 起；[444f11…](../../../Meta/Digestion/atoms/sha256/444f11051be589c4b4239ce0954480b980f5ee5fa450781291d6b0124515350c)；证明在卷内 16068 起 |

其中 `κ_H` 可直接作确定性定义：设 `u_H=H⁻¹1_[0,H]`，则 `κ_H=((u_H*u_H)*u_H)*r_H`。无需先形式化随机路径、独立变量、鞅或局部概率误差。该定义忠于 28522f…；而用正核恒等式直接“定义 κ”会丢掉原文的指定卷积密度，不能这么换对象。

### 4.1 分布极限

**现成件。** 第 2 步真分布、`Distribution.lineDerivCLM`、第 3 步导数/FTC/Taylor API，足以定义目标 `2D²ν−Dν`。完整源式是

\[
\mathcal B_h=\frac{S_h-E_h}{E_h-1}
 \left(\frac{S_h-1}{h}\right)^3 Z
 \longrightarrow (2D-1)D^3Z=2D^2\nu-D\nu.
\]

**缺什么。** `primeRamp`、其正则分布、`primeRamp_secondDeriv`、`primeStencil`、`normalizedPrimeReadout` 及实际配对的极限桥，在 D5 的 R004/R012/R025/R033/R042/R068、Mathlib 的 R069 范围未找到完整对应链。源定义已齐，不是 theory atom 缺失。`Z` 不是测试函数；不能把它直接塞进只接受 `TestFunction` 的差商定理。应先作正则分布，或对每个测试函数把所有算子转置后作局部有限计算。

**判形与规模。** 简单的 `Z''=ν` 桥很可能仍是局部有限和加两次 FTC/IBP 的绑定；只写目标导数表达式肯定是绑定。全配对归一化极限尚需上述活跃余项证明，不能预先授予 content；预估 1–2 席，最小切片为单个 ramp 的分布二阶导数及局部有限求和识别，但该切片也须先按绑定排除。弱配对版本不依赖正核或微观尖峰；强拓扑版本的额外义务见第 3 节。

### 4.2 正核导数读出

**现成件。** R072 先通读 `M/Analysis/Convolution.lean` 的公开 API 列表：`MeasureTheory.convolution`（403）、`convolution_def`（421）、`Integrable.integrable_convolution`（520）、`HasCompactSupport.convolution`（529）、`support_convolution_subset`（631）。这些提供普通卷积、可积性与支集运算；导数作为分布也已存在。注意均匀密度和 `r_H` 在端点有跳跃，不能无条件实例化要求处处光滑密度的卷积微分定理。

**缺什么。** 在 D5 的 `kappa|kappaH|kappa_H|primeStencil|…` 加指数/正部公式查询 R068、Mathlib 的 R025/R033/R069 中未找到本题四个核对象及其连接定理。命中的 `kappa` 是 Hermitian 核负指标、外支集测试函数等不同对象；没有因为命中单词就认作 owner。

同席可写出 `uniformWindowDensity`、`truncatedExpDensity`、`positiveReadoutKernel`、`signedReadoutKernel`、`readoutNormalization` 的定义。**这些定义本身不证明恒等式。** 还需四重卷积的边界/微分识别，并使它等于由五项 stencil 得到的分段仿射核。

原文采用指数变换：

\[
\int e^{zs}\kappa_H(s)\,ds
=\left(\frac{e^{Hz}-1}{Hz}\right)^3
\frac{e^{Hz}-e^{H/2}}{2(e^{H/2}-1)(z-1/2)}.
\]

其后用导数乘子 `2z²−z` 与紧支集分布变换的单射性。若沿此路，需要能将非紧支集的 `e^(zs)` 与紧支集分布配对、说明 cutoff 独立性、填上变换单射性接口，并处理公式中 `z=0,1/2` 的可去点。直接卷积/IBP 路线可省掉变换设施，但仍要处理四次卷积的端点项。普通 `mellin` / L² Fourier 同构不能不作空间识别就替代这一链。

**判形与规模。** 定义和形式上的多项式因式分解是 bind-only。指定四重卷积与指定带符号核的整体分布恒等式是 content 候选，尚无已编译见证；从当前未类型化对象出发预估至少 2 席，不作为一小时独立实施靶。单席最小切片是两个密度及其质量/支集，或一个截断指数的分布导数；都须先排查积分/IBP 绑定，不能把前置定义收集本身算成 content。

`+κ_H'` 是核自变量 `s` 的导数；换成 `κ_H(log p−T)` 后一阶 `T` 导数变号，与 4.1 的 `−ν_P'` 一致，不是可忽略的约定差别。

### 4.3 微观尖峰

**现成件。** 除第 1 步有限集外，另实查到：

| 声明 | 出处 | 含义 |
| --- | --- | --- |
| `Set.Finite.isDiscrete` | `M/Topology/Separation/Basic.lean:807` | 有限集自动离散 |
| `Metric.exists_closedBall_inter_eq_singleton_of_discrete` | `M/Topology/MetricSpace/Pseudo/Basic.lean:178` | 离散集中的点有只含自身的正半径闭球 |
| `Real.log_lt_log_iff`、`strictMonoOn_log` | `M/Analysis/SpecialFunctions/Log/Basic.lean:158,249` | 正数上 log 单射/保序 |
| `Real.hasDerivAt_exp` | `M/Analysis/SpecialFunctions/ExpDeriv.lean:267` | `(E_h−1)/h→1/2` 的绑定入口 |
| `Nat.exists_infinite_primes` | `M/Data/Nat/Prime/Infinite.lean:33` | 如需排除所有 `T≥T₀` 上的统一界，可选足够大的素数 |

R076/R077 为同族隔离机制搜索，R079/R080 读了签名与正文，R081 为公开列表，R084 精确定位 `Set.Finite.isDiscrete`。这改变了对“单素数隔离可能是 content”的初判。

设 `x=log p`，先取实际素数对数在 `[x−1,x+1]` 的有限像集 `F`。`F.isDiscrete` 与上述闭球引理给 `r>0`，使 `closedBall x r ∩ F={x}`；再把半径缩到至多 1，即同时隔离整个实际素数对数集合。令 `h` 小到 `4h` 落在此半径内，两处读出窗口都只含 `p`。**原子隔离的机制已存在，不能另写一个邻素数间距常量就声称发现了不可替代的新机制。** 特别是 atom 只要求“足够小”，并不消费一个人为强化的显式阈值。

**缺什么。** R074 在 D5 检索 `primeSpike|primeLogIsolation|isolatedPrime|primeWindow|microscopicSpike|localPrimeKernel|primeStencil` 退出 1，R073 为同特性阳性对照；GitHub 的 `"Nat.Prime" "spike" language:Lean` 查询 R078 返回空列表。这些阴性只支持“未找到专用名字”。尚要定义实际 `Z,D_h,k_h,c(h),𝓑_h` 并证明有限和的 stencil/kernel 等式。无需先建 `κ_H`、正核导数定理或完整 LF 差商极限。

原文的最小数学结果应针对**任意素数** `p`：

\[
\begin{aligned}
\mathcal B_h(\log p-h/2)&=\frac{a_pE_h}{2h^2(E_h-1)},\\
\mathcal B_h(\log p-2h)&=-\frac{a_p(1+E_h)}{h^2(E_h-1)},\\
h^3\mathcal B_h(\log p-h/2)&\to a_p,\qquad
h^3\mathcal B_h(\log p-2h)\to-4a_p.
\end{aligned}
\]

局部核的两次求值为 `w_E(1/2)=E/2`、`w_E(2)=−(1+E)`。隔离后全素数和降成单项，接 `exp` 的 slope 极限即可。它没有建立“素数普遍服从随机模型”，也不需要 RH。

**判形与规模。** 单独“隔离一个实际素数”判为 bind-only 预估，理由是上面给出的可替代绑定链；两个核值、归一化与渐近同样是现成定理实例化和规范化。全双侧尖峰从标量对象出发预估约 1 席（有限和适配不顺时需拆开），但当前未识别出不可替代的 content 见证，不宜因结果有趣就授予独立模块。只做 `p=2` 的正向实例尤其不符合第 3.3 条，未实施。

## 已明确排除的假缺口与最终派席判断

以下全部实际检索/读过（R013、R062、R067、R095–R097），不列为本支路需要重建的设施：

| 声明 | 钉版出处 |
| --- | --- |
| `ArithmeticFunction.LSeriesSummable_vonMangoldt` | `M/NumberTheory/LSeries/Dirichlet.lean:381` |
| `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | 同文件 436 行；前提 `1 < s.re` |
| `MeasureTheory.measurePreserving_add_right` | `M/MeasureTheory/Group/Measure.lean:90` 的 `@[to_additive] measurePreserving_mul_right` 生成；不是源码精确名字未命中就缺失 |
| `MeasureTheory.Lp.compMeasurePreservingₗᵢ` | `M/MeasureTheory/Function/LpSpace/Basic.lean:632` |
| `Polynomial.aeval` | `M/Algebra/Polynomial/AlgebraMap.lean:257` |
| `MeasureTheory.Lp.fourierTransformₗᵢ` | `M/Analysis/Fourier/LpSpace.lean:50` |
| `mellin` | `M/Analysis/MellinTransform.lean:91` |
| `MeasureTheory.integral_tsum_of_summable_integral_norm` | `M/MeasureTheory/Integral/DominatedConvergence.lean:111` |
| `MeasureTheory.tendsto_integral_of_dominated_convergence` | 同文件 57 行；滤子版本在 68 行附近 |

两个 von Mangoldt 声明在仓内已有实际使用；它们不构成本题局部有限性或连续配对的前置障碍。其余 API 的存在不免除对应可积性、支集、空间和拓扑的具体假设。

| 切片 | 判形结算 / 预估 | 一席可及性 | 本次动作 |
| --- | --- | --- | --- |
| 素数对数紧集有限 | bind-only，编译证实 | 是 | 停手留绑定证据 |
| 实际 `ν_P : Distribution` | bind-only，编译证实 | 是 | 停手留绑定证据 |
| 固定支集平移/基础差商界 | 偏 bind-only，有具名 Taylor→半范数路线 | 约一席 | 不把缺专用 API 当内容 |
| 实际归一化配对极限 | 整体判形未证实；小前置仍偏绑定 | 预估 1–2 席 | 不承诺 content 实施 |
| 指定正核的整体导数恒等式 | content 候选；前置分析连接未闭合 | 预估至少 2 席 | 只定位定义与义务 |
| 单素数隔离及双侧尖峰 | 偏 bind-only，已找到隔离机制 | 约一席 | 不独立落地 |

**这条支路上没有本次可确认的、既非 bind-only 又单席可及的步骤，因为可压到单席的小切片均有已查到的绑定机制，而剩余完整归一化/正核连接尚未同时满足内容见证与单席前置闭合；最先值得继续探测的未连接边是第 3 步的实际测试函数差商与归一化组合极限。**
