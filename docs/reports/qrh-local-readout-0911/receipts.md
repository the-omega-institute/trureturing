# 检索与验证收据

工作目录为仓库根；Mathlib 路径均指钉版依赖。以下是实际执行的命令、实际退出码索引。完整 stdout/stderr 在 [receipts.jsonl](receipts.jsonl)，每行是一条带 `receipt`、`command`、`exit_code`、`output` 的 JSON 记录。收据来自本席记录，未重放已提交证明。

退出 1 的检索仅表示所列范围内未命中；退出 2 不作为阴性证据。带 `head` 的命令仅用于阅读 API 或阳性样本，不能证明全范围无命中。R035 指向了一个错误路径，后续 R053、R054、R055、R057 已改用有效路径。

阳性对照：R082 → R083（同有 `\b(?:...)\b`）；R069 / R074 → R073（同有 `\b(?:...)\b`）；R092 / R093 → R100（逐字相同正则）；R099 单独验证 `\bMathlib\b`。对象名检索还辅以 R004、R009、R012、R025、R027、R033、R041、R068 的类型、公式及同族 API 检索，不能将名字未命中解读成数学机制缺失。

## R001 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P 'theorem |def ' -- Mathlib/Analysis/Distribution/Distribution.lean
```

## R002 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P 'theorem |def ' -- Mathlib/Analysis/Distribution/TestFunction.lean
```

## R004 · exit 0

```sh
git grep -n -P '\b(?:Distribution|TestFunction|lineDerivCLM)\b|prime.*[Dd]istribution|prime.*[Ll]ocal.*[Ff]inite' -- D5
```

## R005 · exit 0

```sh
sed -n '1,285p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/Distribution.lean
```

## R006 · exit 0

```sh
sed -n '300,423p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean
```

## R007 · exit 0

```sh
sed -n '640,735p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean
```

## R008 · exit 0

```sh
git grep -n -P 'theorem |def ' -- D5/S3/Weil/Convention.lean D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition.lean D5/S3/Weil/PrimeOnly/PrimeOnlyNoGap.lean D5/S3/Weil/TestFunctions.lean
```

## R009 · exit 0

```sh
rg -n -i 'translat|comp.*(add|sub)|difference|quotient|tendsto|hasDeriv|integral.*deriv' .lake/packages/mathlib/Mathlib/Analysis/Distribution --glob '*.lean'
```

## R010 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P 'theorem |def ' -- Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean
```

## R011 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:finite_Icc|finite_Iic|finite_le_nat|finite_le_natCast|finite_preimage|finite_preimage_of|log_le_iff|le_exp|natCast_le|finite_inter)\b' -- Mathlib/Order/Interval/Finset Mathlib/Topology/Instances/ENNReal Mathlib/Topology/Algebra/Order Mathlib/Analysis/SpecialFunctions/Log Mathlib/Data/Nat/Prime Mathlib/Data/Set/Finite
```

## R012 · exit 0

```sh
git grep -n -P 'prime.*[Mm]easure|prime.*[Pp]air|ν_P|nuP|primeDistribution|log.*(finite|Finite)|(finite|Finite).*log|LocallyFinite.*[Pp]rime|[Pp]rime.*LocallyFinite' -- D5/S3/Weil D5/S3/Analytic
```

## R013 · exit 0

```sh
git grep -n -P '\b(?:LSeriesSummable_vonMangoldt|LSeries_vonMangoldt_eq_deriv_riemannZeta_div)\b' -- D5; git -C .lake/packages/mathlib grep -n -P '\b(?:LSeriesSummable_vonMangoldt|LSeries_vonMangoldt_eq_deriv_riemannZeta_div)\b' -- Mathlib
```

## R014 · exit 0

```sh
cat D5/S3/Weil/PrimePoleTerms.lean
```

## R015 · exit 0

```sh
sed -n '49,73p' docs/reports/digestion/qrh-deposit-screen-0909.md
```

## R016 · exit 0

```sh
cat Meta/Digestion/atoms/sha256/444f11051be589c4b4239ce0954480b980f5ee5fa450781291d6b0124515350c Meta/Digestion/atoms/sha256/28522f623189702dc45a74125b482c7e1fe24fe76136dfa928dc7d41ab2ae3e6 Meta/Digestion/atoms/sha256/cfbabda410067208101851bc0835de96018e0764ae4329537d312a65946be867 Meta/Digestion/atoms/sha256/102ce887e1d6068e19a166f2726d8309f56a3a1f7eae1217732c5f766be2872e
```

## R017 · exit 0

```sh
rg -n '分布|微观|平移|归一化|κ_H|k_H|𝓑_H|Z\(' docs/develop/theory/QUANTUM-RH.md | head -100
```

## R018 · exit 0

```sh
git grep -n -P 'theorem |def ' -- D5/S3/Weil/PrimePoleTerms.lean
```

## R019 · exit 0

```sh
rg -n 'le_exp|log_le|exp_log' .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean | head -60
```

## R020 · exit 0

```sh
sed -n '12600,12705p' docs/develop/theory/QUANTUM-RH.md
```

## R021 · exit 0

```sh
sed -n '13020,13140p' docs/develop/theory/QUANTUM-RH.md
```

## R022 · exit 0

```sh
sed -n '16068,16137p' docs/develop/theory/QUANTUM-RH.md
```

## R023 · exit 0

```sh
rg -n 'finite_preimage|finite_setOf|finite.*Iic|finite.*[Cc]ompact' .lake/packages/mathlib/Mathlib/Order/Filter .lake/packages/mathlib/Mathlib/Topology/Order .lake/packages/mathlib/Mathlib/Topology/Compactness
```

## R024 · exit 0

```sh
rg -n 'tendsto.*iff|hasBasis|tendsto.*structure|tendsto.*seminorm|tendsto.*norm' .lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean .lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean
```

## R025 · exit 0

```sh
rg -n -i 'distribution|testfunction|ramp|heaviside|positive.?part|piecewise|stieltjes' .lake/packages/mathlib/Mathlib/Analysis/Distribution .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean
```

## R026 · exit 0

```sh
rg --files .lake/packages/mathlib/Mathlib/MeasureTheory/Integral -g '*Parts*' -g '*Derivative*' -g '*Deriv*'
```

## R027 · exit 0

```sh
rg -n '(translat|compSubConst|compAdd|differenceQuotient|slope|tendsto.*deriv|hasDeriv.*[Cc]ontinuous)' D5/S3/Weil D5/S3/Analytic --glob '*.lean' | head -90
```

## R028 · exit 0

```sh
git grep -n -P 'theorem |def ' -- D5/S3/Weil/ZetaBridge/WeilPrimeThresholdParity.lean D5/S3/Weil/ZetaBridge/WeilPrimeActivationEdge.lean D5/S3/Weil/ZetaBridge/TranslationKineticEnergy.lean
```

## R029 · exit 0

```sh
cat .lake/.stratalint-lean-cache-stamp.json
```

## R030 · exit 0

```sh
rg -n 'def |abbrev |toCompact|toContinuous' .lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Spaces/CompactConvergenceCLM.lean | head -70
```

## R031 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P 'theorem |def ' -- Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean | head -60
```

## R032 · exit 0

```sh
rg -n 'theorem (tsum_eq_sum|sum_add|tsum_fintype)|lemma (tsum_eq_sum|le_floor|floor_le|natCast_le)' .lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum .lake/packages/mathlib/Mathlib/Algebra/Order/Floor
```

## R033 · exit 0

```sh
rg -n -i 'ramp|heaviside|(posPart|max|positive.?part).*([Dd]istribution|deriv)|([Dd]istribution|deriv).*(posPart|heaviside)' .lake/packages/mathlib/Mathlib/Analysis .lake/packages/mathlib/Mathlib/MeasureTheory --glob '*.lean' | head -60
```

## R034 · exit 1

```sh
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean
```

## R035 · exit 2

```sh
rg -n "(HasCompactSupport.*(comp|deriv|integrable)|norm_image_sub.*(deriv|fderiv)|norm_image_sub_le|norm_sub.*(fderiv|deriv))" .lake/packages/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/Support.lean
```

## R036 · exit 0

```sh
gh search code "\"TestFunction\" \"translation\" language:Lean" --limit 15 --json repository,path,url
```

## R037 · exit 0

```sh
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean
```

## R038 · exit 0

```sh
rg -n -P '\b(?:hasDerivAt_iff_tendsto_slope|tendsto_slope_zero|tendsto_slope_zero_right|integral_mul_deriv_eq_deriv_mul_of_hasDerivAt|compSubConstCLM)\b' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean .lake/packages/mathlib/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean
```

## R039 · exit 0

```sh
sed -n '12780,12875p' docs/develop/theory/QUANTUM-RH.md
```

## R040 · exit 1

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:compSubConstCLM|differenceQuotient|HasDerivAt|hasDerivAt_iff_tendsto_slope|integral_mul_deriv_eq_deriv_mul_of_hasDerivAt)\b' -- Mathlib/Analysis/Distribution/TestFunction.lean Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean Mathlib/Analysis/Distribution/Distribution.lean
```

## R041 · exit 0

```sh
rg -n 'tendstoUniformly.*(deriv|slope)|(?:deriv|slope).*tendstoUniformly|hasFDerivAt.*(BCF|boundedContinuous)|(?:hasFDerivAt|contDiff).*comp.*(sub|add)' .lake/packages/mathlib/Mathlib/Analysis --glob '*.lean' | head -70
```

## R042 · exit 0

```sh
git grep -n -P '\b(?:primeDistribution|primePairing|primeLogMeasure|primeReadout|primeRamp|testFunctionTranslate|testFunctionDifferenceQuotient|tendsto_testFunction_differenceQuotient|localReadout|normalizedLocalReadout)\b' -- D5
```

## R043 · exit 0

```sh
rg -l -P '## (?:极限不是普通函数，而是分布|定理 3：双侧微观尖峰)|# 一、固定局部读出，并把窗口大小作为真正的参数|## 局部核的精确形式' Meta/Digestion/atoms/sha256
```

## R044 · exit 0

```sh
cat Meta/Digestion/atoms/sha256/1c5fed879b9efbeda741100af3697e756eeacd1a7f82b58514a8f75eb7090a7f Meta/Digestion/atoms/sha256/c8c9c27fd06d332c8d7a2ea1ec469ba9d0b2f58a7b254bd3a1996d259453e347 Meta/Digestion/atoms/sha256/5b0244d70b104c063d191f912199325d3d19c349d3370e19b8f28a94e59b5e9d Meta/Digestion/atoms/sha256/254dfabdd7e130616e87747669cd2a83414b47d9683668df324c0b33e0149f7b Meta/Digestion/atoms/sha256/b745358303e7d849ef95eec3511630d81d525fa44d0bbb646c9070bcefaa111a Meta/Digestion/atoms/sha256/2aa74802d1b3ab3281fc74cb12781b7ab0f1423ab4aabb4a72d53e18b2550e42
```

## R046 · exit 0

```sh
rg -n 'theorem |def ' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean | head -60
```

## R047 · exit 0

```sh
rg -n 'tsupport.*(comp|add|sub)|HasCompactSupport.comp' .lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean
```

## R048 · exit 0

```sh
rg -n 'hasDerivAt_iff_tendsto_slope|tendsto_slope_zero|norm_sub_sub_le|norm.*sub.*fderiv|sub.*fderiv.*le' .lake/packages/mathlib/Mathlib/Analysis/Calculus --glob '*.lean' | head -70
```

## R049 · exit 0

```sh
rg -n 'iteratedFDeriv.*(comp_add|comp_sub|add_const)|iteratedFDeriv.*comp.*(add|sub)' .lake/packages/mathlib/Mathlib/Analysis/Calculus --glob '*.lean'
```

## R050 · exit 0

```sh
gh search code '"TestFunction" "difference quotient" language:Lean' --limit 15 --json repository,path,url
```

## R051 · exit 0

```sh
sed -n '1,245p' /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/TauCetiTranslation.lean
```

## R052 · exit 0

```sh
rg -n -P 'theorem |lemma |def |sorry|axiom|import ' /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/TauCetiTranslation.lean
```

## R053 · exit 0

```sh
rg -n 'integral_Ioi.*hasDerivAt|integral_Ioi_deriv|integral_Iic.*hasDerivAt|integral_mul_deriv.*integrable' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral --glob '*.lean' | head -40
```

## R054 · exit 0

```sh
rg -n 'HasCompactSupport.comp_homeomorph|theorem.*(tsupport_comp|hasCompactSupport_comp)|lemma.*(tsupport_comp|hasCompactSupport_comp)' .lake/packages/mathlib/Mathlib --glob '*.lean' | head -30
```

## R055 · exit 0

```sh
sed -n '790,845p' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean
```

## R056 · exit 0

```sh
sed -n '375,452p' .lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean
```

## R057 · exit 0

```sh
sed -n '1320,1395p' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean
```

## R060 · exit 0

```sh
rg -n -P 'theorem |def |lemma |\b(?:TestFunction|translation|difference quotient)\b' /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/AuxAdmissible.lean
```

## R061 · exit 0

```sh
sed -n '623,765p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean
```

## R062 · exit 0

```sh
rg -n -P '\b(?:measurePreserving_add_right|compMeasurePreservingₗᵢ|aeval|fourierTransformₗᵢ|mellin|integral_tsum_of_summable_integral_norm|tendsto_integral_of_dominated_convergence|LSeriesSummable_vonMangoldt|LSeries_vonMangoldt_eq_deriv_riemannZeta_div)\b' .lake/packages/mathlib/Mathlib/MeasureTheory/Group .lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSpace .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner .lake/packages/mathlib/Mathlib/Algebra/Polynomial/AlgebraMap.lean .lake/packages/mathlib/Mathlib/Analysis/Fourier .lake/packages/mathlib/Mathlib/Analysis/MellinTransform.lean .lake/packages/mathlib/Mathlib/NumberTheory/LSeries/Dirichlet.lean
```

## R063 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:compSubConstCLM|differenceQuotient|translation|translate|HasDerivAt|hasDerivAt_iff_tendsto_slope)\b' -- Mathlib/Analysis/Distribution
```

## R064 · exit 0

```sh
git grep -n -P '\b(?:primeDistribution|primePairing|primeLogMeasure|primeReadout|primeRamp|testFunctionTranslate|testFunctionDifferenceQuotient|tendsto_testFunction_differenceQuotient|normalizedLocalReadout|localReadout|kappa_H|kappaH|w_E|E_h)\b' -- D5
```

## R066 · exit 0

```sh
rg -n -P '\b(?:iteratedDeriv|norm_iteratedFDeriv|iteratedFDeriv_comp_add_right|iteratedFDeriv_comp_sub)\b' .lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean
```

## R067 · exit 0

```sh
rg -n -P '(?:theorem |lemma |def |to_additive[\s\S]*)(?:measurePreserving_add_right|measurePreserving_mul_right|integral_tsum_of_summable_integral_norm|tendsto_integral_of_dominated_convergence)' .lake/packages/mathlib/Mathlib/MeasureTheory
```

## R068 · exit 0

```sh
git grep -n -P '\b(?:kappa|kappaH|kappa_H|primeRamp|primeStencil|normalizedPrimeReadout)\b|(?:Real\.exp.*[/] *2.*- *1)|(?:max.*Real\.log)' -- D5/S3/Weil D5/S3/NumberTheory
```

## R069 · exit 1

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:primeDistribution|primeLogMeasure|primeRamp|kappa_H|kappaH|normalizedPrimeReadout|tendsto_testFunction_differenceQuotient)\b' -- Mathlib
```

## R070 · exit 0

```sh
rg -n -P '\b(?:exists_infinite_primes|infinite_setOf_prime|exists_prime_gt|strictMonoOn_log|log_lt_log_iff|exp_pos|hasDerivAt_exp|tsum_eq_sum|tsum_add|sum_congr)\b' .lake/packages/mathlib/Mathlib/Data/Nat/Prime/Infinite.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ExpDeriv.lean .lake/packages/mathlib/Mathlib/Topology/Algebra/InfiniteSum/Defs.lean
```

## R071 · exit 0

```sh
sed -n '13010,13165p' docs/develop/theory/QUANTUM-RH.md
```

## R072 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P 'theorem |def ' -- Mathlib/Analysis/Convolution.lean | head -60
```

## R073 · exit 0

```sh
git grep -n -P '\b(?:primeSummand|primeTerm|primeWeight|activePrimePowers)\b' -- D5/S3/Weil/PrimePoleTerms.lean D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition.lean | head -25
```

## R074 · exit 1

```sh
git grep -n -P '\b(?:primeSpike|primeLogIsolation|isolatedPrime|primeWindow|microscopicSpike|localPrimeKernel|primeStencil)\b' -- D5
```

## R075 · exit 0

```sh
rg --files Meta/Digestion/atoms/sha256 | rg '28522f623189702|444f11051be589|1c5fed879b9efb|254dfabdd7e130|102ce887e1d606|cfbabda4100672|2aa74802d1b3ab|5b0244d70b104c'
```

## R076 · exit 0

```sh
rg -n -P '(?:theorem |lemma ).*(?:finite|Finite|isolated|discrete|exists_pos).*|(?:Finite|DiscreteTopology).*(?:disjoint|ball|nhds|dist)' .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean .lake/packages/mathlib/Mathlib/Topology/DiscreteSubset.lean
```

## R077 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:Finite|finite)\b.*(?:dist|ball|nhds)|(?:exists_pos.*(?:dist|ball))' -- Mathlib/Topology | head -65
```

## R078 · exit 0

```sh
gh search code '"Nat.Prime" "spike" language:Lean' --limit 15 --json repository,path,url
```

## R079 · exit 0

```sh
sed -n '156,188p' .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean
```

## R080 · exit 0

```sh
sed -n '165,230p' .lake/packages/mathlib/Mathlib/Topology/DiscreteSubset.lean
```

## R081 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P 'theorem |def ' -- Mathlib/Topology/DiscreteSubset.lean | head -60
```

## R082 · exit 1

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:testFunctionTranslate|testFunctionDifferenceQuotient|tendsto_testFunction_differenceQuotient|differenceQuotient|compSubConstCLM)\b' -- Mathlib/Analysis/Distribution/TestFunction.lean Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean Mathlib/Analysis/Distribution/Distribution.lean
```

## R083 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:compSubConstCLM|taylor_mean_remainder_bound|lineDerivCLM)\b' -- Mathlib/Analysis/Distribution/TestFunction.lean Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean Mathlib/Analysis/Calculus/Taylor.lean | head -14
```

## R084 · exit 0

```sh
rg -n -P '(?:Finite.*isDiscrete|[.]isDiscrete.*Finite|Finite.*discreteTopology)' .lake/packages/mathlib/Mathlib/Topology
```

## R086 · exit 0

```sh
sed -n '150,240p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/Distribution.lean
```

## R087 · exit 0

```sh
sed -n '689,736p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean
```

## R088 · exit 0

```sh
sed -n '310,383p' .lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean
```

## R089 · exit 0

```sh
sed -n '15685,15782p' docs/develop/theory/QUANTUM-RH.md
```

## R090 · exit 0

```sh
sed -n '16033,16110p' docs/develop/theory/QUANTUM-RH.md
```

## R092 · exit 1

```sh
rg -n -P '\b(?:IsCompact|IsVonNBounded|IsBounded|Tendsto|tendsto|Equicontinuous|Bounded)\b' .lake/packages/mathlib/Mathlib/Analysis/Distribution/TestFunction.lean
```

## R093 · exit 1

```sh
rg -n -P '\b(?:IsCompact|IsVonNBounded|IsBounded|Tendsto|tendsto|Equicontinuous|Bounded)\b' .lake/packages/mathlib/Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean
```

## R094 · exit 0

```sh
rg -n -P '\b(?:le_floor_iff|norm_iteratedFDeriv_eq_norm_iteratedDeriv|tendsto_nhds)\b' .lake/packages/mathlib/Mathlib/Algebra/Order/Floor/Semiring.lean .lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean .lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean
```

## R095 · exit 0

```sh
sed -n '80,98p' .lake/packages/mathlib/Mathlib/MeasureTheory/Group/Measure.lean
```

## R096 · exit 0

```sh
sed -n '105,126p' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean
```

## R097 · exit 0

```sh
sed -n '49,71p' .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean
```

## R099 · exit 0

```sh
git grep -n -P '\bMathlib\b' -- D5/S3/Weil/PrimePoleTerms.lean
```

## R100 · exit 0

```sh
git -C .lake/packages/mathlib grep -n -P '\b(?:IsCompact|IsVonNBounded|IsBounded|Tendsto|tendsto|Equicontinuous|Bounded)\b' -- Mathlib/Analysis/LocallyConvex/WithSeminorms.lean | head -12
```

## R102 · exit 0

```sh
rg -n -P '(?:theorem|lemma) le_floor_iff\b' .lake/packages/mathlib/Mathlib
```

## R103 · exit 0

```sh
rg -n -P '^(namespace |(?:protected )?(?:theorem|lemma|def) integral_Ioi_mul_deriv_eq_deriv_mul|(?:protected )?(?:theorem|lemma|def) convolution\b)' .lake/packages/mathlib/Mathlib/Analysis/Convolution.lean .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean
```

## R105 · exit 0

```sh
rg -n -P '(?:theorem|lemma) IsCompact.bddAbove\b' .lake/packages/mathlib/Mathlib/Topology
```
