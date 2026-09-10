# 绑定探针：原始成功快照

此文件是报告中的文本证据，不是仓库 Lean 模块，未加入任何构建、Blueprint、L note 或冻结面。

预登记原文：

```text
本探针先试绑定，不创建 D5 模块。
候选 1: 任意 [a,b] 中的素数对数有限，预测为 Set.finite_Icc + Real.le_exp_of_log_le + Nat.le_floor 的绑定。
候选 2: primePairing phi = tsum_p a_p phi(log p)，用 TestFunction.limitCLM 与固定紧集内的有限 Dirac 和构造真正 Distribution，预测仍为绑定；若编译成功且只用该链，停止此候选实施。
后续内容候选: 平移差商在统一紧支集的全部导数半范数中收敛；拟议见证是统一 Taylor 余项估计及向 LF 拓扑的传递，不以 lineDerivCLM 的定义冒充该极限。报告须另查端点定义后才判断单席规模。
```

以下 51 行在仓外临时路径编译成功；未用 `sorry` 或增加公理。第一轮因误写 `real_smul` 和未展开函数零而失败（R034），修正为 `smul_eq_mul` 与 `Pi.zero_apply` 后得到 R037。失败轮的 `sorryAx` 不属于以下成功快照。

```lean
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat

open Set TopologicalSpace
open scoped Distributions

example (a b : ℝ) : Set.Finite {p : ℕ | p.Prime ∧ Real.log p ∈ Set.Icc a b} :=
  (Set.finite_Icc 0 ⌊Real.exp b⌋₊).subset fun p hp ↦
    ⟨Nat.zero_le p, (Nat.le_floor_iff (Real.exp_pos b).le).2
      (Real.le_exp_of_log_le hp.2.2)⟩

private theorem finite_prime_logs (K : Compacts ℝ) :
    Set.Finite {p : ℕ | p.Prime ∧ Real.log p ∈ (K : Set ℝ)} := by
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove
  exact (Set.finite_Icc 0 ⌊Real.exp b⌋₊).subset fun p hp ↦
    ⟨Nat.zero_le p, (Nat.le_floor_iff (Real.exp_pos b).le).2
      (Real.le_exp_of_log_le (hb hp.2))⟩

noncomputable def primePairing (φ : 𝓓((⊤ : Opens ℝ), ℝ)) : ℝ :=
  ∑' p : ℕ, if p.Prime then Real.log p / Real.sqrt p * φ (Real.log p) else 0

noncomputable def primeDistribution : 𝓓'((⊤ : Opens ℝ), ℝ) := by
  classical
  apply TestFunction.limitCLM ℝ primePairing
    (fun K hK ↦ ∑ p ∈ (finite_prime_logs K).toFinset,
      (Real.log p / Real.sqrt p) •
        ((Distribution.delta (Real.log p)).comp (TestFunction.ofSupportedInCLM ℝ hK)))
  intro K hK φ
  change (∑' p : ℕ, if p.Prime then Real.log p / Real.sqrt p * φ (Real.log p) else 0) = _
  rw [tsum_eq_sum (s := (finite_prime_logs K).toFinset)]
  · simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Distribution.delta_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [if_pos ((finite_prime_logs K).mem_toFinset.mp hp).1]
    rfl
  · intro p hp
    by_cases hprime : p.Prime
    · rw [if_pos hprime]
      have hout : Real.log p ∉ (K : Set ℝ) := fun hx ↦
        hp ((finite_prime_logs K).mem_toFinset.mpr ⟨hprime, hx⟩)
      simp only [φ.zero_on_compl hout, Pi.zero_apply, mul_zero]
    · simp only [if_neg hprime]

example (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    primeDistribution φ = primePairing φ := rfl

#print axioms primeDistribution
```

成功命令与完整输出：

```sh
/usr/bin/time -l lake env lean -Dprofiler=true -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 /var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean```

```text
import took 12.9s
/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean:34:15: warning: `ContinuousLinearMap.sum_apply` has been deprecated: Use `sum_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sum_apply` to `sum_apply x`).
/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean:34:46: warning: `ContinuousLinearMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean:35:6: warning: This simp argument is unused:
  ContinuousLinearMap.comp_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Distribution.delta_apply,
    smul_eq_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
/var/folders/7r/h8yjr2y927n8m2kh38c18n9w0000gp/T/consensus-rnd/sshx/qrh-local-probe-0911/attempt-1/BindProbe.lean:35:38: warning: This simp argument is unused:
  Distribution.delta_apply

Hint: Omit it from the simp argument list.
  [apply] simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
'primeDistribution' depends on axioms: [propext, Classical.choice, Quot.sound]
cumulative profiling times:
	attribute application 0.0436ms
	blocked (unaccounted) 11.5ms
	congr simp thm 1.15ms
	elaboration 27.3ms
	fix level params 0.104ms
	import 12.9s
	initialization 20.4ms
	instantiate metavars 0.243ms
	interpretation 835ms
	let-to-have transformation 0.345ms
	linting 5.86ms
	module linting 0.00146ms
	overlappingInstancesLinter 10.3ms
	parsing 1.89ms
	process pre-definitions 5.94ms
	share common exprs 0.878ms
	simp 14.8ms
	tactic execution 56.9ms
	tacticAnalysis 12.8ms
	type checking 28.3ms
	typeclass inference 78.3ms
       18.31 real         1.53 user         5.39 sys
          2630926336  maximum resident set size
                   0  average shared memory size
                   0  average unshared data size
                   0  average unshared stack size
              149971  page reclaims
              126784  page faults
                   0  swaps
                   0  block input operations
                   0  block output operations
                   0  messages sent
                   0  messages received
                   0  signals received
               37405  voluntary context switches
              136353  involuntary context switches
          5980557424  instructions retired
          3356442011  cycles elapsed
           136502824  peak memory footprint
EXIT=0
```

`checked`：本次输出未产生该标签，不能报为 0 秒；实际 profiler 字段是 `type checking 28.3ms`。墙钟 18.31 s；maximum resident set size 2,630,926,336 bytes（约 2.63 GB / 2.45 GiB）。不是 `peak memory footprint` 那个较小读数。没有修改 timeout、heartbeats 或构建预算。成功后未继续修饰该探针；deprecated / unused simp 警告原样保留。

| 对象 / 声明 | proof_shape | 直接 D5 冻结依赖（GID / statement_id） | escape_witness | admission_basis |
| --- | --- | --- | --- | --- |
| 区间有限性 example / finite_prime_logs | bind-only | 无（仅钉版 Mathlib） | 无 | 不申请落地 |
| primePairing | 定义，不单独充当内容 | 无 | 无 | 不申请落地 |
| primeDistribution / 配对等式 example | bind-only | 无（仅钉版 Mathlib） | 无 | 不申请落地 |

公理闭包：`[propext, Classical.choice, Quot.sound]`。成本实测只支持本快照，不外推为第 3、4 步的编译成本或工时。
