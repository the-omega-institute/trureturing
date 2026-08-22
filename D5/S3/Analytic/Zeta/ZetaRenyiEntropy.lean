/- GID: D5/S3/Analytic/Zeta/ZetaRenyiEntropy
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Define countable Renyi entropy and compute it for the zeta law. -/

import Mathlib
/- Provenance: Native proof over pinned mathlib. -/
import D5.S3.Analytic.Zeta.ZetaEntropy
import D5.S3.Analytic.ZetaGibbs

/- Search and proof receipt (2026-08-22).

   Generality and placement.
   * Tag: `I`. The rule `能免费一般化者必须一般化陈述` governs statement form, so
     `countableRenyiEntropy` is defined for every `PMF ℕ`; no zeta datum is built into it.
     Placement rule: `不预建空壳;`
     `抽象只在第二个实例或已证实的压力出现时才上收`.
     There is one countable-Renyi consumer, this zeta result, so article 8 does not
     license a new general module. The general definition is therefore kept in this `I` file.
     This repeats the discoverability debt of the general countable-Shannon API frozen inside
     `ZetaEntropy.lean`; a second consumer, or an SL-010-blocked `G` consumer, is the recorded
     trigger to hoist both APIs rather than creating an empty abstraction now.
   * Repository imports, one by one: `D5.S3.Analytic.Zeta.ZetaEntropy` -- `I`;
     `D5.S3.Analytic.ZetaGibbs` -- `I`. `Mathlib` is external and has no repository tag.

   Thinness, per theorem (the definition is not a theorem claim).
   * `partition_toReal_eq_zeta_re` is THIN: apply `Complex.re` to the imported partition theorem.
   * `tsum_real_weight_eq_partition_toReal` is THIN: convert one already-summable nonnegative
     real p-series to and from `ENNReal`.
   * `zeta_renyi_power_pointwise` is THIN: distribute `Real.rpow` and multiply its exponents.
   * `zeta_renyi_power_summable` is THIN but load-bearing: `1 < alpha*s` is passed to the imported
     p-series theorem, deriving summability rather than assuming it.
   * `zeta_renyi_power_sum` is SUBSTANTIVE: it combines the pointwise normalization, justified
     `tsum` factorization, and both real zeta conversions.
   * `zeta_renyi_entropy_eq` is THIN: unfold the general entropy and apply the power-sum theorem.

   Attribute audit of every cited load-bearing declaration.
   * Repository: `pmfReal` and `zeta_real_apply` (`ZetaEntropy.lean:153,192`), and
     `partitionFunction`, `summable_real_weight`, `zetaDist`, and
     `partition_function_toReal_eq_riemannZeta` (`ZetaGibbs.lean:31,35,55,64`) carry no
     attributes. Same-line and preceding-line attribute searches found no alias or `to_additive`
     source for any of them.
   * Pinned mathlib: `Real.rpow_nonneg` (`Pow/Real.lean:163`) CARRIES `@[bound]` on the preceding
     line; `Real.rpow_mul` (412), `Real.mul_rpow` (476), and `Real.inv_rpow` (481) carry none.
     The same names under `NNReal` and `ENNReal` were rejected as different declarations: their
     bases are `ℝ≥0`/`ℝ≥0∞`, while the resolved declarations take real bases plus
     nonnegativity proofs.
   * `ENNReal.toReal_ofReal` (`Data/ENNReal/Basic.lean:244`) CARRIES `@[simp]` on the preceding
     line; `ENNReal.toReal_nonneg` (268) CARRIES `@[simp]` on the SAME LINE;
     `ENNReal.ofReal_tsum_of_nonneg` (`InfiniteSum/ENNReal.lean:564`) carries none.
   * Dot notation was audited by resolved identity: `n.cast_nonneg` is `Nat.cast_nonneg`
     (`Data/Nat/Cast/Order/Ring.lean:34`), which CARRIES `@[simp]`; `.mul_right` is
     `Summable.mul_right` (`InfiniteSum/Ring.lean:48`), and `.tsum_mul_right` is
     `Summable.tsum_mul_right` (59); both carry none. Other same-named `tsum_mul_right`
     declarations have different `NNReal`/`ENNReal` or unqualified typeclass surfaces and were
     rejected as different declarations.
   * `tsum_nonneg` has no declaration line: it is explicitly renamed from `one_le_tprod` by
     bare `@[to_additive tsum_nonneg]` (`InfiniteSum/Order.lean:168-169`), so no listed attribute
     propagates. No load-bearing declaration is generated with `to_additive (attr := ...)`, and
     the alias scan found no load-bearing alias carrying a same-line attribute.
   * `Complex.ofReal_re` (`Data/Complex/Basic.lean:88`) CARRIES `@[simp, norm_cast]`;
     `congrArg` (pinned core `Init/Prelude.lean:423`) carries none. The three closure axioms
     `propext` (`Init/Core.lean:1593`), `Quot.sound` (1789), and `Classical.choice`
     (`Init/Prelude.lean:816`) have no attribute line. All used names resolved in the compiling
     `import Mathlib` scratch; no declaration is reported UNRESOLVED.

   Automation probe, actually executed in run-local `ZetaRenyiScratch.lean`.
   * For EACH of the six theorem statements, `solve | decide`, plain `simp`, `omega`, and
     `norm_num` failed to close the goal.
   * Single-lemma `simp only` also failed to close: the partition-real statement with
     `partition_function_toReal_eq_riemannZeta`; the real-tsum statement with each of
     `summable_real_weight`, `ENNReal.ofReal_tsum_of_nonneg`, `ENNReal.toReal_ofReal`, and
     `tsum_nonneg`; the pointwise statement with each of `zeta_real_apply`,
     `Real.rpow_nonneg`, `ENNReal.toReal_nonneg`, `Real.mul_rpow`, `Real.rpow_mul`, and
     `Real.inv_rpow`; summability with each of `zeta_renyi_power_pointwise`,
     `summable_real_weight`, and `Summable.mul_right`; the power sum with each of
     `zeta_renyi_power_pointwise`, `summable_real_weight`, `Summable.tsum_mul_right`,
     `tsum_real_weight_eq_partition_toReal`, and `partition_toReal_eq_zeta_re`; the closed form
     with each of `countableRenyiEntropy` and `zeta_renyi_power_sum`.
   * An initial probe incorrectly used `fail_if_success norm_num`, which tests tactic execution
     rather than closure. It was rejected and rerun with `fail_if_success (solve | ...)`; the
     corrected probe compiled with zero resolution errors. The scratch file was deleted.

   Candidates inspected versus declarations doing real work.
   * Inspected candidates: pinned Mathlib `InformationTheory/`, `zeta_eq_tsum_one_div_nat_cpow`,
     `riemannZeta_re_pos_of_one_lt`, `Real.summable_nat_rpow`; repository
     `RenyiDivergence/Basic.lean`, `RenyiDivergence/PowerAdditivity.lean`, and the six existing
     direct zeta files. The finite Renyi API has the wrong carrier; the direct complex series
     route is longer than the already-frozen partition conversion.
   * Real work: repository `zeta_real_apply`, `summable_real_weight`, and
     `partition_function_toReal_eq_riemannZeta`; mathlib `ENNReal.ofReal_tsum_of_nonneg`,
     `ENNReal.toReal_ofReal`, `tsum_nonneg`, the four audited `Real.rpow` lemmas, and the two
     audited `Summable` multiplication lemmas.

   Search provenance, scope, and strength.
   * SUPPLIED BY THE DISPATCHER: Mathlib has no Shannon/Renyi distribution entropy and its
     `InformationTheory/` contents are Hamming, Coding, and Kullback-Leibler; 13 repository files
     reference finite `renyiDivergence`, none with `tsum`; `renyiEntropy`, `countableRenyi`, and
     `collisionEntropy` have zero repository hits; no zeta/alpha power sum exists; the target
     directory has six direct files and `RenyiDivergence/` has exactly twelve.
   * ADDED AFTER REVIEW, measured by the coordinator rather than by the worker. Three
     load-bearing declarations were absent from the audit above. `inv_nonneg` does real work once,
     at line 150; it is an `iff`, and the `.mpr` there resolves to `Iff.mpr`, whose structure is
     declared in pinned Lean core at `Init/Core.lean:188`. At line 190 the `.elim` on a `False`
     resolves to `False.elim`. **Neither `Iff.mpr` nor `False.elim` occurs literally anywhere in
     this file** — dot notation resolves to them — so a spelling-based audit cannot reach them and
     they must be audited by resolved identity. Note the coherence: `False.elim` is load-bearing
     only because of the `by_cases` branch that discharges `alpha ≠ 1`, so the guard retained
     below brings its own audit obligation with it.
   * A CONTESTED POINT, RULED AND RECORDED so it is not re-opened. A probe established that
     `zeta_renyi_entropy_eq` still compiles with `halpha_ne_one` REMOVED — its proof never uses the
     hypothesis. Under the natural-generality obligation that would make it dead weight to be
     dropped. **It is kept.** The hypothesis guards a junk instance rather than carrying proof
     weight: at `alpha = 1` both sides of the identity collapse to Lean's totalized zero, so a
     version without the guard would assert an equation between two artifacts and could be read as
     saying the order-one Renyi entropy is zero, which it is not. Two independent review seats,
     asked through different lenses — what the statement communicates to a reader, and natural
     generality against article 8 — converged on keeping it.
   * A SUGGESTED RENAME, DECLINED with its reason. A seat proposed renaming the definition to
     something like `countableRenyiEntropyFormula` to signal totalization. Declined: totalization
     is the convention throughout Lean and mathlib — `Real.log 0 = 0` is not named `logFormula` —
     so a name suffix would be noise, while the specific degeneracies belong in the docstring,
     which now states them. The name is unchanged and the docstring above carries the semantics.
   * Independently verified, separately: `find` returned exactly six Mathlib
     information-theory files and the entropy-name search found only binary/negMulLog utilities;
     `rg` returned 13 finite-Renyi reference files and zero `tsum`/`sum'` hits in them; each of the
     three proposed names returned zero; mathematical-content searches returned zero zeta-alpha
     power sums in all `D5/`; pinned Lean core returned zero subject-API hits. Directory counts
     were independently 6 and 12 before this file. The repository and both pinned trees were
     searched separately.
   * Ranked scopes 1, 2, and 3 are complete. Scope 4 is omitted: proving the order-one limit
     requires a separate limit/interchange or zeta-derivative development and is not needed for
     the closed form. No obstruction affects scopes 1-3.
   * STRENGTHENING: no separate `0 < alpha` hypothesis is required. From `1 < s` and
     `1 < alpha*s`, positivity of `alpha` follows; the proof itself only needs nonnegative bases.
     The convergence side condition remains explicit, and `alpha != 1` remains explicit as the
     mathematical order-one guard despite Lean's totalized division. `#print axioms` reports
     exactly `{propext, Classical.choice, Quot.sound}` for the three main declarations. -/

namespace D5.S3.Analytic.Zeta.ZetaRenyiEntropy

open scoped ENNReal BigOperators
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy

noncomputable section

/-- The countable Renyi entropy formula, in nats, stated totally.

Two degeneracies are inherent to stating it as a total function and are NOT defects of the
formula's intended range. At `alpha = 1` the coefficient is Lean's totalized `1 / 0 = 0`, so this
returns `0` for every distribution — the order-one entropy is the LIMIT as `alpha` tends to one,
not this value, and every theorem below that means the Renyi entropy carries `alpha ≠ 1`
explicitly. Off the summable regime the bare `tsum` is likewise totalized to `0`; summability is a
separate proposition, proved here for the zeta law from `1 < alpha * s`. -/
def countableRenyiEntropy (alpha : ℝ) (p : PMF ℕ) : ℝ :=
  (1 / (1 - alpha)) * Real.log (∑' n, (pmfReal p n) ^ alpha)

lemma partition_toReal_eq_zeta_re (s : ℝ) (hs : 1 < s) :
    (partitionFunction s).toReal = (riemannZeta (s : ℂ)).re := by
  exact congrArg Complex.re (partition_function_toReal_eq_riemannZeta s hs)

lemma tsum_real_weight_eq_partition_toReal (s : ℝ) (hs : 1 < s) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) = (partitionFunction s).toReal := by
  have hsum := summable_real_weight s hs
  have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-s) :=
    fun n ↦ Real.rpow_nonneg n.cast_nonneg _
  rw [partitionFunction]
  change (∑' n : ℕ, (n : ℝ) ^ (-s)) =
    (∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (-s))).toReal
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg)]

lemma zeta_renyi_power_pointwise (s alpha : ℝ) (hs : 1 < s) (n : ℕ) :
    (pmfReal (zetaDist s hs) n) ^ alpha =
      (n : ℝ) ^ (-(alpha * s)) * ((partitionFunction s).toReal ^ alpha)⁻¹ := by
  rw [zeta_real_apply, Real.mul_rpow
    (Real.rpow_nonneg n.cast_nonneg _) (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ← Real.rpow_mul n.cast_nonneg, Real.inv_rpow ENNReal.toReal_nonneg]
  congr 2
  ring

/-- The Renyi power series of the zeta law is summable whenever `1 < alpha * s`. -/
theorem zeta_renyi_power_summable (s alpha : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) :
    Summable (fun n ↦ (pmfReal (zetaDist s hs) n) ^ alpha) := by
  rw [show (fun n ↦ (pmfReal (zetaDist s hs) n) ^ alpha) =
      fun n : ℕ ↦ (n : ℝ) ^ (-(alpha * s)) *
        ((partitionFunction s).toReal ^ alpha)⁻¹ by
    funext n
    exact zeta_renyi_power_pointwise s alpha hs n]
  exact (summable_real_weight (alpha * s) halpha_s).mul_right _

/-- The zeta law's Renyi power sum is the ratio of two real zeta values. -/
theorem zeta_renyi_power_sum (s alpha : ℝ) (hs : 1 < s)
    (halpha_s : 1 < alpha * s) :
    ∑' n, (pmfReal (zetaDist s hs) n) ^ alpha =
      (riemannZeta ((alpha * s : ℝ) : ℂ)).re /
        (riemannZeta (s : ℂ)).re ^ alpha := by
  have hbase := summable_real_weight (alpha * s) halpha_s
  rw [show (fun n ↦ (pmfReal (zetaDist s hs) n) ^ alpha) =
      fun n : ℕ ↦ (n : ℝ) ^ (-(alpha * s)) *
        ((partitionFunction s).toReal ^ alpha)⁻¹ by
    funext n
    exact zeta_renyi_power_pointwise s alpha hs n]
  rw [hbase.tsum_mul_right, tsum_real_weight_eq_partition_toReal _ halpha_s,
    partition_toReal_eq_zeta_re _ halpha_s, partition_toReal_eq_zeta_re s hs]
  rfl

/-- Closed form for the Renyi entropy of the zeta distribution. -/
theorem zeta_renyi_entropy_eq (s alpha : ℝ) (hs : 1 < s)
    (halpha_ne_one : alpha ≠ 1) (halpha_s : 1 < alpha * s) :
    countableRenyiEntropy alpha (zetaDist s hs) =
      (1 / (1 - alpha)) *
        Real.log ((riemannZeta ((alpha * s : ℝ) : ℂ)).re /
          (riemannZeta (s : ℂ)).re ^ alpha) := by
  by_cases h : alpha = 1
  · exact (halpha_ne_one h).elim
  rw [countableRenyiEntropy, zeta_renyi_power_sum s alpha hs halpha_s]

end


end D5.S3.Analytic.Zeta.ZetaRenyiEntropy
