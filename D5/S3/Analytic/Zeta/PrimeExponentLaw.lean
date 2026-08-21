/- GID: D5/S3/Analytic/Zeta/PrimeExponentLaw
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime exponents under the zeta distribution have geometric tails and masses. -/

import Mathlib
import D5.S3.Analytic.ZetaGibbs

/- Provenance: Native proof over pinned mathlib. -/

/- Search and proof receipt (2026-08-21).

   Generality tag and rule applied.
   * This file is tagged `I`. H10 reads `通用性头必填;标 G 者禁 import 实例事实`,
     and SL-010 enforces that a `G`-tagged file may not import an `I`-tagged
     fact. This file imports the `I`-tagged `ZetaGibbs.lean` and uses its
     particular `zetaDist`, so `G` is forbidden and `I` is forced.

   Generality tags of every repository import, listed individually.
   * `D5/S3/Analytic/ZetaGibbs.lean` — tagged `I`. This is the only repository
     import. `Mathlib` is external and carries no repository tag.

   Thinness assessment, per theorem.
   * `measure_dvd` is SUBSTANTIVE: it reindexes the subtype of multiples by an
     explicit equivalence, proves multiplicativity of `weight` including its
     zero slot, and separately cancels the finite nonzero partition function.
   * `measure_prime_pow_dvd` is THIN: it applies `measure_dvd` and performs the
     real-exponent algebra for a prime power.
   * `measure_factorization_ge` is SUBSTANTIVE: factorization at zero prevents
     a set equality, so the proof first proves the zero slot null and then uses
     an almost-everywhere divisibility/factorization equivalence.
   * `measure_factorization_eq` is NOT THIN: it realizes equality as a
     difference of two tails, proves the measurable finite-measure subtraction
     step, and computes the successor exponent.
   * `tsum_prime_exponent_masses` is NOT THIN: it explicitly converts real
     powers and `ofReal` operations before applying the ENNReal geometric
     series. `ENNReal.tsum_mul_left` performs only the final factor extraction;
     it does not supply the preceding PMF normalization, multiples equivalence,
     or zero-slot work. The previous worker's one-lemma warning is confirmed.

   Attribute audit of load-bearing declarations. Each attribute claim was
   checked by aligning the line immediately above the declaration in the
   pinned source; generated additive declarations include their source
   `to_additive` attribute.
   * The three private helpers and all five public theorems declared below
     carry no attributes; each declaration is preceded by a blank line or its
     docstring, never by an attribute line.
   * Repository declarations `weight`, `partitionFunction`,
     `partition_function_ne_zero`, `partition_function_ne_top`, and
     `zeta_dist_apply` (`ZetaGibbs.lean:19,31,51,41,59`) carry no attribute.
     `weight_zero` (`ZetaGibbs.lean:24`) CARRIES `@[simp]`.
   * `Equiv.tsum_eq` is generated from `Equiv.tprod_eq`
     (`Mathlib/Topology/Algebra/InfiniteSum/Basic.lean:561`) by the bare
     `@[to_additive]` on line 560; it inherits no `simp` attribute.
     `tsum_subtype` is likewise generated from `tprod_subtype` at line 589 by
     the bare `@[to_additive]` on line 588; it inherits no `simp` attribute.
   * `ENNReal.tsum_mul_left` and `ENNReal.tsum_mul_right`
     (`Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:179,188`) carry no
     attribute. `ENNReal.tsum_geometric`
     (`Mathlib/Analysis/SpecificLimits/Basic.lean:401`) CARRIES `@[simp]`.
   * `PMF.toMeasure_apply_singleton` and `PMF.toMeasure_apply_eq_tsum`
     (`Mathlib/Probability/ProbabilityMassFunction/Basic.lean:228,282`) carry
     no attribute.
   * `ENNReal.mul_inv_cancel` (`Mathlib/Data/ENNReal/Inv.lean:102`) carries no
     attribute. `ENNReal.sub_ne_top` (`Mathlib/Data/ENNReal/Operations.lean:298`)
     CARRIES `@[aesop (rule_sets := [finiteness]) unsafe 75% apply]`
     attribute, not `simp`.
   * `ENNReal.ofReal_mul`, `ENNReal.ofReal_pow`, `ENNReal.ofReal_lt_one`, and
     `ENNReal.ofReal_one` (`Mathlib/Data/ENNReal/Real.lean:297,306,203` and
     `Mathlib/Data/ENNReal/Basic.lean:291`) CARRY `@[simp]`;
     `ENNReal.ofReal_sub` (`Mathlib/Data/ENNReal/Operations.lean:436`) carries
     no attribute.
   * `Real.rpow_natCast` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:62`)
     CARRIES `@[simp, norm_cast]`. `Real.rpow_add`, `Real.rpow_mul`,
     `Real.mul_rpow`, and `Real.rpow_lt_one_of_one_lt_of_neg` (lines
     207, 412, 476, and 662) carry no attribute.
     `Real.rpow_nonneg` (line 163) CARRIES `@[bound]`.
   * `ae_iff` and `measure_congr`
     (`Mathlib/MeasureTheory/OuterMeasure/AE.lean:78,270`), `measure_sdiff`
     (`Mathlib/MeasureTheory/Measure/MeasureSpace.lean:250`), and
     `Nat.Prime.pow_dvd_iff_le_factorization`
     (`Mathlib/Data/Nat/Factorization/Basic.lean:164`) carry no attribute.
     `measure_ne_top` (`Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean:55`)
     CARRIES `@[simp, aesop (rule_sets := [finiteness]) safe apply]`.
   * `tsub_pos_of_lt` (`Mathlib/Algebra/Order/Sub/Basic.lean:57`) carries no
     attribute. Its pinned signature is `a < b → 0 < b - a`; this is the
     declaration used to repair the final nonzero proof.
   * `Nat.div_mul_cancel` (`Init/Data/Nat/Dvd.lean:110`) and
     `Nat.mul_div_cancel_left` (`Init/Data/Nat/Div/Basic.lean:423`) are both
     `protected theorem` declarations preceded by a blank line and carry no
     attribute. These two live in the pinned Lean core tree
     (`~/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/`), not in
     Mathlib; the first pass searched only the Mathlib tree and recorded them
     as unresolved. An adversarial review located them, and the coordinates
     and attribute status above were then confirmed line by line against the
     pinned core source by the coordinator.

   Automation probe. After all five statements elaborated, a run-local scratch
   file independently attempted `decide`, `simp`, `omega`, and `norm_num` on
   each statement. NONE closed any statement. `decide` reported that its
   expected type contained free variables; `simp` and `norm_num` left the
   measure or series equality unsolved; `omega` reported no usable arithmetic
   route. These are failures to close, not name-resolution errors.
   * Single-lemma probes on `measure_dvd`: `simp
     [PMF.toMeasure_apply_eq_tsum]`, `simp [zeta_dist_apply]`, and `simp
     [ENNReal.mul_inv_cancel]` all failed.
   * On `measure_prime_pow_dvd`: `simp [measure_dvd]` and `simp
     [Real.rpow_mul]` both failed.
   * On `measure_factorization_ge`: `simp [PMF.toMeasure_apply_singleton]`,
     `simp [Nat.Prime.pow_dvd_iff_le_factorization]`, and `simp
     [measure_prime_pow_dvd]` all failed.
   * On `measure_factorization_eq`: `simp [measure_factorization_ge]`, `simp
     [measure_sdiff]`, and `simp [Real.rpow_add]` all failed.
   * On `tsum_prime_exponent_masses`: `simp [ENNReal.tsum_mul_left]`, `simp
     [ENNReal.tsum_geometric]`, `simp [ENNReal.ofReal_mul]`, and `simp
     [tsub_pos_of_lt]` all failed. Several cited declarations carry `@[simp]`;
     measured closability by plain `simp` is nevertheless false. Every cited
     name resolved. The scratch file was deleted and is not part of this unit.

   Candidates inspected. This list is separate from the declarations doing
   real work and is not claimed exhaustive.
   * Repository-wide D5 searches for `zetaDist`, `zeta_dist`, factorization,
     geometric laws, and prime exponents located `ZetaGibbs.lean` as the sole
     source of this distribution and no prior single-prime law. Recursive hits
     in subdirectories were inspected: `Analytic/EulerGerm/
     GermProductNonvanishing.lean` concerns a geometric analytic majorant, and
     `Analytic/Displacement/GoldenDisplacementSurfaceRegion.lean` concerns a
     fixed golden displacement spectrum; neither supplies this probability
     law. `Analytic/DiagonalCollapse.lean` also mentions factorization but not
     a zeta-distribution marginal.
   * In pinned mathlib, `Mathlib/Data/Nat/Factorization/Basic.lean`,
     `Mathlib/Probability/ProbabilityMassFunction/Basic.lean`,
     `Mathlib/Probability/Distributions/Geometric.lean`,
     `Mathlib/Probability/Independence/Basic.lean`, the ENNReal files, the
     infinite-sum files, and `Mathlib/Algebra/Order/Sub/` were searched and the
     relevant declarations above inspected. The geometric-distribution file
     supplies a generic geometric measure, not the zeta marginal or the
     divisibility computation needed to identify it.
   * Third-party source search used GitHub queries for Lean declarations
     combining zeta distributions, `Nat.factorization`, and geometric prime
     exponents. Results exposed mathlib's generic geometric-series and
     geometric-measure material but no exact theorem or usable package
     supplying this result.

   Declarations doing real work in the proof bodies.
   * `multiplesEquiv`, `weight_mul`, and `weight_multiples` perform the explicit
     reindexing and scaling of all multiples; `Equiv.tsum_eq`,
     `ENNReal.tsum_mul_left`, and the two partition-function nonvanishing/
     finiteness theorems then normalize `measure_dvd`.
   * `measure_dvd`, `Real.rpow_natCast`, and `Real.rpow_mul` identify the
     prime-power tail.
   * `PMF.toMeasure_apply_singleton`, `weight_zero`, `ae_iff`, `measure_congr`,
     and `Nat.Prime.pow_dvd_iff_le_factorization` remove the exceptional zero
     slot and transfer divisibility to factorization.
   * `measure_sdiff`, `measure_factorization_ge`, `ENNReal.ofReal_sub`, and
     `Real.rpow_add` turn adjacent tails into the point mass.
   * `Real.rpow_lt_one_of_one_lt_of_neg`, the `ofReal` conversion lemmas,
     `ENNReal.tsum_geometric`, `ENNReal.mul_inv_cancel`, `tsub_pos_of_lt`, and
     `ENNReal.sub_ne_top` normalize the displayed masses. Arithmetic tactics
     `ring`, `linarith`, `omega`, `positivity`, `push_cast`, and
     `exact_mod_cast` carry only the displayed bookkeeping.

   Provenance of supplied findings and independent verification.
   * SUPPLIED BY THE DISPATCHER: under pinned `Mathlib/` there is no
     `zetaDist`, `zeta_dist`, or `ZetaDistribution`, and under
     `Mathlib/Probability/` there is no `Nat.factorization`; present are
     `Mathlib/Probability/Distributions/Geometric.lean` and, in
     `Mathlib/Probability/Independence/Basic.lean`, `iIndepFun` (line 136),
     `iIndepFun_iff_measure_inter_preimage_eq_mul` (654), and
     `iIndepFun_iff_map_fun_eq_pi_map` (861). This is recorded as supplied,
     not claimed as an independently originated audit.
   * Independently verified here with exact recursive `rg` searches over the
     pinned trees: all three zeta-name searches returned zero Mathlib hits;
     the `Nat.factorization` search returned zero Probability hits; the
     geometric file exists; and the three independence declarations occur at
     exactly lines 136, 654, and 861. The repository and third-party searches
     described above additionally found no reusable exact result.

   Residual and address provenance.
   * This unit follows F1, `ZetaGibbs.lean`, and delivers only the single-prime
     geometric law from the residual row `F2 | 素指数独立性:zeta 分布下 v_p
     独立几何` and the residual atom `Euler 积 = 独立性`. The independence half
     of F2 remains open; no independence statement is attempted here.
   * Remeasurement found exactly twelve direct `.lean` files in
     `D5/S3/Analytic`, so a thirteenth direct file would violate the split
     threshold. `Zeta/` is a subdirectory and needs no registration.
     `Meta/domains.yaml` registers only the top-level `Analytic` and
     `AnalyticClosure` domains; none of the measured subdirectories `Dilation`,
     `Displacement`, `EulerGerm`, `Isolation`, or `Zeta` occurs in either
     `Meta/domains.yaml` or `Meta/registry.yaml`. -/

namespace D5.S3.Analytic.Zeta.PrimeExponentLaw

open scoped ENNReal
open MeasureTheory
open D5.S3.Analytic.ZetaGibbs

noncomputable section

private def multiplesEquiv (a : ℕ) (ha : a ≠ 0) : ℕ ≃ {n : ℕ // a ∣ n} where
  toFun m := ⟨a * m, dvd_mul_right a m⟩
  invFun n := n.1 / a
  left_inv m := Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero ha)
  right_inv n := by
    apply Subtype.ext
    simpa [Nat.mul_comm] using Nat.div_mul_cancel n.2

private theorem weight_mul (s : ℝ) (hs : 0 < s) (a m : ℕ) (ha : a ≠ 0) :
    weight s (a * m) = weight s a * weight s m := by
  by_cases hm : m = 0
  · subst m
    simp [weight_zero s hs]
  · have haR : 0 ≤ (a : ℝ) := by positivity
    have hmR : 0 ≤ (m : ℝ) := by positivity
    rw [weight, weight, weight, Nat.cast_mul, Real.mul_rpow haR hmR]
    exact ENNReal.ofReal_mul (Real.rpow_nonneg haR (-s))

private theorem weight_multiples (s : ℝ) (hs : 0 < s) (a : ℕ) (ha : a ≠ 0) :
    ∑' n : {n : ℕ // a ∣ n}, weight s n = weight s a * partitionFunction s := by
  rw [← (multiplesEquiv a ha).tsum_eq]
  change (∑' m : ℕ, weight s (a * m)) = _
  simp_rw [weight_mul s hs a _ ha]
  exact ENNReal.tsum_mul_left

/-- The zeta probability of divisibility by `a` is its unnormalized zeta weight. -/
theorem measure_dvd (s : ℝ) (hs : 1 < s) (a : ℕ) (ha : a ≠ 0) :
    (zetaDist s hs).toMeasure {n : ℕ | a ∣ n} = weight s a := by
  rw [PMF.toMeasure_apply_eq_tsum, ← tsum_subtype]
  simp_rw [zeta_dist_apply]
  rw [ENNReal.tsum_mul_right]
  change (∑' n : {n : ℕ // a ∣ n}, weight s n) * _ = _
  rw [weight_multiples s (by linarith) a ha]
  rw [partitionFunction, mul_assoc]
  have hcancel : (∑' n : ℕ, weight s n) * (∑' n : ℕ, weight s n)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simpa [partitionFunction] using partition_function_ne_zero s)
      (by simpa [partitionFunction] using partition_function_ne_top s hs)
  rw [hcancel, mul_one]

/-- Divisibility by a prime power has the expected power-law probability. -/
theorem measure_prime_pow_dvd (s : ℝ) (hs : 1 < s) (p k : ℕ) (hp : p.Prime) :
    (zetaDist s hs).toMeasure {n : ℕ | p ^ k ∣ n} =
      ENNReal.ofReal ((p : ℝ) ^ (-(k : ℝ) * s)) := by
  rw [measure_dvd s hs (p ^ k) (pow_ne_zero _ hp.ne_zero), weight]
  congr 1
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- The tail of a prime exponent is the corresponding prime-power divisibility probability. -/
theorem measure_factorization_ge (s : ℝ) (hs : 1 < s) (p k : ℕ) (hp : p.Prime) :
    (zetaDist s hs).toMeasure {n : ℕ | k ≤ n.factorization p} =
      ENNReal.ofReal ((p : ℝ) ^ (-(k : ℝ) * s)) := by
  let μ := (zetaDist s hs).toMeasure
  have hz : μ ({0} : Set ℕ) = 0 := by
    rw [(zetaDist s hs).toMeasure_apply_singleton 0 MeasurableSet.of_discrete]
    simp [zeta_dist_apply, weight_zero s (by linarith)]
  have hne : ∀ᵐ n ∂μ, n ≠ 0 := by
    rw [ae_iff]
    simpa using hz
  calc
    μ {n : ℕ | k ≤ n.factorization p} = μ {n : ℕ | p ^ k ∣ n} := by
      apply measure_congr
      filter_upwards [hne] with n hn
      exact propext (hp.pow_dvd_iff_le_factorization hn).symm
    _ = ENNReal.ofReal ((p : ℝ) ^ (-(k : ℝ) * s)) :=
      measure_prime_pow_dvd s hs p k hp

/-- Each prime exponent has the geometric mass function with ratio `p ^ (-s)`. -/
theorem measure_factorization_eq (s : ℝ) (hs : 1 < s) (p k : ℕ) (hp : p.Prime) :
    (zetaDist s hs).toMeasure {n : ℕ | n.factorization p = k} =
      ENNReal.ofReal
        ((1 - (p : ℝ) ^ (-s)) * (p : ℝ) ^ (-(k : ℝ) * s)) := by
  let μ := (zetaDist s hs).toMeasure
  have hset : {n : ℕ | n.factorization p = k} =
      {n : ℕ | k ≤ n.factorization p} \ {n : ℕ | k + 1 ≤ n.factorization p} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    omega
  rw [hset, measure_sdiff (by intro n hn; exact Nat.le_of_succ_le hn)
    MeasurableSet.of_discrete.nullMeasurableSet
    (measure_ne_top μ _)]
  rw [measure_factorization_ge s hs p k hp, measure_factorization_ge s hs p (k + 1) hp]
  rw [← ENNReal.ofReal_sub _ (Real.rpow_nonneg (by positivity) _)]
  congr 1
  have hstep : (p : ℝ) ^ (-((k + 1 : ℕ) : ℝ) * s) =
      (p : ℝ) ^ (-(k : ℝ) * s) * (p : ℝ) ^ (-s) := by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    rw [show -((k + 1 : ℕ) : ℝ) * s = -(k : ℝ) * s + -s by push_cast; ring,
      Real.rpow_add hpR]
  rw [hstep]
  ring

/-- The displayed geometric masses are normalized. -/
theorem tsum_prime_exponent_masses (s : ℝ) (hs : 1 < s) (p : ℕ) (hp : p.Prime) :
    ∑' k : ℕ, ENNReal.ofReal
      ((1 - (p : ℝ) ^ (-s)) * (p : ℝ) ^ (-(k : ℝ) * s)) = 1 := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hq0 : 0 ≤ (p : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  have hq1 : (p : ℝ) ^ (-s) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  simp_rw [show ∀ k : ℕ, (p : ℝ) ^ (-(k : ℝ) * s) = ((p : ℝ) ^ (-s)) ^ k by
    intro k
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    ring]
  simp_rw [ENNReal.ofReal_mul (sub_nonneg.mpr hq1.le), ENNReal.ofReal_sub 1 hq0,
    ENNReal.ofReal_one, ENNReal.ofReal_pow hq0]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_inv_cancel
    (tsub_pos_of_lt (ENNReal.ofReal_lt_one.mpr hq1)).ne' (ENNReal.sub_ne_top ENNReal.one_ne_top)

end

end D5.S3.Analytic.Zeta.PrimeExponentLaw
