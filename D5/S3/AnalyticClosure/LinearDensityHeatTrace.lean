/- GID: D5/S3/AnalyticClosure/LinearDensityHeatTrace
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/LinearDensityHeatTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear spectral density gives a bounded heat-trace remainder. -/

import Mathlib

open Filter Set
open scoped Topology Nat

namespace D5.S3.AnalyticClosure.LinearDensityHeatTrace

private lemma geometric_heat
    {c t : ℝ} (hc : 0 < c) (ht : 0 < t) (htc : t ≤ c) :
    Summable (fun n : ℕ => Real.exp (-t * (n + 1) / c)) ∧
      (∑' n : ℕ, Real.exp (-t * (n + 1) / c)) ≤ c / t ∧
      |(∑' n : ℕ, Real.exp (-t * (n + 1) / c)) - c / t| ≤ 1 := by
  let a : ℝ := t / c
  let q : ℝ := Real.exp (-a)
  have ha : 0 < a := div_pos ht hc
  have ha1 : a ≤ 1 := (div_le_one hc).2 htc
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hterm : (fun n : ℕ => Real.exp (-t * (n + 1) / c)) =
      fun n : ℕ => q ^ (n + 1) := by
    funext n
    rw [show -t * (n + 1) / c = (-a) * (n + 1) by
      dsimp [a]
      ring]
    simpa [q, mul_comm] using (Real.exp_nat_mul (-a) (n + 1))
  have hsumq : Summable (fun n : ℕ => q ^ (n + 1)) := by
    simpa [pow_succ] using
      (summable_geometric_of_lt_one hq0 hq1).mul_right q
  have hsum : Summable (fun n : ℕ => Real.exp (-t * (n + 1) / c)) := by
    rw [hterm]
    exact hsumq
  have hsum_eq : (∑' n : ℕ, Real.exp (-t * (n + 1) / c)) =
      1 / (Real.exp a - 1) := by
    rw [hterm]
    calc
      (∑' n : ℕ, q ^ (n + 1)) = q * (∑' n : ℕ, q ^ n) := by
        simp_rw [pow_succ]
        rw [tsum_mul_right, mul_comm]
      _ = q * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq0 hq1]
      _ = 1 / (Real.exp a - 1) := by
        rw [show q = (Real.exp a)⁻¹ by simp [q, Real.exp_neg]]
        field_simp [Real.exp_ne_zero]
  have hden : 0 < Real.exp a - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr ha)
  have hlinear : a ≤ Real.exp a - 1 := by
    linarith [Real.add_one_le_exp a]
  have hsum_le_a : 1 / (Real.exp a - 1) ≤ 1 / a := by
    exact one_div_le_one_div_of_le ha hlinear
  have hca : c / t = 1 / a := by
    dsimp [a]
    field_simp [hc.ne', ht.ne']
  have hupper : (∑' n : ℕ, Real.exp (-t * (n + 1) / c)) ≤ c / t := by
    rw [hsum_eq, hca]
    exact hsum_le_a
  have habsA : |a| ≤ 1 := by simpa [abs_of_pos ha] using ha1
  have hremainder : |Real.exp a - 1 - a| ≤ a ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le habsA
  have herror : |1 / (Real.exp a - 1) - 1 / a| ≤ 1 := by
    rw [show 1 / (Real.exp a - 1) - 1 / a =
      (a - (Real.exp a - 1)) / (a * (Real.exp a - 1)) by
        field_simp [ha.ne', hden.ne']]
    rw [abs_div, abs_mul, abs_of_pos ha, abs_of_pos hden]
    have hnum : |a - (Real.exp a - 1)| ≤ a ^ 2 := by
      simpa [abs_sub_comm] using hremainder
    have hdenLower : a ^ 2 ≤ a * (Real.exp a - 1) := by
      nlinarith
    rw [div_le_one (mul_pos ha hden)]
    exact hnum.trans hdenLower
  refine ⟨hsum, hupper, ?_⟩
  rw [hsum_eq, hca]
  exact herror

set_option maxHeartbeats 1200000 in
-- The explicit finite-head and infinite-tail estimates need a larger elaboration budget.
/-- Linear counting density gives a reciprocal-time heat trace with bounded remainder. -/
theorem linear_density_heat_trace
    (spectrum : ℕ → ℝ) (c : ℝ)
    (spectrumPositive : ∀ n, 0 < spectrum n)
    (spectrumStrict : StrictMono spectrum)
    (spectrumUnbounded : Tendsto spectrum atTop atTop)
    (densityPositive : 0 < c)
    (countingDensity : ∃ C U : ℝ, 0 ≤ C ∧
      ∀ u, U ≤ u →
        |(({n : ℕ | spectrum n ≤ u}.ncard : ℕ) : ℝ) - c * u| ≤ C) :
    ∃ B δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t ≤ δ →
      Summable (fun n : ℕ => Real.exp (-t * spectrum n)) ∧
      |(∑' n : ℕ, Real.exp (-t * spectrum n)) - c / t| ≤ B := by
  rcases countingDensity with ⟨C, U, hC, countingDensity⟩
  have countAtSpectrum : ∀ n : ℕ,
      (({m : ℕ | spectrum m ≤ spectrum n}.ncard : ℕ) : ℝ) = n + 1 := by
    intro n
    have hset : {m : ℕ | spectrum m ≤ spectrum n} = Set.Iic n := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_Iic, spectrumStrict.le_iff_le]
    rw [hset, Set.ncard_Iic_nat]
    norm_cast
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n, N ≤ n → U ≤ spectrum n := by
    rcases (eventually_atTop.1 (spectrumUnbounded.eventually (eventually_ge_atTop U))) with
      ⟨N, hN⟩
    exact ⟨N, hN⟩
  have displacement : ∀ n, N ≤ n →
      |spectrum n - (n + 1) / c| ≤ C / c := by
    intro n hn
    have hcount := countingDensity (spectrum n) (hN n hn)
    rw [countAtSpectrum n] at hcount
    rw [show spectrum n - (n + 1) / c =
      (c * spectrum n - (n + 1)) / c by
        field_simp [densityPositive.ne']]
    rw [abs_div, abs_of_pos densityPositive]
    have hsymmetric : |c * spectrum n - (n + 1)| ≤ C := by
      simpa [abs_sub_comm] using hcount
    exact div_le_div_of_nonneg_right hsymmetric densityPositive.le
  let δ : ℝ := min c (c / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < δ := lt_min densityPositive (div_pos densityPositive hC1)
  refine ⟨2 * N + 2 * C + 1, δ, hδ, ?_⟩
  intro t ht htδ
  have htc : t ≤ c := htδ.trans (min_le_left _ _)
  have htdensity : t * (C / c) ≤ 1 := by
    have htbound : t ≤ c / (C + 1) := htδ.trans (min_le_right _ _)
    have hmul : t * (C + 1) ≤ c := (le_div_iff₀ hC1).mp htbound
    have htcC : t * C ≤ c := by nlinarith
    calc
      t * (C / c) = t * C / c := by ring
      _ ≤ 1 := (div_le_one densityPositive).2 htcC
  let lattice : ℕ → ℝ := fun n => Real.exp (-t * (n + 1) / c)
  let heat : ℕ → ℝ := fun n => Real.exp (-t * spectrum n)
  have latticeFacts := geometric_heat densityPositive ht htc
  have latticeSummable : Summable lattice := by simpa [lattice] using latticeFacts.1
  have latticeUpper : (∑' n, lattice n) ≤ c / t := by
    simpa [lattice] using latticeFacts.2.1
  have latticeError : |(∑' n, lattice n) - c / t| ≤ 1 := by
    simpa [lattice] using latticeFacts.2.2
  have pointwiseDifference : ∀ n, N ≤ n →
      |heat n - lattice n| ≤ lattice n * (2 * t * (C / c)) := by
    intro n hn
    have hdisp := displacement n hn
    have hsmall : |-(t * (spectrum n - (n + 1) / c))| ≤ 1 := by
      rw [abs_neg, abs_mul, abs_of_pos ht]
      exact (mul_le_mul_of_nonneg_left hdisp ht.le).trans htdensity
    have hexpSplit : heat n = lattice n *
        Real.exp (-(t * (spectrum n - (n + 1) / c))) := by
      dsimp [heat, lattice]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexpSplit]
    calc
      |lattice n * Real.exp (-(t * (spectrum n - (n + 1) / c))) - lattice n| =
          lattice n * |Real.exp (-(t * (spectrum n - (n + 1) / c))) - 1| := by
        rw [show lattice n * Real.exp (-(t * (spectrum n - (n + 1) / c))) - lattice n =
          lattice n * (Real.exp (-(t * (spectrum n - (n + 1) / c))) - 1) by ring,
          abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ lattice n * (2 * |-(t * (spectrum n - (n + 1) / c))|) := by
        gcongr
        exact Real.abs_exp_sub_one_le hsmall
      _ ≤ lattice n * (2 * t * (C / c)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        rw [abs_neg, abs_mul, abs_of_pos ht]
        nlinarith
  have latticeTailSummable : Summable (fun k => lattice (k + N)) :=
    latticeSummable.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have differenceNormSummable : Summable (fun k => |heat (k + N) - lattice (k + N)|) := by
    apply Summable.of_norm_bounded_eventually
      (latticeTailSummable.mul_right (2 * t * (C / c)))
    filter_upwards [] with k
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    simpa [Nat.add_comm, mul_assoc, mul_left_comm, mul_comm] using
      pointwiseDifference (k + N) (Nat.le_add_left N k)
  have differenceSummable : Summable (fun k => heat (k + N) - lattice (k + N)) :=
    differenceNormSummable.of_norm
  have heatTailSummable : Summable (fun k => heat (k + N)) := by
    simpa only [sub_add_cancel] using differenceSummable.add latticeTailSummable
  have heatSummable : Summable heat := (summable_nat_add_iff N).mp heatTailSummable
  let tailMajor : ℕ → ℝ := fun k =>
    lattice (k + N) * (2 * t * (C / c))
  have tailMajorSummable : Summable tailMajor := by
    dsimp [tailMajor]
    exact latticeTailSummable.mul_right _
  have tailPointwise : ∀ k, |heat (k + N) - lattice (k + N)| ≤ tailMajor k := by
    intro k
    exact pointwiseDifference (k + N) (Nat.le_add_left N k)
  have tailTsumComparison :
      (∑' k, |heat (k + N) - lattice (k + N)|) ≤ ∑' k, tailMajor k :=
    Summable.tsum_le_tsum tailPointwise differenceNormSummable tailMajorSummable
  have differenceRealNormSummable :
      Summable (fun k => ‖heat (k + N) - lattice (k + N)‖) := by
    simpa only [Real.norm_eq_abs] using differenceNormSummable
  have tailAbsoluteSumBound :
      |(∑' k, (heat (k + N) - lattice (k + N)))| ≤
        ∑' k, |heat (k + N) - lattice (k + N)| := by
    simpa only [Real.norm_eq_abs] using
      (norm_tsum_le_tsum_norm differenceRealNormSummable)
  have tailBound : |(∑' k, (heat (k + N) - lattice (k + N)))| ≤ 2 * C := by
    calc
      |(∑' k, (heat (k + N) - lattice (k + N)))| ≤
          ∑' k, |heat (k + N) - lattice (k + N)| := tailAbsoluteSumBound
      _ ≤ ∑' k, tailMajor k := tailTsumComparison
      _ = ∑' k, lattice (k + N) * (2 * t * (C / c)) := by rfl
      _ ≤ (∑' k, lattice k) * (2 * t * (C / c)) := by
        rw [tsum_mul_right]
        have hsplit := latticeSummable.sum_add_tsum_nat_add N
        have hfinite : 0 ≤ ∑ n ∈ Finset.range N, lattice n := by
          exact Finset.sum_nonneg fun _ _ => Real.exp_nonneg _
        have htailLe : (∑' k, lattice (k + N)) ≤ ∑' k, lattice k := by
          linarith
        exact mul_le_mul_of_nonneg_right htailLe (by positivity)
      _ ≤ (c / t) * (2 * t * (C / c)) := by
        gcongr
      _ = 2 * C := by field_simp [densityPositive.ne', ht.ne']
  have finiteBound :
      |(∑ n ∈ Finset.range N, heat n) - ∑ n ∈ Finset.range N, lattice n| ≤ 2 * N := by
    calc
      |(∑ n ∈ Finset.range N, heat n) - ∑ n ∈ Finset.range N, lattice n| =
          |∑ n ∈ Finset.range N, (heat n - lattice n)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ n ∈ Finset.range N, |heat n - lattice n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.range N, (2 : ℝ) := by
        gcongr with n hn
        have hheat : 0 < heat n := Real.exp_pos _
        have hheatOne : heat n ≤ 1 := by
          dsimp [heat]
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le)
            (spectrumPositive n).le
        have hlattice : 0 < lattice n := Real.exp_pos _
        have hlatticeOne : lattice n ≤ 1 := by
          dsimp [lattice]
          rw [Real.exp_le_one_iff]
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (by positivity))
            densityPositive.le
        rw [abs_le]
        constructor <;> linarith
      _ = 2 * N := by simp; ring
  have decomposition :
      (∑' n, heat n) - c / t =
        ((∑ n ∈ Finset.range N, heat n) -
          ∑ n ∈ Finset.range N, lattice n) +
        (∑' k, (heat (k + N) - lattice (k + N))) +
        ((∑' n, lattice n) - c / t) := by
    have hheatSplit := heatSummable.sum_add_tsum_nat_add N
    have hlatticeSplit := latticeSummable.sum_add_tsum_nat_add N
    have htailSub : (∑' k, (heat (k + N) - lattice (k + N))) =
        (∑' k, heat (k + N)) - (∑' k, lattice (k + N)) :=
      (heatTailSummable.hasSum.sub latticeTailSummable.hasSum).tsum_eq
    rw [← hheatSplit, ← hlatticeSplit, htailSub]
    ring
  refine ⟨by simpa [heat] using heatSummable, ?_⟩
  rw [show (∑' n : ℕ, Real.exp (-t * spectrum n)) = ∑' n, heat n by rfl,
      decomposition]
  calc
    |((∑ n ∈ Finset.range N, heat n) - ∑ n ∈ Finset.range N, lattice n) +
        (∑' k, (heat (k + N) - lattice (k + N))) +
        ((∑' n, lattice n) - c / t)| ≤
        |(∑ n ∈ Finset.range N, heat n) - ∑ n ∈ Finset.range N, lattice n| +
        |(∑' k, (heat (k + N) - lattice (k + N)))| +
        |(∑' n, lattice n) - c / t| := by
      let A := (∑ n ∈ Finset.range N, heat n) -
        ∑ n ∈ Finset.range N, lattice n
      let D := ∑' k, (heat (k + N) - lattice (k + N))
      let G := (∑' n, lattice n) - c / t
      have houter : ‖(A + D) + G‖ ≤ ‖A + D‖ + ‖G‖ := norm_add_le _ _
      have hinner : ‖A + D‖ ≤ ‖A‖ + ‖D‖ := norm_add_le _ _
      dsimp [A, D, G] at houter hinner ⊢
      simpa only [Real.norm_eq_abs] using houter.trans (by nlinarith [hinner])
    _ ≤ 2 * N + 2 * C + 1 := by gcongr

#print axioms linear_density_heat_trace

end D5.S3.AnalyticClosure.LinearDensityHeatTrace
