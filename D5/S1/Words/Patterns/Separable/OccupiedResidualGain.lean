/- GID: D5/S1/Words/Patterns/Separable/OccupiedResidualGain
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedResidualGain
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.SpecificFunctions.Basic]
   utility: none
   digest: The full logarithmic profile has a uniform positive linear gain on both tails. -/

import D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries
import D5.S1.Words.Patterns.Separable.OccupiedTruncatedMixture
import D5.S1.Words.Patterns.Separable.OccupiedKernelCoefficient
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SumIntegralComparisons

/-! The residual of the finite exponent mixture has convex local terms and
a controlled crossing-jump cost. This cost is absorbed by the mixture gain. -/

open Set MeasureTheory Filter
open scoped BigOperators Topology

namespace D5.S1.Words.Patterns.Separable.OccupiedResidualGain

open D5.S0.Asymptotics.WeightedProbability.AbsoluteDiscrepancySeries (discrepancyProfile)
open OccupiedComparison OccupiedKernelCoefficient
open OccupiedActualPowerGenerator OccupiedTruncatedMixture

private noncomputable def residualBase (t : ℝ) : ℝ :=
  t ^ (-(3 / 4 : ℝ)) / Real.log t

private noncomputable def residualProfile (z : ℤ) : ℝ := residualBase (2+|(z : ℝ)|)

private theorem resConvex : ConvexOn ℝ (Ici (2 : ℝ)) residualBase := by
  let S := Ici (2 : ℝ)
  have hS : S ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hx
  have hlog : ConcaveOn ℝ S Real.log :=
    (strictConcaveOn_log_Ioi.concaveOn).subset hS (convex_Ici _)
  have hImg : Real.log '' S ⊆ Ioi (0 : ℝ) := by
    rintro y ⟨x,hx,rfl⟩
    apply Real.log_pos
    exact lt_of_lt_of_le (by norm_num) hx
  have hm : MonotoneOn Real.log (Real.log '' S) :=
    Real.strictMonoOn_log.monotoneOn.mono hImg
  have hOuter : ConcaveOn ℝ (Real.log '' S) Real.log :=
    (strictConcaveOn_log_Ioi.concaveOn).subset hImg
      (hlog.1.isPreconnected.image Real.log
        (fun x hx => (Real.continuousAt_log (ne_of_gt (hS hx))).continuousWithinAt)).convex
  have hloglog : ConcaveOn ℝ S (Real.log ∘ Real.log) := hOuter.comp hlog hm
  let q (x : ℝ) := -(3 / 4 : ℝ) * Real.log x - Real.log (Real.log x)
  have hq : ConvexOn ℝ S q := by
    convert (hlog.neg.smul (by norm_num : (0 : ℝ) ≤ 3 / 4)).add hloglog.neg using 1
    funext x
    simp only [q, Pi.add_apply, Pi.neg_apply, smul_eq_mul, Function.comp_apply]
    ring
  have hExp : ConvexOn ℝ (q '' S) Real.exp :=
    (convexOn_exp).subset (subset_univ _) (by
      -- The image is an interval because q is continuous on S.
      have hc : ContinuousOn q S := by
        intro x hx
        apply ContinuousAt.continuousWithinAt
        have hl := Real.continuousAt_log (ne_of_gt (hS hx))
        have hl2 : ContinuousAt (fun x : ℝ => Real.log (Real.log x)) x :=
          (Real.continuousAt_log (Real.log_pos (lt_of_lt_of_le (by norm_num) hx)).ne').comp hl
        exact (continuousAt_const.mul hl).sub hl2
      exact ((convex_Ici (2 : ℝ)).isPreconnected.image q hc).convex)
  refine (hExp.comp hq (Real.exp_monotone.monotoneOn _)).congr ?_
  intro x hx
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hxp := zero_lt_one.trans hx1
  have hlogp := Real.log_pos hx1
  simp only [Function.comp_apply, q, residualBase, Real.exp_sub,
    Real.exp_log hlogp, Real.rpow_def_of_pos hxp]
  rw [mul_comm]

private theorem kernel_nonneg (i : ℕ) : 0 ≤ kernelWeight i := by
  unfold kernelWeight shapeWeight rho
  positivity

private theorem residual_nonneg (z : ℤ) : 0 ≤ residualProfile z := by
  have hx : 1 < 2+|(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  exact div_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _) (Real.log_pos hx).le

private theorem residual_le (z : ℤ) : residualProfile z ≤ 1 / Real.log 2 := by
  have hx : 2 ≤ 2+|(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < Real.log (2+|(z : ℝ)|) := Real.log_pos (lt_of_lt_of_le (by norm_num) hx)
  unfold residualProfile residualBase
  calc
    _ ≤ 1 / Real.log (2+|(z : ℝ)|) :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)) hp.le
    _ ≤ _ := one_div_le_one_div_of_le hln (Real.log_le_log (by norm_num) hx)

private theorem residual_second_local (n m : ℕ) (hm : m ≤ n) :
    0 ≤ residualProfile ((n : ℤ) + (m : ℤ)) + residualProfile ((n : ℤ) - (m : ℤ)) -
      2 * residualProfile (n : ℤ) := by
  let x := 2 + ((n : ℝ) + (m : ℝ))
  let y := 2 + ((n : ℝ) - (m : ℝ))
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hm
  have hx : x ∈ Ici (2 : ℝ) := by
    change (2 : ℝ) ≤ 2 + ((n : ℝ) + (m : ℝ))
    exact le_add_of_nonneg_right (by positivity)
  have hy : y ∈ Ici (2 : ℝ) := by
    change (2 : ℝ) ≤ 2 + ((n : ℝ) - (m : ℝ))
    exact le_add_of_nonneg_right (sub_nonneg.mpr hmn)
  have h := resConvex.2 hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hxy : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = 2 + (n : ℝ) := by
    simp only [smul_eq_mul, x, y]
    ring
  rw [hxy, smul_eq_mul, smul_eq_mul] at h
  unfold residualProfile
  push_cast
  rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + (m : ℝ)),
    abs_of_nonneg (sub_nonneg.mpr hmn), abs_of_nonneg (by positivity : 0 ≤ (n : ℝ))]
  linarith only [h]

private theorem kernel_tail_weight :
    ∃ B > (0 : ℝ), ∀ n : ℕ, 0 < n →
      (∑' i : ℕ, kernelWeight (n + i)) ≤ 2 * B / Real.sqrt (n : ℝ) := by
  obtain ⟨A,hA,h⟩ := actual_kernel_weight_strict_remainder
  let B := A + 21 / 16
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B,hB,?_⟩
  intro n hn
  have hW (j : ℕ) (hj : 0 < j) :
      kernelWeight j ≤ B * (1 / (((j + 1 : ℕ) : ℝ) * Real.sqrt ((j + 1 : ℕ) : ℝ))) := by
    have hA' := (abs_le.mp (h (j + 1) (by omega))).2
    rw [Nat.add_sub_cancel] at hA'
    let m := ((j + 1 : ℕ) : ℝ)
    have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast (show 1 ≤ j + 1 by omega)
    have hs : 0 < Real.sqrt m := by positivity
    have hd : m * Real.sqrt m ≤ m ^ 2 * Real.sqrt m := by
      gcongr
      nlinarith only [hm, sq_nonneg (m - 1)]
    have hc := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 21 / 16)
      (by positivity : 0 < m * Real.sqrt m) hd
    have hr : kernelWeight j ≤ A / (m * Real.sqrt m) + (21 / 16) / (m ^ 2 * Real.sqrt m) := by
      change kernelWeight j - A / (m * Real.sqrt m) ≤ _ at hA'
      linarith only [hA']
    exact (hr.trans (add_le_add le_rfl hc)).trans_eq (by dsimp only [B]; ring)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  let f (x : ℝ) := x ^ (-(3 / 2 : ℝ))
  have hanti : AntitoneOn f (Ici (n : ℝ)) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (hn0.trans_le hx) hxy (by norm_num)
  have hf : IntegrableOn f (Ioi (n : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hn0
  have hfn : ∀ x ∈ Ioi (n : ℝ), 0 ≤ f x :=
    fun x hx => Real.rpow_nonneg (hn0.trans (mem_Ioi.mp hx)).le _
  have hw : Summable fun i : ℕ => f (↑(i + n + 1 : ℕ)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (n + 1)).2 (hanti.summable_of_integrableOn_Ioi hf hfn)
  have hκ : Summable fun i : ℕ => kernelWeight (n + i) := by
    simpa only [Nat.add_comm n] using (summable_nat_add_iff n).2 critical_shape_masses.2.2.1
  have hcomp : ∀ i : ℕ, kernelWeight (n + i) ≤ B * f (↑(i + n + 1 : ℕ)) := by
    intro i
    rw [Nat.add_comm i n]
    have hm : 0 < ((n + i + 1 : ℕ) : ℝ) := by positivity
    have he : 1 / (((n + i + 1 : ℕ) : ℝ) * Real.sqrt ((n + i + 1 : ℕ) : ℝ)) =
        f (↑(n + i + 1 : ℕ)) := by
      let m : ℝ := ((n + i + 1 : ℕ) : ℝ)
      change 1 / (m * Real.sqrt m) = m ^ (-(3 / 2 : ℝ))
      rw [Real.sqrt_eq_rpow]
      calc
        _ = 1 / (m ^ (1 : ℝ) * m ^ (1 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by
          rw [← Real.rpow_add hm, one_div, ← Real.rpow_neg hm.le]
          norm_num [m]
    rw [← he]
    exact hW _ (by omega)
  apply (hκ.tsum_le_tsum hcomp (hw.mul_left B)).trans
  rw [tsum_mul_left]
  have hb := mul_le_mul_of_nonneg_left (hanti.tsum_comp_add_le_integral n hf hfn) hB.le
  refine hb.trans_eq ?_
  dsimp [f] at *
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(3 / 2 : ℝ)) < -1) hn0,
    show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num,
    Real.rpow_neg hn0.le, ← Real.sqrt_eq_rpow]
  ring

private theorem weighted_generator_summable {u : ℤ → ℝ} {B : ℝ}
    (hB : ∀ z, |u z| ≤ B) (z : ℤ) :
    Summable (fun i : ℕ => kernelWeight i *
      (u (z + (i + 1 : ℕ)) + u (z - (i + 1 : ℕ)) - 2 * u z)) := by
  have hK : Summable kernelWeight := critical_shape_masses.2.2.1
  apply (hK.mul_right (4 * B)).of_norm_bounded
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg i)]
  have h : |u (z + (i + 1 : ℕ)) + u (z - (i + 1 : ℕ)) - 2 * u z| ≤ 4 * B := by
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h' := (abs_add_le (u (z + (i + 1 : ℕ))) (u (z - (i + 1 : ℕ)))).trans
      (add_le_add (hB _) (hB _))
    linarith only [h', hB z]
  exact mul_le_mul_of_nonneg_left h (kernel_nonneg i)

/-- Far crossing jumps are the only potentially negative terms on the
residual. Their total yields a one-sided, uniform polynomial bound. -/
private theorem residual_generator_lower :
    ∃ E > (0 : ℝ), ∀ n : ℕ, 0 < n →
      -(E * (n : ℝ) ^ (-(5 / 4 : ℝ))) ≤ actualGenerator residualProfile (n : ℤ) := by
  obtain ⟨B,hB,hTail⟩ := kernel_tail_weight
  let ln2 := Real.log 2
  have hl : 0 < ln2 := Real.log_pos (by norm_num)
  refine ⟨4 * B / ln2, div_pos (by positivity) hl, ?_⟩
  intro n hn
  let z := (n : ℤ)
  let u := residualProfile
  let w (i : ℕ) := kernelWeight i * (u (z + (i + 1 : ℕ)) + u (z - (i + 1 : ℕ)) - 2 * u z)
  let v (i : ℕ) := kernelWeight (n + i) * (-(2 * u z))
  have hK : Summable kernelWeight := critical_shape_masses.2.2.1
  have hW : Summable w := weighted_generator_summable
    (by intro z; rw [abs_of_nonneg (residual_nonneg z)]; exact residual_le z) z
  have hPart : Summable (fun i : ℕ => kernelWeight (i + n)) :=
    (summable_nat_add_iff n).2 hK
  have hV : Summable v := by
    simpa only [v, Nat.add_comm n] using hPart.mul_right (-(2 * u z))
  have hTailLower : (∑' i : ℕ, v i) ≤ ∑' i : ℕ, w (i + n) := by
    apply Summable.tsum_le_tsum _ hV ((summable_nat_add_iff n).2 hW)
    intro i
    dsimp only [v,w]
    rw [add_comm i n]
    apply mul_le_mul_of_nonneg_left _ (kernel_nonneg (n + i))
    linarith only [residual_nonneg (z + (n + i + 1 : ℕ)), residual_nonneg (z - (n + i + 1 : ℕ))]
  have hFinite : 0 ≤ ∑ i ∈ Finset.range n, w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (kernel_nonneg i)
      (residual_second_local n (i + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
  have hLow : (∑' i : ℕ, v i) ≤ actualGenerator residualProfile (n : ℤ) := by
    change _ ≤ ∑' i : ℕ, w i
    rw [← hW.sum_add_tsum_nat_add n]
    exact hTailLower.trans (le_add_of_nonneg_left hFinite)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hU : u z ≤ (n : ℝ) ^ (-(3 / 4 : ℝ)) / ln2 := by
    change (2+|((n : ℕ) : ℝ)|) ^ (-(3 / 4 : ℝ)) / Real.log (2+|((n : ℕ) : ℝ)|) ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have hL2 : ln2 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_le_log (by norm_num) (by linarith)
    apply (div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num))
      (hl.le.trans hL2)).trans
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _) hl hL2
  have hU0 : 0 ≤ u z := residual_nonneg z
  have hT := hTail n hn
  have hEq : (2 * B / Real.sqrt (n : ℝ)) * (2 * ((n : ℝ) ^ (-(3 / 4 : ℝ)) / ln2)) =
      (4 * B / ln2) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv (2 * B), ← Real.rpow_neg hn0.le]
    calc
      _ = (4 * B / ln2) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(3 / 4 : ℝ))) := by ring
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num
  have hBound : (∑' i : ℕ, kernelWeight (n + i)) * (2 * u z) ≤
      (4 * B / ln2) * (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
    have hh := mul_le_mul hT (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ)≤2))
      (by positivity : 0 ≤ 2 * u z) (by positivity : 0 ≤ 2 * B / Real.sqrt (n : ℝ))
    exact hh.trans_eq hEq
  apply le_trans _ hLow
  dsimp only [v]
  rw [tsum_mul_right, mul_neg]
  exact neg_le_neg hBound

private theorem discrepancyProfile_nonneg (z : ℤ) : 0 ≤ discrepancyProfile z := by
  have hx : 1 < (2 : ℝ) + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  unfold discrepancyProfile
  exact one_div_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.log_pos hx).le)

private theorem discrepancyProfile_bounded (z : ℤ) : |discrepancyProfile z| ≤ 1 / Real.log 2 := by
  have hx : 2 ≤ (2 : ℝ) + |(z : ℝ)| := by linarith [abs_nonneg (z : ℝ)]
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt (2 + |(z : ℝ)|) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith)
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
  rw [abs_of_nonneg (discrepancyProfile_nonneg z), discrepancyProfile]
  apply one_div_le_one_div_of_le hln
  simpa only [one_mul] using mul_le_mul hsqrt hl hln.le (Real.sqrt_nonneg _)

/-- Exact decomposition of the logarithmic profile, with no omitted
high-exponent term. -/
private theorem discrepancy_eq_truncated_add_residual (z : ℤ) :
    discrepancyProfile z = truncatedProfile z + residualProfile z := by
  let X := 2+|(z : ℝ)|
  have hx : 1 < X := by dsimp [X]; linarith [abs_nonneg (z : ℝ)]
  have hp : 0 < X := zero_lt_one.trans hx
  have htr : truncatedProfile z = (1 - X ^ (-(1 / 4 : ℝ))) / (Real.sqrt X * Real.log X) := by
    exact (truncated_profile_analysis.1 z).2
  rw [htr]
  change 1 / (Real.sqrt X * Real.log X) = _ + X ^ (-(3 / 4 : ℝ)) / Real.log X
  have he : X ^ (-(3 / 4 : ℝ)) = X ^ (-(1 / 2 : ℝ)) * X ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hp]
    norm_num
  have hf : X ^ (-(1 / 2 : ℝ)) = (Real.sqrt X)⁻¹ := by
    rw [Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
  rw [he, hf]
  ring

private theorem actualGenerator_add_bounded {u v : ℤ → ℝ} {B C : ℝ}
    (hU : ∀ z, |u z| ≤ B) (hV : ∀ z, |v z| ≤ C) (z : ℤ) :
    actualGenerator (u + v) z = actualGenerator u z + actualGenerator v z := by
  have hsum := (weighted_generator_summable hU z).tsum_add (weighted_generator_summable hV z)
  unfold actualGenerator
  rw [← hsum]
  apply tsum_congr
  intro i
  simp only [Pi.add_apply]
  ring

private theorem generator_decompose (z : ℤ) :
    actualGenerator discrepancyProfile z =
      actualGenerator truncatedProfile z + actualGenerator residualProfile z := by
  have hres (x : ℤ) : |residualProfile x| ≤ 1 / Real.log 2 := by
    rw [abs_of_nonneg (residual_nonneg x)]
    exact residual_le x
  have htr (x : ℤ) : |truncatedProfile x| ≤ 2 / Real.log 2 := by
    have heq : truncatedProfile x = discrepancyProfile x - residualProfile x := by
      linarith only [discrepancy_eq_truncated_add_residual x]
    rw [heq]
    exact ((abs_sub _ _).trans (add_le_add (discrepancyProfile_bounded x) (hres x))).trans_eq
      (by ring)
  have hf : discrepancyProfile = truncatedProfile + residualProfile := by
    funext x
    exact discrepancy_eq_truncated_add_residual x
  rw [hf, actualGenerator_add_bounded htr hres]

private theorem discrepancyProfile_sq_nat (n : ℕ) (hn : 1 < n) :
    (discrepancyProfile (n : ℤ)) ^ 2 ≤ 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  let N := (n : ℝ)
  have hN1 : 1 < N := by dsimp [N]; exact_mod_cast hn
  have hl := Real.log_pos hN1
  have hN : 0 < N := zero_lt_one.trans hN1
  have he : discrepancyProfile (n : ℤ) = 1 / (Real.sqrt (2 + N) * Real.log (2 + N)) := by
    change 1 / (Real.sqrt (2 + |N|) * Real.log (2 + |N|)) = _
    rw [abs_of_nonneg hN.le]
  have hp : discrepancyProfile (n : ℤ) ≤ 1 / (Real.sqrt N * Real.log N) := by
    rw [he]
    apply one_div_le_one_div_of_le (mul_pos (Real.sqrt_pos.mpr hN) hl)
    exact mul_le_mul (Real.sqrt_le_sqrt (by linarith))
      (Real.log_le_log hN (by linarith)) hl.le (Real.sqrt_nonneg _)
  apply (pow_le_pow_left₀ (discrepancyProfile_nonneg _) hp 2).trans_eq
  rw [div_pow, mul_pow, Real.sq_sqrt hN.le, one_pow]

private theorem generator_even {u : ℤ → ℝ} (h : Function.Even u) :
    Function.Even (actualGenerator u) := by
  intro x
  unfold actualGenerator
  apply tsum_congr
  intro i
  rw [show -x + (i + 1 : ℕ) = -(x - (i + 1 : ℕ)) by ring,
    show -x - (i + 1 : ℕ) = -(x + (i + 1 : ℕ)) by ring, h, h, h]
  ring

private theorem discrepancyProfile_even : Function.Even discrepancyProfile := by
  intro x
  simp [discrepancyProfile]

private theorem eventual_residual_absorb {E c : ℝ} (hE : 0 < E) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      E * (n : ℝ) ^ (-(5 / 4 : ℝ)) ≤ (c / 2) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2) := by
  have h₀ := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ)<1 / 4)).bound
    (show 0 < c / (2 * E) by positivity)
  have h := tendsto_natCast_atTop_atTop.eventually h₀
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with n hn h2
  let N := (n : ℝ)
  have hN2 : 2 ≤ N := by dsimp [N]; exact_mod_cast h2
  have hN : 0 < N := by linarith
  have hL := Real.log_pos (by linarith : 1 < N)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hn
  have hx : (Real.log N) ^ 2 ≤ (c / (2 * E)) * N ^ (1 / 4 : ℝ) := by
    simpa only [← Real.rpow_natCast, Nat.cast_ofNat] using hn
  have hX := mul_le_mul_of_nonneg_left hx
    (show 0 ≤ E * N ^ (-(5 / 4 : ℝ)) * N by positivity)
  change E * N ^ (-(5 / 4 : ℝ)) ≤ (c / 2) / (N * (Real.log N) ^ 2)
  apply (le_div_iff₀ (by positivity)).2
  have hpow : N ^ (-(5 / 4 : ℝ)) * N * N ^ (1 / 4 : ℝ) = 1 := by
    calc
      _ = (N ^ (-(5 / 4 : ℝ)) * N ^ (1 : ℝ)) * N ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hN, ← Real.rpow_add hN]; norm_num
  calc
    _ = (E * N ^ (-(5 / 4 : ℝ)) * N) * (Real.log N) ^ 2 := by ring
    _ ≤ _ := hX
    _ = _ := by
      calc
        _ = (E * (c / (2 * E))) * (N ^ (-(5 / 4 : ℝ)) * N * N ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [hpow, mul_one]; field_simp

/-- Strict eventual gain for the full logarithmic profile, for both signs
of the integer site. This is the linear estimate only. -/
theorem eventual_discrepancy_linear_gain :
    ∃ A > (0 : ℝ), ∃ N : ℕ, ∀ z : ℤ, (N : ℤ) < |z| →
      A * (discrepancyProfile z) ^ 2 ≤ actualGenerator discrepancyProfile z := by
  obtain ⟨c,hc,hg⟩ := truncated_profile_analysis.2
  obtain ⟨E,hE,he⟩ := residual_generator_lower
  have hb := eventual_residual_absorb hE hc
  have hNat : ∀ᶠ n : ℕ in atTop,
      (c / 2) * (discrepancyProfile (n : ℤ)) ^ 2 ≤ actualGenerator discrepancyProfile (n : ℤ) := by
    filter_upwards [hg, hb, eventually_ge_atTop (2 : ℕ)] with n hn hm h2
    have h1 : 1 < n := by omega
    have hp : 0 < n := by omega
    have hR := he n hp
    have hsq := mul_le_mul_of_nonneg_left (discrepancyProfile_sq_nat n h1)
      (show 0 ≤ c / 2 by positivity)
    rw [generator_decompose]
    have halg : (c / 2) * (1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)) =
      c / ((n : ℝ) * Real.log (n : ℝ) ^ 2) - (c / 2) / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := by ring
    rw [halg] at hsq
    linarith only [hsq, hR, hn, hm]
  obtain ⟨N,hN⟩ := eventually_atTop.1 hNat
  refine ⟨c / 2, by positivity, N, ?_⟩
  intro z hz
  have hzNat : N < z.natAbs := by
    rw [← Int.natCast_natAbs] at hz
    exact_mod_cast hz
  have h := hN z.natAbs hzNat.le
  rcases Int.natAbs_eq z with heq | heq
  · rw [← heq] at h
    exact h
  · rw [heq, discrepancyProfile_even, generator_even discrepancyProfile_even]
    exact h

end D5.S1.Words.Patterns.Separable.OccupiedResidualGain
