/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSparseZeroPhaseAlignment
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHSparseZeroPhaseAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse omitted zeta zeros give the full signed-window coefficient. -/

import D5.S3.Analytic.Oscillation.SparseOrdinateMass
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedPhaseLimsup
import D5.S3.Fourier.WeightedPhaseRelationLattice

/-! Application to the actual positive zeta ordinates and analytic multiplicities. -/

set_option autoImplicit false

open Filter Set ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum (zetaSpectrum)
open D5.S3.Analytic.Oscillation.SparseOrdinateMass (cutoffSum harmonicMass_tendsto_zero)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

noncomputable section

/-- Omitted positive zeta zeros through the same inclusive cutoff as the full mass. -/
def omittedCutoff (hRH : RiemannHypothesis) (S : Set ℝ) (T : ℝ) :
    Finset PositiveZetaZero := by
  classical
  exact (positiveCutoff hRH T).filter (fun j => ordinate j ∉ S)

/-- The original multiplicities of omitted positive zeta zeros. -/
def omittedCount (hRH : RiemannHypothesis) (S : Set ℝ) (T : ℝ) : ℕ :=
  ∑ j ∈ omittedCutoff hRH S T, Zeta23.zeroMult j.val

/-- The original harmonic weights of omitted positive zeta zeros. -/
def omittedMass (hRH : RiemannHypothesis) (S : Set ℝ) (T : ℝ) : ℝ :=
  ∑ j ∈ omittedCutoff hRH S T, harmonicWeight j

/-- A sparse omitted multiplicity count gives vanishing mass on the squared logarithmic scale. -/
theorem omittedMass_tendsto_zero (hRH : RiemannHypothesis) (S : Set ℝ)
    (hcount : Tendsto (fun T : ℝ => (omittedCount hRH S T : ℝ) / (T * Real.log T))
      atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => omittedMass hRH S T / Real.log T ^ 2) atTop (𝓝 0) := by
  classical
  let m (j : PositiveZetaZero) := if ordinate j ∉ S then Zeta23.zeroMult j.val else 0
  let finite_le : ∀ T : ℝ, {j : PositiveZetaZero | ordinate j ≤ T}.Finite :=
    (zetaSpectrum hRH).finite_le
  have count_eq (T : ℝ) :
      (omittedCount hRH S T : ℝ) = cutoffSum ordinate finite_le (fun j => (m j : ℝ)) T := by
    rw [omittedCount, Nat.cast_sum, omittedCutoff, Finset.sum_filter]
    change (∑ j ∈ positiveCutoff hRH T,
      if ordinate j ∉ S then (Zeta23.zeroMult j.val : ℝ) else 0) =
      ∑ j ∈ positiveCutoff hRH T, (m j : ℝ)
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ordinate j ∈ S <;> simp [m, hj]
  have mass_eq (T : ℝ) :
      omittedMass hRH S T = cutoffSum ordinate finite_le
        (fun j => (m j : ℝ) * ordinate j / (1 / 4 + ordinate j ^ 2)) T := by
    rw [omittedMass, omittedCutoff, Finset.sum_filter]
    change (∑ j ∈ positiveCutoff hRH T,
      if ordinate j ∉ S then harmonicWeight j else 0) =
      ∑ j ∈ positiveCutoff hRH T, (m j : ℝ) * ordinate j / (1 / 4 + ordinate j ^ 2)
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ordinate j ∈ S <;> simp [m, hj, harmonicWeight]
  simp_rw [count_eq] at hcount
  simp_rw [mass_eq]
  exact harmonicMass_tendsto_zero ordinate m finite_le (fun j => j.property.2) hcount

/-- At a cutoff of positive mass, a rationally independent set of ordinates leaves at most
twice the omitted fraction of harmonic mass as a common-time phase deficit. -/
theorem weightedPhaseDefect_le_omittedMass (hRH : RiemannHypothesis) (S : Set ℝ)
    (hS : LinearIndependent ℚ (fun γ : S => (γ : ℝ))) (T : ℝ)
    (hW : 0 < harmonicMass hRH T) :
    weightedPhaseDefect hRH T ≤ 2 * omittedMass hRH S T / harmonicMass hRH T := by
  classical
  let cutoff := positiveCutoff hRH T
  let kept := cutoff.filter (fun j => ordinate j ∈ S)
  let embed (j : ↥kept) : S := ⟨ordinate j, (Finset.mem_filter.mp j.property).2⟩
  have hfreq : LinearIndependent ℚ (fun j : ↥kept => ordinate j) :=
    hS.comp embed fun _ _ h => Subtype.ext ((zetaSpectrum hRH).gamma_injective
      (congrArg Subtype.val h))
  let orbit (v : ℝ) (j : ↥kept) := Circle.exp (ordinate j * v)
  let quarter : ↥kept → Circle := fun _ => Circle.exp (Real.pi / 2)
  have hquarter : quarter ∈ closure (range orbit) := by
    rw [D5.S3.Fourier.WeightedPhaseRelationLattice.closure_real_phase_orbit]
    intro k hk
    have hrat : ∀ j, (k j : ℚ) = 0 :=
      Fintype.linearIndependent_iff.mp hfreq (fun j => (k j : ℚ)) (by
        simpa only [Rat.smul_def, Rat.cast_intCast] using hk)
    have hzero (j : ↥kept) : k j = 0 := by exact_mod_cast hrat j
    simp [hzero]
  have hweight (j : PositiveZetaZero) : 0 ≤ harmonicWeight j := by
    have hj : 0 < ordinate j := j.property.2
    unfold harmonicWeight
    positivity
  let score (s : Finset PositiveZetaZero) (p : ↥s → Circle) :=
    ∑ j : ↥s, harmonicWeight j * (p j : ℂ).im
  have hscore (s : Finset PositiveZetaZero) : Continuous (score s) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul
      (Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_apply j)))
  have hfull : BddAbove (range (weightedSine hRH T)) := by
    refine (isCompact_univ.image (hscore cutoff)).bddAbove.mono ?_
    rintro _ ⟨v, rfl⟩
    refine ⟨fun j => Circle.exp (ordinate j * v), mem_univ _, ?_⟩
    simp only [score, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
    exact Finset.sum_coe_sort cutoff (fun j => harmonicWeight j * Real.sin (ordinate j * v))
  have hscore_bound :
      score kept quarter ≤ weightedSineSup hRH T + omittedMass hRH S T := by
    apply closure_minimal
      (t := {p | score kept p ≤ weightedSineSup hRH T + omittedMass hRH S T}) ?_
      (isClosed_le (hscore kept) continuous_const) hquarter
    rintro _ ⟨v, rfl⟩
    change score kept (orbit v) ≤ weightedSineSup hRH T + omittedMass hRH S T
    have hsplit :
        score kept (orbit v) + (∑ j ∈ omittedCutoff hRH S T,
          harmonicWeight j * Real.sin (ordinate j * v)) = weightedSine hRH T v := by
      simp only [score, orbit, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
      rw [Finset.sum_coe_sort kept (fun j => harmonicWeight j * Real.sin (ordinate j * v))]
      exact Finset.sum_filter_add_sum_filter_not cutoff (fun j => ordinate j ∈ S)
        (fun j => harmonicWeight j * Real.sin (ordinate j * v))
    have homit : -(omittedMass hRH S T) ≤ ∑ j ∈ omittedCutoff hRH S T,
        harmonicWeight j * Real.sin (ordinate j * v) := by
      rw [omittedMass, ← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => by
        simpa only [mul_neg, mul_one] using
          mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (ordinate j * v)) (hweight j)
    have hsup : weightedSine hRH T v ≤ weightedSineSup hRH T :=
      le_csSup hfull (mem_range_self v)
    linarith
  have hmass : score kept quarter + omittedMass hRH S T = harmonicMass hRH T := by
    simp only [score, quarter, Circle.coe_exp, Complex.exp_ofReal_mul_I_im,
      Real.sin_pi_div_two, mul_one,
      Finset.sum_coe_sort, omittedMass, harmonicMass]
    exact Finset.sum_filter_add_sum_filter_not cutoff (fun j => ordinate j ∈ S) harmonicWeight
  rw [weightedPhaseDefect, ← div_self hW.ne', ← sub_div]
  exact div_le_div_of_nonneg_right (by linarith) hW.le

/-- A sparse omitted multiplicity count in a rationally independent set forces the actual
weighted phase deficit to tend to zero at infinity. -/
theorem weightedPhaseDefect_tendsto_zero_of_sparse_count
    (hRH : RiemannHypothesis) (S : Set ℝ)
    (hS : LinearIndependent ℚ (fun γ : S => (γ : ℝ)))
    (hcount : Tendsto (fun T : ℝ => (omittedCount hRH S T : ℝ) / (T * Real.log T))
      atTop (𝓝 0)) :
    Tendsto (weightedPhaseDefect hRH) atTop (𝓝 0) := by
  have hlimit := harmonic_mass_limit hRH
  have hκ : 0 < (1 : ℝ) / (4 * Real.pi) := by positivity
  have hsmall := omittedMass_tendsto_zero hRH S hcount
  have hratio : Tendsto (fun T : ℝ => 2 * omittedMass hRH S T / harmonicMass hRH T)
      atTop (𝓝 0) := by
    have hnorm := (hsmall.const_mul 2).div hlimit hκ.ne'
    rw [mul_zero, zero_div] at hnorm
    refine hnorm.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    change 2 * (omittedMass hRH S T / Real.log T ^ 2) /
      (harmonicMass hRH T / Real.log T ^ 2) = _
    rw [← mul_div_assoc, div_div_div_cancel_right₀ (pow_ne_zero _ (Real.log_pos hT).ne')]
  have hpos : ∀ᶠ T in atTop, 0 < harmonicMass hRH T := by
    filter_upwards [(tendsto_order.mp hlimit).1 _ hκ] with T hT
    exact (div_pos_iff.mp hT).elim And.left fun h => (not_lt_of_ge (sq_nonneg _) h.2).elim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hratio ?_ ?_
  · filter_upwards [hpos] with T hW
    exact sub_nonneg.mpr ((div_le_one hW).mpr (weighted_sine_sup_bounds hRH T).2)
  · filter_upwards [hpos] with T hW
    exact weightedPhaseDefect_le_omittedMass hRH S hS T hW

/-- Under the sparse-count condition, the original signed and power-gap normalized
left-endpoint late limsup has the full leading coefficient. -/
theorem signed_window_even_cutoff_full_coefficient_of_sparse_count
    (hRH : RiemannHypothesis) (S : Set ℝ)
    (hS : LinearIndependent ℚ (fun γ : S => (γ : ℝ)))
    (hcount : Tendsto (fun T : ℝ => (omittedCount hRH S T : ℝ) / (T * Real.log T))
      atTop (𝓝 0))
    (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r) (hμ : μ r ≠ 0) :
    let s := orderRate m
    let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    let V := fun L u : ℝ =>
      |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r u|
    let Q := fun L : ℝ => limsup (V L) atTop / (L * (Real.log (1 / L)) ^ 2)
    (∀ᶠ L in 𝓝[>] (0 : ℝ), (atTop : Filter ℝ).IsBoundedUnder (· ≤ ·) (V L)) ∧
      Tendsto Q (𝓝[>] 0) (𝓝 (|(μ r : ℝ)| / (4 * Real.pi * s))) := by
  dsimp only
  obtain ⟨hbound, _, hcoeff⟩ := signed_window_even_cutoff_weighted_phase hRH m r hm heven
  exact ⟨hbound, (hcoeff hμ).mpr
    (weightedPhaseDefect_tendsto_zero_of_sparse_count hRH S hS hcount)⟩

end

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
