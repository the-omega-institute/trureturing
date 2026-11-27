/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedRelationLimsup
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHWeightedRelationLimsup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A uniform disjoint relation deficit gives a quantitative gap in the RH left-window limsup. -/

import D5.S3.Fourier.WeightedIntegerRelations
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHWeightedPhaseLimsup

/-! The disjoint relation bound at the actual zero cutoff transfers to the normalized arithmetic
limsup as the window width tends to zero from above. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder

open D5.S3.Fourier.WeightedIntegerRelations
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)

private theorem harmonic_weight_pos (j : PositiveZetaZero) : 0 < harmonicWeight j := by
  have hmult : 0 < Zeta23.zeroMult j.val :=
    Nat.zero_lt_of_lt (Zeta23.ZetaSeam.one_le_mult_holds j.val j.property.1)
  have hmultReal : (0 : ℝ) < (Zeta23.zeroMult j.val : ℝ) := by exact_mod_cast hmult
  exact div_pos (mul_pos hmultReal j.property.2) (by positivity)

/-- An eventual disjoint relation bound of size `ε` lowers the original normalized
left-window upper limit by at least `ε` times the full coefficient. The rows and
their coefficients may vary with the cutoff. -/
theorem signed_window_limsup_le_of_eventually_disjoint_relations
    {A : Type*} (hRH : RiemannHypothesis) (m r : ℕ) (hm : 2 ≤ m) (heven : m + 1 = 2 * r)
    (hμ : μ r ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hpacking : ∀ᶠ T : ℝ in atTop,
      let columns := positiveCutoff hRH T
      ∃ (rows : Finset A) (k : A → PositiveZetaZero → ℤ),
        (∀ a ∈ rows, ∑ j ∈ columns, (k a j : ℝ) * ordinate j = 0) ∧
        (∀ a ∈ rows, ∃ j ∈ columns, k a j ≠ 0) ∧
        (∀ a ∈ rows, ∀ b ∈ rows, a ≠ b → ∀ j ∈ columns, k a j = 0 ∨ k b j = 0) ∧
        ε ≤ (1 / (2 * harmonicMass hRH T)) * ∑ a ∈ rows,
          ‖(1 : ℂ) - Complex.I ^ (∑ j ∈ columns, k a j)‖ ^ 2 /
            (∑ j ∈ columns, (k a j : ℝ) ^ 2 / harmonicWeight j)) :
    let s := orderRate m
    let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
    let V := fun L u : ℝ =>
      |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
        powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r u|
    let Q := fun L : ℝ => limsup (V L) atTop / (L * (Real.log (1 / L)) ^ 2)
    let κ := |(μ r : ℝ)| / (4 * Real.pi * s)
    limsup Q (𝓝[>] 0) ≤ κ * (1 - ε) ∧ limsup Q (𝓝[>] 0) < κ := by
  let s := orderRate m
  let cm := (μ (m + 1) : ℝ) * (((m : ℝ) + 1) / ((m : ℝ) * s))
  let V := fun L u : ℝ =>
    |signedWindowResidual m (Real.exp u) (Real.exp (u + L)) /
      powerGap s (Real.exp u) (Real.exp (u + L)) + cm + (μ r : ℝ) * rootSignal r u|
  let Q := fun L : ℝ => limsup (V L) atTop / (L * (Real.log (1 / L)) ^ 2)
  let κ := |(μ r : ℝ)| / (4 * Real.pi * s)
  let cutoff (L : ℝ) := 2 * (r : ℝ) / L
  change limsup Q (𝓝[>] 0) ≤ κ * (1 - ε) ∧ limsup Q (𝓝[>] 0) < κ
  have hr : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hmReal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < s := by
    change 0 < 1 / 2 - ((m : ℝ) + 1)⁻¹
    rw [sub_pos, inv_eq_one_div, div_lt_iff₀ (by positivity)]
    linarith
  have hμReal : (μ r : ℝ) ≠ 0 := by exact_mod_cast hμ
  have hκ : 0 < κ := div_pos (abs_pos.mpr hμReal) (by positivity)
  have hcut : Tendsto cutoff (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [cutoff, div_eq_mul_inv] using
      (tendsto_const_mul_atTop_of_pos (mul_pos two_pos hr)).2 tendsto_inv_nhdsGT_zero
  have hmass : ∀ᶠ T : ℝ in atTop, 0 < harmonicMass hRH T := by
    filter_upwards [(harmonic_mass_limit hRH).eventually_const_lt
      (by positivity : 0 < 1 / (4 * Real.pi))] with T hT
    exact ((div_pos_iff.mp hT).resolve_right (fun h => (sq_nonneg _).not_gt h.2)).1
  have hdeficit : ∀ᶠ T : ℝ in atTop, ε ≤ weightedPhaseDefect hRH T := by
    filter_upwards [hpacking, hmass] with T hT hW
    obtain ⟨rows, k, hrel, hrow, hdisj, hεT⟩ := hT
    exact hεT.trans (weighted_phase_deficit_disjoint (positiveCutoff hRH T) rows
      ordinate harmonicWeight k (fun j _ => harmonic_weight_pos j)
      hrel hrow hdisj hW)
  obtain ⟨hbounded, hformula, _⟩ := signed_window_even_cutoff_weighted_phase hRH m r hm heven
  change Tendsto (fun L => Q L - κ * (1 - weightedPhaseDefect hRH (cutoff L)))
    (𝓝[>] 0) (𝓝 0) at hformula
  have hpositive : ∀ᶠ L : ℝ in 𝓝[>] 0, 0 < L := self_mem_nhdsWithin
  have hQ_nonneg : ∀ᶠ L in 𝓝[>] (0 : ℝ), 0 ≤ Q L := by
    filter_upwards [hbounded, hpositive] with L hL hLpos
    exact div_nonneg
      (le_limsup_of_frequently_le (Frequently.of_forall fun u => abs_nonneg _) hL)
      (mul_nonneg hLpos.le (sq_nonneg _))
  have hupper : limsup Q (𝓝[>] 0) ≤ κ * (1 - ε) := by
    apply le_of_forall_pos_le_add
    intro η hη
    apply limsup_le_of_le (isCoboundedUnder_le_of_eventually_le _ hQ_nonneg)
    filter_upwards [hcut.eventually hdeficit, hformula.eventually_lt_const hη] with L hD herror
    have hlead := mul_le_mul_of_nonneg_left (sub_le_sub_left hD 1) hκ.le
    linarith only [hlead, herror]
  exact ⟨hupper, hupper.trans_lt (by nlinarith only [mul_pos hκ hε])⟩

#print axioms signed_window_limsup_le_of_eventually_disjoint_relations

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
