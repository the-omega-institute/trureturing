/- GID: D5/S3/Weil/ZetaBridge/UnitSupportBurnolPacket
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/UnitSupportBurnolPacket
   mirror-E: none(waiver:fixed-unit-packet-support)
   anchors: []
   digest: Construct the actual Burnol packet with B=K=1 and derive an explicit exceptional radius from two certified peak seminorms. -/

import D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget

/-!
# Unit-support Burnol packets and an explicit exceptional-radius test

The finite interpolation stage can use B=K=1. This reconstructs the packet;
it does not assert these bounds for the earlier arbitrary chosen packet.
Convolution depth still enlarges the final support to at most N+2.
No derivative bound uniform over colliding zero nodes is inferred.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket

open Set MeasureTheory
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.WeilBurnolSupportBudget
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open scoped BigOperators ComplexConjugate

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reconstruct both the peak and every killer in the fixed unit window. -/
theorem exists_unit_support_orbitBurnolPacket (F : FiniteEvenWeilOrbitFrame Z ι) :
    ∃ P : OrbitBurnolPacket F,
      tsupport (P.peak : ℝ → ℂ) ⊆ Icc (-1) 1 ∧
      ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1 := by
  classical
  obtain ⟨b, hb, hbs⟩ := exists_even_weil_finite_unit_peak_unit_support Z (frameTargetIndices F)
  obtain ⟨E, hOE, htail⟩ := exists_common_exceptional_ball Z b (frameTargetIndices F)
  have hkexists (i : ι) : ∃ k : WeilTestFunction,
      (∀ j ∈ E, fourierLaplace k (Z.gamma j) = orbitSignedAssignment Z (F.index i) j) ∧
      tsupport (k : ℝ → ℂ) ⊆ Icc (-1) 1 :=
    even_weil_interpolation_on_finite_indices_unit_support Z E
      (orbitSignedAssignment Z (F.index i)) (orbitSignedAssignment_reflection Z (F.index i))
  choose k hk hks using hkexists
  have hn (i : ι) : F.index i ∈ frameTargetIndices F :=
    orbit_subset_frameTargetIndices F i (by simp [zeroOrbit])
  have hcn (i : ι) : Z.conjugation (F.index i) ∈ frameTargetIndices F :=
    orbit_subset_frameTargetIndices F i (by simp [zeroOrbit])
  have hconjEval (g : WeilTestFunction) (j : ℕ) :
      fourierLaplace g (conj (Z.gamma j)) =
        fourierLaplace g (Z.gamma (Z.conjugation j)) := by
    rw [Z.gamma_conjugation, fourierLaplace_neg]
  let P : OrbitBurnolPacket F :=
    { peak := b
      killer := k
      exceptional := E
      target_subset := hOE
      peak_values := by
        intro i
        exact ⟨hb _ (hn i), (hconjEval b _).trans (hb _ (hcn i))⟩
      killer_values := by
        intro i j
        have hvalues := orbitSignedAssignment_on_frame F i j
        exact ⟨(hk i _ (hOE (hn j))).trans hvalues.1,
          (hconjEval (k i) _).trans ((hk i _ (hOE (hcn j))).trans hvalues.2)⟩
      kills_exception := by
        intro i j hj hjO
        rw [hk i j hj]
        apply orbitSignedAssignment_zero_of_not_mem
        exact fun h => hjO (orbit_subset_frameTargetIndices F i h)
      peak_tail := htail }
  exact ⟨P, hbs, hks⟩

/-- Unit peak and killer support gives the exact arithmetic radius budget N+2. -/
theorem unit_support_burnol_radius (F : FiniteEvenWeilOrbitFrame Z ι)
    (P : OrbitBurnolPacket F)
    (hp : tsupport (P.peak : ℝ → ℂ) ⊆ Icc (-1) 1)
    (hk : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1)
    (N : ℕ) (a : ι → ℂ) :
    tsupport (burnolSynthesis F P N a : ℝ → ℂ) ⊆
      Icc (-((N : ℝ) + 2)) ((N : ℝ) + 2) := by
  simpa only [mul_one, add_assoc, one_add_one_eq_two] using
    burnolSynthesis_tsupport_subset F P 1 1 hp hk N a

/-- Two actual L1 seminorm bounds yield a specified exceptional spectral ball.
The sufficient radius is 2*(3*(J0+J2))+1; no eventual-smallness choice is used. -/
theorem peak_tail_of_two_jet_budget
    (Z : ZeroData) (b : WeilTestFunction) (J0 J2 R : ℝ)
    (hs : tsupport (b : ℝ → ℂ) ⊆ Icc (-1) 1)
    (hJ0 : (∫ x : ℝ, ‖b x‖) ≤ J0)
    (hJ2 : (∫ x : ℝ, ‖((deriv^[2]) (b : ℝ → ℂ)) x‖) ≤ J2)
    (hR : 2 * (3 * (J0 + J2)) + 1 ≤ R) :
    ∀ n ∉ Z.symmetricIndices R,
      ‖fourierLaplace b (Z.gamma n)‖ ≤ (1 / 2 : ℝ) ∧
      ‖fourierLaplace b (conj (Z.gamma n))‖ ≤ (1 / 2 : ℝ) := by
  let D : ℝ := 3 * (J0 + J2)
  have hD : 0 ≤ D := by
    have h0 := (integral_nonneg fun x => norm_nonneg (b x)).trans hJ0
    have h2 := (integral_nonneg fun x => norm_nonneg (((deriv^[2]) (b : ℝ → ℂ)) x)).trans hJ2
    dsimp [D]
    linarith
  intro n hn
  have him : |(Z.gamma n).im| ≤ (1 / 2 : ℝ) := by
    rw [ZeroData.gamma, ← gammaOf_eq_spectralParameter]
    exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial n).2).le
  have him2 : (Z.gamma n).im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have hl := (abs_le.mp him).1
    have hu := (abs_le.mp him).2
    have hprod := mul_nonneg
      (show 0 ≤ (Z.gamma n).im + (1 / 2 : ℝ) by linarith)
      (show 0 ≤ (1 / 2 : ℝ) - (Z.gamma n).im by linarith)
    nlinarith
  have hnorm : ‖Z.gamma n‖ ^ 2 = (Z.gamma n).re ^ 2 + (Z.gamma n).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hlarge : 2 * D + 1 < ‖Z.gamma n‖ := by
    have hnot : ¬ ‖Z.gamma n‖ ≤ R := by simpa only [Z.mem_symmetricIndices] using hn
    exact lt_of_le_of_lt hR (lt_of_not_ge hnot)
  have hlarge2 : (2 * D + 1) ^ 2 < ‖Z.gamma n‖ ^ 2 := by
    nlinarith [norm_nonneg (Z.gamma n)]
  have hden : 2 * D ≤ 1 + (Z.gamma n).re ^ 2 := by
    nlinarith [sq_nonneg D]
  have hratio : D * inverseQuadraticEnvelope Z n ≤ (1 / 2 : ℝ) := by
    rw [inverseQuadraticEnvelope, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0 < 1 + (Z.gamma n).re ^ 2)).2
    nlinarith
  have h := zero_transform_pair_le_three_jets Z b J0 J2 hs hJ0 hJ2 n
  exact ⟨h.1.trans hratio, h.2.trans hratio⟩

#print axioms exists_unit_support_orbitBurnolPacket
#print axioms unit_support_burnol_radius
#print axioms peak_tail_of_two_jet_budget

end D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket
