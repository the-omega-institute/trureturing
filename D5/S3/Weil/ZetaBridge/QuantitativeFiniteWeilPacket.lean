/- GID: D5/S3/Weil/ZetaBridge/QuantitativeFiniteWeilPacket
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/QuantitativeFiniteWeilPacket
   mirror-E: none(waiver:finite-node-quantitative-packet-construction)
   anchors: []
   digest: Construct actual unit-support Burnol packets with explicit interpolation jets and an explicit exceptional cutoff from certified finite radii and squared-node gaps. -/

import D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets
import D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket

/-!
# Actual packets from finite quantitative nodal data

The two node catalogs are the existing reflection quotients of actual zero
indices: first the selected orbit union, then the explicit exceptional ball.
All gap and radius hypotheses are finite nodal statements. The seed derivative
bounds and peak tail cutoff are constructed here rather than supplied.

The scalar infinite spectral tail remains a separate number-theoretic input
in the final majorant theorem. This file does not postulate the
Brent--Platt--Trudgian estimate or silently promote its literature citation to
a Lean theorem. It eliminates the previously uncomputed finite interpolation
jets and the eventual-smallness selection of the exceptional radius.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.ZetaBridge.QuantitativeFiniteWeilPacket

open Set MeasureTheory
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
open D5.S3.Weil.TestFunctions.QuantitativeEvenInterpolationJets
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.ZetaBridge.FiniteReflectionCompatibleWeilInterpolation
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.UnitSupportBurnolPacket
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.WeilMixedHeadTailBudget
open scoped BigOperators ComplexConjugate

/-- The same reflection-node image used by the existing interpolation owner. -/
def reflectionNodeSet (Z : ZeroData) (E : Finset ℕ) : Finset ℂ :=
  E.image (fun j => Z.gamma (reflectionRep Z j))

/-- Finite-index interpolation with actual jets, preserving the existing
reflection quotient and the original test-function state space. -/
theorem quantitative_interpolation_on_finite_indices
    (Z : ZeroData) (E : Finset ℕ) (a : ℕ → ℂ) (R sigma V : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (hV : 0 ≤ V)
    (ha : ∀ j, a (Z.reflection j) = a j)
    (hbound : ∀ j ∈ E, ‖Z.gamma j‖ ≤ R)
    (hvalue : ∀ j ∈ E, ‖a j‖ ≤ V)
    (hgap : ∀ u v : reflectionNodeSet Z E, u ≠ v →
      sigma ≤ ‖u.1 ^ 2 - v.1 ^ 2‖) :
    ∃ g : WeilTestFunction,
      (∀ j ∈ E, fourierLaplace g (Z.gamma j) = a j) ∧
      tsupport (g : ℝ → ℂ) ⊆ Icc (-1) 1 ∧
      ∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (g : ℝ → ℂ)) x‖) ≤
          interpolationJetBudget (reflectionNodeSet Z E).card R sigma V s := by
  classical
  let S := reflectionNodeSet Z E
  let chosen (z : S) : ℕ := Classical.choose (Finset.mem_image.mp z.property)
  have chosen_mem (z : S) : chosen z ∈ E :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).1
  have chosen_spec (z : S) : Z.gamma (reflectionRep Z (chosen z)) = z.1 :=
    (Classical.choose_spec (Finset.mem_image.mp z.property)).2
  let values (z : S) : ℂ := a (reflectionRep Z (chosen z))
  have hz (z : S) : ‖z.1‖ ≤ R := by
    rw [← chosen_spec z]
    rcases reflectionRep_freq Z (chosen z) with h | h
    · rw [h]
      exact hbound _ (chosen_mem z)
    · rw [h, norm_neg]
      exact hbound _ (chosen_mem z)
  have hv (z : S) : ‖values z‖ ≤ V := by
    dsimp [values]
    rw [reflectionRep_value Z a ha]
    exact hvalue _ (chosen_mem z)
  obtain ⟨g, hg, hs, hjets⟩ := exists_even_interpolant_with_explicit_jets
    (fun z : S => z.1) values R sigma V hR hsigma hV hz hv hgap
  have hrep (j : ℕ) (hj : j ∈ E) :
      fourierLaplace g (Z.gamma (reflectionRep Z j)) = a j := by
    let z : S := ⟨Z.gamma (reflectionRep Z j), Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    have hread := hg z
    have heq : reflectionRep Z (chosen z) = reflectionRep Z j :=
      gamma_injective Z (chosen_spec z)
    change fourierLaplace g (Z.gamma (reflectionRep Z j)) =
      a (reflectionRep Z (chosen z)) at hread
    rw [heq, reflectionRep_value Z a ha j] at hread
    exact hread
  have hr : quantitativeSeedRadius R ≤ 1 := by
    unfold quantitativeSeedRadius
    apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).2
    nlinarith
  refine ⟨g, ?_, ?_, ?_⟩
  · intro j hj
    rcases reflectionRep_freq Z j with hsame | hneg
    · rw [← hsame]
      exact hrep j hj
    · calc
        fourierLaplace g (Z.gamma j) = fourierLaplace g (-Z.gamma j) :=
          (fourierLaplace_neg g (Z.gamma j)).symm
        _ = fourierLaplace g (Z.gamma (reflectionRep Z j)) := by rw [hneg]
        _ = a j := hrep j hj
  · intro x hx
    have h := hs hx
    exact ⟨(neg_le_neg hr).trans h.1, h.2.trans hr⟩
  · intro s hsq
    simpa only [S, Fintype.card_coe] using hjets s hsq

/-- Explicit cutoff for a unit target peak; only finite arithmetic is used. -/
def quantitativePeakRadius (d : ℕ) (R sigma : ℝ) : ℝ :=
  R + 6 * (interpolationJetBudget d R sigma 1 0 +
    interpolationJetBudget d R sigma 1 2) + 1

/-- Construct the actual peak, its two jets and its specified spectral cutoff. -/
theorem exists_quantitative_finite_unit_peak
    (Z : ZeroData) (E : Finset ℕ) (R sigma : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma)
    (hbound : ∀ j ∈ E, ‖Z.gamma j‖ ≤ R)
    (hgap : ∀ u v : reflectionNodeSet Z E, u ≠ v →
      sigma ≤ ‖u.1 ^ 2 - v.1 ^ 2‖) :
    ∃ b : WeilTestFunction,
      (∀ j ∈ E, fourierLaplace b (Z.gamma j) = 1) ∧
      tsupport (b : ℝ → ℂ) ⊆ Icc (-1) 1 ∧
      (∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (b : ℝ → ℂ)) x‖) ≤
          interpolationJetBudget (reflectionNodeSet Z E).card R sigma 1 s) ∧
      E ⊆ Z.symmetricIndices (quantitativePeakRadius (reflectionNodeSet Z E).card R sigma) ∧
      ∀ n ∉ Z.symmetricIndices (quantitativePeakRadius (reflectionNodeSet Z E).card R sigma),
        ‖fourierLaplace b (Z.gamma n)‖ ≤ (1 / 2 : ℝ) ∧
        ‖fourierLaplace b (conj (Z.gamma n))‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨b, hb, hs, hj⟩ := quantitative_interpolation_on_finite_indices
    Z E (fun _ => 1) R sigma 1 hR hsigma (by norm_num) (fun _ => rfl)
    hbound (fun _ _ => by simp) hgap
  let J0 := interpolationJetBudget (reflectionNodeSet Z E).card R sigma 1 0
  let J2 := interpolationJetBudget (reflectionNodeSet Z E).card R sigma 1 2
  have h0 : (∫ x : ℝ, ‖b x‖) ≤ J0 := by simpa only [Function.iterate_zero_apply] using hj 0 (by omega)
  have h2 : (∫ x : ℝ, ‖((deriv^[2]) (b : ℝ → ℂ)) x‖) ≤ J2 := hj 2 le_rfl
  have hnonneg : 0 ≤ J0 + J2 := add_nonneg
    ((integral_nonneg fun x => norm_nonneg (b x)).trans h0)
    ((integral_nonneg fun x => norm_nonneg (((deriv^[2]) (b : ℝ → ℂ)) x)).trans h2)
  have hlarge : 2 * (3 * (J0 + J2)) + 1 ≤
      quantitativePeakRadius (reflectionNodeSet Z E).card R sigma := by
    change 2 * (3 * (J0 + J2)) + 1 ≤ R + 6 * (J0 + J2) + 1
    linarith
  refine ⟨b, hb, hs, hj, ?_, peak_tail_of_two_jet_budget Z b J0 J2 _ hs h0 h2 hlarge⟩
  intro j hjE
  rw [Z.mem_symmetricIndices]
  have hbR := hbound j hjE
  change ‖Z.gamma j‖ ≤ R + 6 * (J0 + J2) + 1
  linarith

private theorem signed_assignment_norm_le_one (Z : ZeroData) (n j : ℕ) :
    ‖orbitSignedAssignment Z n j‖ ≤ 1 := by
  unfold orbitSignedAssignment
  split_ifs <;> norm_num

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A quantitative actual packet. The two supplied gaps are finite certificates
for the target catalog and the explicitly determined exception catalog.
No peak tail, derivative seminorm or unknown cutoff is supplied. -/
theorem exists_quantitative_orbitBurnolPacket
    (F : FiniteEvenWeilOrbitFrame Z ι) (R sigma tau : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 < sigma) (htau : 0 < tau)
    (hbound : ∀ j ∈ frameTargetIndices F, ‖Z.gamma j‖ ≤ R)
    (hgapTarget : ∀ u v : reflectionNodeSet Z (frameTargetIndices F), u ≠ v →
      sigma ≤ ‖u.1 ^ 2 - v.1 ^ 2‖)
    (hgapException : ∀ u v : reflectionNodeSet Z
        (Z.symmetricIndices (quantitativePeakRadius
          (reflectionNodeSet Z (frameTargetIndices F)).card R sigma)), u ≠ v →
      tau ≤ ‖u.1 ^ 2 - v.1 ^ 2‖) :
    let H := quantitativePeakRadius (reflectionNodeSet Z (frameTargetIndices F)).card R sigma
    let E := Z.symmetricIndices H
    ∃ P : OrbitBurnolPacket F,
      P.exceptional = E ∧
      tsupport (P.peak : ℝ → ℂ) ⊆ Icc (-1) 1 ∧
      (∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1) ∧
      ∀ i, ∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (P.killer i : ℝ → ℂ)) x‖) ≤
          interpolationJetBudget (reflectionNodeSet Z E).card H tau 1 s := by
  classical
  let H := quantitativePeakRadius (reflectionNodeSet Z (frameTargetIndices F)).card R sigma
  let E := Z.symmetricIndices H
  obtain ⟨b, hb, hbs, hbj, hOE, htail⟩ := exists_quantitative_finite_unit_peak
    Z (frameTargetIndices F) R sigma hR hsigma hbound hgapTarget
  have hH : 0 ≤ H := by
    unfold H quantitativePeakRadius interpolationJetBudget interpolationCoefficientBudget
      interpolationJetScale
    positivity
  have hkexists (i : ι) : ∃ k : WeilTestFunction,
      (∀ j ∈ E, fourierLaplace k (Z.gamma j) = orbitSignedAssignment Z (F.index i) j) ∧
      tsupport (k : ℝ → ℂ) ⊆ Icc (-1) 1 ∧
      ∀ s : ℕ, s ≤ 2 →
        (∫ x : ℝ, ‖((deriv^[s]) (k : ℝ → ℂ)) x‖) ≤
          interpolationJetBudget (reflectionNodeSet Z E).card H tau 1 s := by
    apply quantitative_interpolation_on_finite_indices Z E _ H tau 1 hH htau (by norm_num)
      (orbitSignedAssignment_reflection Z (F.index i))
    · intro j hj
      exact (Z.mem_symmetricIndices).mp hj
    · intro j _
      exact signed_assignment_norm_le_one Z (F.index i) j
    · exact hgapException
  choose k hk hks hkj using hkexists
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
  exact ⟨P, rfl, hbs, hks, hkj⟩

/-- The remaining scalar spectral budget controls the actual mixed total.
The supplied finite jets here are the closed formulas produced by the packet
constructor above. The infinite scalar tail is explicitly not removed. -/
theorem packet_majorant_of_uniform_jets
    (F : FiniteEvenWeilOrbitFrame Z ι) (P : OrbitBurnolPacket F)
    (E : Finset ℕ) (J0 J2 Theta : ℝ)
    (hs : ∀ i, tsupport (P.killer i : ℝ → ℂ) ⊆ Icc (-1) 1)
    (h0 : ∀ i, (∫ x : ℝ, ‖P.killer i x‖) ≤ J0)
    (h2 : ∀ i, (∫ x : ℝ, ‖((deriv^[2]) (P.killer i : ℝ → ℂ)) x‖) ≤ J2)
    (hspectral : Summable (fun n : {n : ℕ // n ∉ E} => fourthMomentSummand Z n.1))
    (htail : (∑' n : {n : ℕ // n ∉ E}, fourthMomentSummand Z n.1) ≤ Theta) :
    finiteMixedMajorantTotal Z P.killer ≤
      (3 * (Fintype.card ι : ℝ) * (J0 + J2)) ^ 2 *
        ((∑ n ∈ E, fourthMomentSummand Z n) + Theta) := by
  have h := finiteMixedMajorantTotal_le_unit_support_jets Z P.killer E
    (fun _ => J0) (fun _ => J2) Theta hs h0 h2 hspectral htail
  have heq : (∑ _i : ι, 3 * (J0 + J2)) = 3 * (Fintype.card ι : ℝ) * (J0 + J2) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rwa [heq] at h

#print axioms quantitative_interpolation_on_finite_indices
#print axioms exists_quantitative_finite_unit_peak
#print axioms exists_quantitative_orbitBurnolPacket
#print axioms packet_majorant_of_uniform_jets

end D5.S3.Weil.ZetaBridge.QuantitativeFiniteWeilPacket
