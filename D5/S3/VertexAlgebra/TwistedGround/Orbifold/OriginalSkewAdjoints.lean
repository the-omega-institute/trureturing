/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalSkewAdjoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite original corrected-field adjoint and original-source translation transpose. -/

import D5.S3.VertexAlgebra.SourceBPZ.AllStateTranspose
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import Batteries.Tactic.OpenPrivate

/-!
The actual corrected-field inversion on a monomial has oscillator cutoff R.
Positive charge energy puts R at most d on every monomial in a grade-d source.
The original Sugawara nilpotence gives the common finite interval.
The original BPZ identity on the stress state gives the translation transpose.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeHalfFock LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticeInvolution
open ActualChargedAdjoint CorrectedInversion MvPolynomial
open MixedIntertwiner (fixedGrade)
open LatticeHalfFockFiniteCorrection (sourceWeight)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open private conformal_polynomial_homogeneous conformal_polynomial_lowering from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

private abbrev sourceL1 (D : LatticeData) :=
  sugawaraMode D (LatticeSugawaraCurrents.gramComplex D)⁻¹ 1

set_option maxHeartbeats 1600000 in
/-- The finite corrected-field adjoint on an entire original lattice grade.
The common cutoff applies to both source parities and to arbitrary actual tensor vectors. -/
theorem actual_corrected_adjoint_of_grade (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (d e : ℤ)
    (a : Carrier D) (ha : a ∈ grade D d) (x y : ActualTensor D hu) :
    actualForm D hu ((correctedField D hu a).coeff e x) y =
      (-1 : ℂ)^d * ∑ j ∈ Finset.range (d.toNat + 1),
        (j.factorial : ℂ)⁻¹ *
          actualForm D hu x ((correctedField D hu ((sourceL1 D ^ j) a)).coeff
            (-e - 4*d + 2*(j : ℤ)) y) := by
  classical
  let F : Carrier D →ₗ[ℂ] ℂ := ∑ j ∈ Finset.range (d.toNat + 1),
    (j.factorial : ℂ)⁻¹ •
      (K_R D hu (-e - 4*d + 2*(j : ℤ)) x y).comp (sourceL1 D ^ j)
  have evaluate (b : Carrier D) : F b = ∑ j ∈ Finset.range (d.toNat + 1),
      (j.factorial : ℂ)⁻¹ *
        K_R D hu (-e - 4*d + 2*(j : ℤ)) x y ((sourceL1 D ^ j) b) := by
    simp only [F, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  change K_L D hu e x y a = (-1 : ℂ)^d * ∑ j ∈ Finset.range (d.toNat + 1),
    (j.factorial : ℂ)⁻¹ * K_R D hu (-e - 4*d + 2*(j : ℤ)) x y
      ((sourceL1 D ^ j) a)
  rw [← evaluate]
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  have basis (α : Charge D) (m : Index D →₀ ℕ) (hm : m ∈ (a α).support) :
      K_L D hu e x y (Finsupp.single α (monomial m 1)) =
        (-1 : ℂ)^d * F (Finsupp.single α (monomial m 1)) := by
    let R := m.weight (sourceWeight D)
    let b : Carrier D := Finsupp.single α (monomial m 1)
    have henergy : chargeEnergy D α + (R : ℤ) = d := by
      change energy D (α, m) = d
      by_contra hn
      exact (MvPolynomial.mem_support_iff.mp hm)
        ((mem_grade_iff D d a).mp ha (α, m) hn)
    have hR : R ≤ d.toNat := by
      have hc := chargeEnergy_nonneg D hD α
      omega
    have hnorm : chargeNorm D α = 2 * chargeEnergy D α :=
      (two_chargeEnergy D α).symm
    have hsign : paritySign (chargeNorm D α / 2) * (-1 : ℂ)^R = (-1 : ℂ)^d := by
      have hp : paritySign (chargeNorm D α / 2) = (-1 : ℂ)^(chargeEnergy D α) := by
        change paritySign (bilinear D α α / 2) = _
        rw [chargeEnergy, paritySign, neg_one_zpow_eq_ite]
      rw [hp, ← zpow_natCast (-1 : ℂ) R, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        henergy]
    have hshift (j : ℕ) : -e - 2*chargeNorm D α - 4*(R : ℤ) + 2*(j : ℤ) =
        -e - 4*d + 2*(j : ℤ) := by omega
    let term := fun j : ℕ => (j.factorial : ℂ)⁻¹ *
      K_R D hu (-e - 4*d + 2*(j : ℤ)) x y ((sourceL1 D ^ j) b)
    have inv := actual_corrected_monomial_inversion D hu α m e x y
    change K_L D hu e x y b = paritySign (chargeNorm D α / 2) * (-1 : ℂ)^R *
      ∑ j ∈ Finset.range (R + 1), K_R D hu
        (-e - 2*chargeNorm D α - 4*(R : ℤ) + 2*(j : ℤ)) x y
        (Finsupp.single α ((j.factorial : ℂ)⁻¹ •
          (((SourceMobius.sectorL1 D α).toLinearMap ^ j) (monomial m 1)))) at inv
    simp_rw [hsign, hshift, ← Finsupp.smul_single,
      ← SourceMobius.sugawara_pow_single D _ hHG hGH, map_smul, smul_eq_mul] at inv
    change K_L D hu e x y b = (-1 : ℂ)^d * ∑ j ∈ Finset.range (R + 1), term j at inv
    change K_L D hu e x y b = _
    rw [inv]
    congr 1
    rw [evaluate]
    change (∑ j ∈ Finset.range (R + 1), term j) = ∑ j ∈ Finset.range (d.toNat + 1), term j
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro j hj hnot
      have hle : R + 1 ≤ j := Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
      have hz : (sourceL1 D ^ j) b = 0 := Module.End.pow_map_zero_of_le hle
        (SourceMobius.actual_sugawara_one_monomial_bound D hu α m 1)
      simp [term, hz]
  have expansion : a = ∑ α ∈ a.support, ∑ m ∈ (a α).support,
      (a α).coeff m • Finsupp.single α (monomial m 1) := by
    calc
      a = ∑ α ∈ a.support, Finsupp.single α (a α) :=
        (Finsupp.sum_single a).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro α _
        conv_lhs => arg 2; rw [(a α).as_sum]
        rw [Finsupp.single_finsetSum]
        apply Finset.sum_congr rfl
        intro m _
        simp only [Finsupp.smul_single, smul_monomial, smul_eq_mul, mul_one]
  rw [expansion]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro m hm
  rw [basis α m hm]
  ring

/-- The original corrected-field adjoint specialized to the fixed grade. -/
theorem actual_corrected_grade_adjoint (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (d e : ℤ)
    (a : fixedGrade D d) (x y : ActualTensor D hu) :
    actualForm D hu ((correctedField D hu a.val).coeff e x) y =
      (-1 : ℂ)^d * ∑ j ∈ Finset.range (d.toNat + 1),
        (j.factorial : ℂ)⁻¹ *
          actualForm D hu x ((correctedField D hu ((sourceL1 D ^ j) a.val)).coeff
            (-e - 4*d + 2*(j : ℤ)) y) :=
  actual_corrected_adjoint_of_grade D hu hD d e a.val a.property.1 x y

/-- BPZ transpose of the literal original translation and the original
inverse-Gram Sugawara mode one. -/
theorem sourcePairing_translation (D : LatticeData) (hu : IsUnit D.G.det)
    (u v : Carrier D) :
    sourcePairing D (translation D u) v = sourcePairing D u (sourceL1 D v) := by
  classical
  let H := (LatticeSugawaraCurrents.gramComplex D)⁻¹
  let w := LatticeActualConformalState.omega D H
  let P := LatticeActualConformalState.conformalPolynomial D H
  have hHG := Matrix.nonsing_inv_mul _ (SourceMobius.gram_det_unit D hu)
  have hGH := Matrix.mul_nonsing_inv _ (SourceMobius.gram_det_unit D hu)
  have hw : w ∈ grade D 2 := by
    rw [mem_grade_iff]
    rintro ⟨α, m⟩ hm
    by_cases hα : α = 0
    · subst α
      change (Finsupp.single (0 : Charge D) P 0).coeff m = 0
      rw [Finsupp.single_eq_same]
      apply (conformal_polynomial_homogeneous D H).coeff_eq_zero
      intro he
      apply hm
      change chargeEnergy D 0 + (m.weight (sourceWeight D) : ℤ) = 2
      simp [he]
    · simp [w, LatticeActualConformalState.omega, Finsupp.single_apply, hα, Ne.symm hα]
  have killed : sourceL1 D w = 0 := by
    change sourceL1 D (Finsupp.single 0 P) = 0
    have hp := SourceMobius.sugawara_pow_single D H hHG hGH (0 : Charge D) P 1
    rw [pow_one, pow_one] at hp
    change sourceL1 D (Finsupp.single 0 P) = _ at hp
    rw [hp]
    change Finsupp.single (0 : Charge D) (SourceMobius.sectorL1 D 0 P) = 0
    rw [conformal_polynomial_lowering D H, Finsupp.single_zero]
  have powers (j : ℕ) (hj : j ≠ 0) : (sourceL1 D ^ j) w = 0 := by
    have h1 : (sourceL1 D ^ (1 : ℕ)) w = 0 := by simpa using killed
    exact Module.End.pow_map_zero_of_le (Nat.pos_of_ne_zero hj) h1
  have h0 : ((Y D w)[[0]]) = translation D := by
    simpa [w] using (LatticeActualConformalState.omega_modes D H (-1)).trans
      (sugawaraMode_minus_one_eq_translation D H hHG hGH)
  have h2 : ((Y D w)[[2]]) = sourceL1 D := by
    simpa [w, H] using LatticeActualConformalState.omega_modes D H 1
  have law := SourceBPZ.AllStateTranspose.sourcePairing_allState D hu 2 0 w hw u v
  rw [h0, Finset.sum_eq_single 0] at law
  · norm_num at law
    simpa [h2] using law
  · intro j _ hj
    rw [powers j hj]
    simp
  · intro hj
    exact (hj (Finset.mem_range.mpr (Nat.succ_pos _))).elim

/-- Every power of the original fixed translation transposes to the same
power of the original source lowering operator. -/
theorem sourcePairing_fixedTranslation_pow (D : LatticeData) (hu : IsUnit D.G.det)
    (j : ℕ) (u : FixedCarrier D) (a : Carrier D) :
    sourcePairing D ((fixedTranslation D ^ j) u).val a =
      sourcePairing D u.val ((sourceL1 D ^ j) a) := by
  induction j generalizing a with
  | zero => simp
  | succ j ih =>
    rw [pow_succ' (fixedTranslation D), Module.End.mul_apply]
    change sourcePairing D (translation D ((fixedTranslation D ^ j) u).val) a = _
    rw [sourcePairing_translation D hu, ih, pow_succ (sourceL1 D), Module.End.mul_apply]

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints
