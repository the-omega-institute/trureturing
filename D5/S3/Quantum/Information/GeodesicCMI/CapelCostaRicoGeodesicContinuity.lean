/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoGeodesicContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Geodesic relative entropy is continuous on the positive cone in its first argument at fixed reference. -/

import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoGeodesicModular
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! For Capel and Costa Rico, *Geodesic Quantum f-Divergences*
(arXiv:2608.15833v1), equations (52), (59), and (63), we prove continuity of the
native formula up to the positive semidefinite boundary when the second argument
is fixed and faithful. This is the boundary approached by the faithful mixtures
in Remark 3.5. The result supplies the continuity step for trureturing #32416. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI

open Matrix Set
open scoped ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The modular matrix in (52) is positive semidefinite for a positive semidefinite
first argument. The fixed inverse-square-root factor is self-adjoint by real CFC. -/
theorem geodesicModular_posSemidef (t : ℝ) {r : Matrix n n ℂ} (hr : r.PosSemidef)
    (s : Matrix n n ℂ) : (geodesicModular t r s).PosSemidef := by
  have hpow (p : ℝ) : (cfc (fun z : ℝ => z ^ p) r).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp <|
      cfc_nonneg fun _ hz => Real.rpow_nonneg (spectrum_nonneg_of_nonneg hr.nonneg hz) p
  let q : Matrix n n ℂ := cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s
  have hq : qᴴ = q := by
    have h : IsSelfAdjoint q := IsSelfAdjoint.cfc (a := s)
    exact h.isHermitian.eq
  have hright : (q * cfc (fun z : ℝ => z ^ t) r * q).PosSemidef := by
    simpa only [hq] using (hpow t).conjTranspose_mul_mul_same q
  rw [geodesicModular_eq_kronecker]
  exact (hpow (1 - t)).kronecker hright.transpose

/-- Equation (52) is continuous in the first argument on the positive semidefinite
cone for each fixed reference and each interpolation parameter in `[0, 1]`. -/
theorem continuousOn_geodesicModular (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (s : Matrix n n ℂ) :
    ContinuousOn (fun r => geodesicModular t r s) {r | r.PosSemidef} := by
  have hpow (p : ℝ) (hp : 0 ≤ p) :
      ContinuousOn (cfc (fun z : ℝ => z ^ p)) {r : Matrix n n ℂ | r.PosSemidef} :=
    continuousOn_id.cfc_of_mem_nhdsSet (s := (Set.univ : Set ℝ)) (fun z : ℝ => z ^ p)
      Filter.univ_mem (fun _ hr => hr.isHermitian.isSelfAdjoint)
      (Real.continuous_rpow_const hp).continuousOn
  have hleft :
      ContinuousOn (cfc (fun z : ℝ => z ^ (1 - t))) {r : Matrix n n ℂ | r.PosSemidef} := by
    rcases lt_or_eq_of_le ht₁ with ht | rfl
    · exact hpow (1 - t) (sub_nonneg.mpr ht.le)
    · refine (continuousOn_const (c := (1 : Matrix n n ℂ))).congr ?_
      intro r hr
      simpa only [sub_self, Real.rpow_zero] using
        (cfc_const_one ℝ r hr.isHermitian.isSelfAdjoint)
  let q : Matrix n n ℂ := cfc (fun z : ℝ => (Real.sqrt z)⁻¹) s
  have hright : ContinuousOn (fun r => q * cfc (fun z : ℝ => z ^ t) r * q)
      {r : Matrix n n ℂ | r.PosSemidef} :=
    ((continuousOn_const (c := q)).mul (hpow t ht₀)).mul (continuousOn_const (c := q))
  rw [continuousOn_iff_continuous_domRestrict] at hleft hright ⊢
  refine continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => ?_
  simp only [Set.domRestrict_apply, geodesicModular_eq_kronecker, Matrix.kronecker_apply,
    Matrix.transpose_apply]
  exact (hleft.matrix_elem i₁ j₁).mul (hright.matrix_elem j₂ i₂)

/-- The native geodesic relative entropy in (59) and (63) is continuous in its
first positive semidefinite argument for a fixed faithful reference. The same
continuity holds for the totalized native expression at any fixed matrix `s`. -/
theorem continuousOn_geodesicRelativeEntropy (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (s : Matrix n n ℂ) :
    ContinuousOn (fun r => geodesicRelativeEntropy t r s) {r | r.PosSemidef} := by
  have hlog : ContinuousOn (fun r => cfc (fun z : ℝ => z * Real.log z)
      (geodesicModular t r s)) {r | r.PosSemidef} :=
    (continuousOn_geodesicModular t ht₀ ht₁ s).cfc_of_mem_nhdsSet
      (s := (Set.univ : Set ℝ)) (fun z : ℝ => z * Real.log z) Filter.univ_mem
      (fun _ hr => (geodesicModular_posSemidef t hr s).isHermitian.isSelfAdjoint)
      Real.continuous_mul_log.continuousOn
  unfold geodesicRelativeEntropy
  rw [continuousOn_iff_continuous_domRestrict] at hlog ⊢
  exact Complex.continuous_re.comp <|
    (continuous_const (y := star (weightedVector s))).dotProduct
      (hlog.matrix_mulVec (continuous_const (y := weightedVector s)))

end

end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoReverseGeodesicCMI
