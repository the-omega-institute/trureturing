/- GID: D5/S3/VertexAlgebra/LatticeActualLZeroGrading
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeActualLZeroGrading
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Sugawara zero-mode eigenspaces and all-integer mode grading. -/

/-
Exact eigenspaces of the ACTUAL Sugawara zero mode and all-integer
closure of the ACTUAL state-field modes. The actual operator and fused
energy proof are loaded from sealed sources, never replaced by a definition.
Bakalov--Kac math/0402315v1 Def2.2 (2.23)--(2.24), Thm4.1/(4.16).
Imported Kalle Kytölä Sugawara architecture: Apache 2.0, VirasoroProject
5ff4245383b2cdd4eea7a0524bc1274c32041eb4; exact lattice adaptations
remain in the sealed supplier, imported read-only.
-/
import D5.S3.VertexAlgebra.LatticeEnergyGrading
import D5.S3.VertexAlgebra.LatticeActualConformalEnergy
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace D5.S3.VertexAlgebra.LatticePositiveEnergy
open LatticeGeneratingFieldLocality LatticeAllStateField
open LatticeAllStateReconstruction LatticeSugawaraConformal
open LatticeSugawaraCurrents
open LatticeActualConformalEnergy MvPolynomial
open scoped BigOperators VertexOperator DirectSum
noncomputable section

theorem chargeEnergy_complex_half (D : LatticeData) (a : Charge D) :
    (chargeEnergy D a : ℂ) = (bilinear D a a : ℂ) / 2 := by
  have h : (2 : ℂ) * (chargeEnergy D a : ℂ) = (bilinear D a a : ℂ) := by
    exact_mod_cast two_chargeEnergy D a
  linear_combination h / 2

@[simp] theorem carrierCoeffEquiv_basis (D : LatticeData) (a : Label D) :
    carrierCoeffEquiv D (carrierBasis D a) = Finsupp.single a 1 :=
  (carrierBasis D).repr_self a

/-- Eigenformula consumed on the exact all-charge actual monomial basis. -/
theorem actualL0_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (a : Label D) :
    sugawaraMode D H 0 (carrierBasis D a) = (energy D a : ℂ) • carrierBasis D a := by
  rw [carrierBasis_apply]
  have hp : IsWeightedHomogeneous (fun x : Index D => x.2 + 1)
      (monomial a.2 (1 : ℂ)) (oscillatorEnergy a.2) := by
    apply isWeightedHomogeneous_monomial
    rfl
  rw [sugawaraMode_weighted_homogeneous D H hHG hGH a.1
    (monomial a.2 (1 : ℂ)) (oscillatorEnergy a.2) hp]
  congr 2
  simp only [energy, Int.cast_add, Int.cast_natCast]
  rw [chargeEnergy_complex_half]
  ring

/-- Every coefficient of an arbitrary actual state, including mixed energies. -/
theorem actualL0_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (v : Carrier D) (a : Label D) :
    carrierCoeffEquiv D (sugawaraMode D H 0 v) a =
      (energy D a : ℂ) * carrierCoeffEquiv D v a := by
  classical
  let f : Carrier D →ₗ[ℂ] ℂ := (Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap
  have he : f.comp (sugawaraMode D H 0) = (energy D a : ℂ) • f := by
    apply (carrierBasis D).ext
    intro b
    change f (sugawaraMode D H 0 (carrierBasis D b)) =
      (energy D a : ℂ) • f (carrierBasis D b)
    rw [actualL0_basis D H hHG hGH, map_smul]
    change (energy D b : ℂ) * carrierCoeffEquiv D (carrierBasis D b) a =
      (energy D a : ℂ) * carrierCoeffEquiv D (carrierBasis D b) a
    rw [carrierCoeffEquiv_basis]
    by_cases hb : b = a
    · subst b
      rfl
    · simp only [Finsupp.single_apply, if_neg hb, mul_zero]
  exact LinearMap.congr_fun he v

/-- Both inclusions follow by coefficient separation; no homogeneity premise. -/
theorem actualL0_eigen_iff_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (n : ℤ) (v : Carrier D) :
    sugawaraMode D H 0 v = (n : ℂ) • v ↔ v ∈ grade D n := by
  classical
  constructor
  · intro hv
    rw [mem_grade_iff]
    intro a ha
    have h := congrArg (fun w : Carrier D => carrierCoeffEquiv D w a) hv
    rw [actualL0_coeff D H hHG hGH] at h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
    have hne : (energy D a : ℂ) ≠ (n : ℂ) := by
      exact_mod_cast ha
    exact (mul_eq_mul_right_iff.mp h).resolve_left hne
  · intro hv
    apply (carrierCoeffEquiv D).injective
    ext a
    rw [actualL0_coeff D H hHG hGH]
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases ha : energy D a = n
    · rw [ha]
    · have hz : carrierCoeffEquiv D v a = 0 := (mem_grade_iff D n v).mp hv a ha
      rw [hz]
      simp

theorem actualL0_eigenspace_eq_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) (n : ℤ) :
    (sugawaraMode D H 0).eigenspace (n : ℂ) = grade D n := by
  ext v
  rw [Module.End.mem_eigenspace_iff]
  exact actualL0_eigen_iff_grade D H hHG hGH n v

/-- Actual fused products at every integer q, derived from all-state covariance. -/
theorem actual_mode_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (m n q : ℤ) (a b : Carrier D) (ha : a ∈ grade D m) (hb : b ∈ grade D n) :
    ((Y D a)[[q]]) b ∈ grade D (m + n - q - 1) := by
  apply (actualL0_eigen_iff_grade D H hHG hGH _ _).mp
  have hea := (actualL0_eigen_iff_grade D H hHG hGH m a).mpr ha
  have heb := (actualL0_eigen_iff_grade D H hHG hGH n b).mpr hb
  have h := fused_eigenstate_energy D H hHG hGH a b (m : ℂ) (n : ℂ) hea heb q
  simpa [mu] using h

/-- Real positive definiteness gives a complex inverse without integral det-unit. -/
theorem complex_inverse_exists (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    ∃ H : Matrix (Fin D.rank) (Fin D.rank) ℂ,
      H * gramComplex D = 1 ∧ gramComplex D * H = 1 := by
  classical
  have hR : (D.G.map (Int.cast : ℤ → ℝ)).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit |>.ne_zero
  have hC : (gramComplex D).det ≠ 0 := by
    have he : gramComplex D = (D.G.map (Int.cast : ℤ → ℝ)).map Complex.ofRealHom := by
      ext i j
      simp [gramComplex]
    rw [he]
    change (Complex.ofRealHom.mapMatrix (D.G.map (Int.cast : ℤ → ℝ))).det ≠ 0
    rw [← RingHom.map_det]
    exact Complex.ofReal_ne_zero.mpr hR
  have hu : IsUnit (gramComplex D).det := isUnit_iff_ne_zero.mpr hC
  exact ⟨(gramComplex D)⁻¹, Matrix.nonsing_inv_mul _ hu, Matrix.mul_nonsing_inv _ hu⟩

/-- Positivity alone suffices for the actual all-integer mode closure. -/
theorem positive_actual_mode_grade (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (m n q : ℤ) (a b : Carrier D) (ha : a ∈ grade D m) (hb : b ∈ grade D n) :
    ((Y D a)[[q]]) b ∈ grade D (m + n - q - 1) := by
  obtain ⟨H,hHG,hGH⟩ := complex_inverse_exists D hD
  exact actual_mode_grade D H hHG hGH m n q a b ha hb

#print axioms actualL0_basis
#print axioms actualL0_coeff
#print axioms actualL0_eigenspace_eq_grade
#print axioms actual_mode_grade
#print axioms complex_inverse_exists
#print axioms positive_actual_mode_grade
end
end D5.S3.VertexAlgebra.LatticePositiveEnergy
