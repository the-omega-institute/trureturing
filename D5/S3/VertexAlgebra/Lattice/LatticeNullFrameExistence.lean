/- GID: D5/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeNullFrameExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original lattice light-cone coordinates and charge-dependent null frames. -/

/- The original integral Charge, complex bilinear Gram form and oscillator
carrier are preserved. No positivity or operator-transport certificate is
assumed. The coordinate input and null-frame input were fallible uncompiled
drafts; this implementation repairs them against the current native API.
Classical setting: Bakalov--Kac, arXiv math/0402315v1, section 4.1.
The claims are algebraic tools, with no BRST or no-ghost conclusion.
proof_shape: content
admission_basis: escape-witness
escape_witness: Explicit inverse substitutions, Gram directional derivatives,
and isotropic-vector normalization are proved on the original carrier.
-/
import D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-! Charge-dependent null-frame existence and exact transverse dimension. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeNullFrameExistence

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeLightConeCoordinates

/-- The standard library bilinear form of the actual complex Gram matrix. -/
abbrev gramBilin (D : LatticeData) : LinearMap.BilinForm ℂ (E D) :=
  (gramComplex D).toBilin'

@[simp] private theorem gramBilin_apply (D : LatticeData) (u v : E D) :
    gramBilin D u v = g D u v :=
  Matrix.toBilin'_apply (gramComplex D) u v

private theorem gramBilin_isSymm (D : LatticeData) : (gramBilin D).IsSymm := by
  constructor
  intro u v
  simpa only [gramBilin_apply] using g_symm D u v

/-- A genuine inverse-Gram equation implies actual nondegeneracy.
Only the left-inverse equation is needed for a finite square matrix. -/
theorem gramBilin_nondegenerate (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) : (gramBilin D).Nondegenerate := by
  have hdet : H.det * (gramComplex D).det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hHG
  have hG : (gramComplex D).det ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hdet
    exact zero_ne_one hdet
  exact LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hG

/-- Scalar extension is injective on the unchanged original integral labels. -/
private theorem chargeVector_injective (D : LatticeData) :
    Function.Injective (@chargeVector D) := by
  intro p q hpq
  funext i
  have hi : (p i : ℂ) = (q i : ℂ) := congrFun hpq i
  exact_mod_cast hi

@[simp] private theorem chargeVector_zero (D : LatticeData) :
    chargeVector (0 : Charge D) = 0 := by
  ext i
  simp [chargeVector]

/-- The ambient space still has the rank of the original lattice. -/
private theorem finrank_E (D : LatticeData) : Module.finrank ℂ (E D) = D.rank := by
  simp [E]

/-- Two orthogonal directions and a complex square root give an actual null
vector detected by any prescribed nonzero vector. Isotropic existence is a
conclusion here, not an input. -/
private theorem exists_null_vector_pairing_ne_zero (D : LatticeData)
    (hB : (gramBilin D).Nondegenerate) (hrank : 2 ≤ D.rank)
    (q : E D) (hq : q ≠ 0) :
    ∃ v : E D, g D v v = 0 ∧ g D v q ≠ 0 := by
  classical
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis
    (LinearMap.BilinForm.isSymm_iff.mp (gramBilin_isSymm D))
  have hb' : (gramBilin D).IsOrthoᵢ b := hb
  have hdiag : ∀ i, g D (b i) (b i) ≠ 0 := by
    intro i
    simpa only [gramBilin_apply] using
      LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hb' hB i
  have hex : ∃ i, g D (b i) q ≠ 0 := by
    by_contra! hz
    have hfunctional : pairing D q = 0 := by
      apply b.ext
      intro i
      change g D q (b i) = 0
      rw [g_symm]
      exact hz i
    apply hq
    apply hB.1 q
    intro x
    rw [gramBilin_apply]
    exact LinearMap.congr_fun hfunctional x
  obtain ⟨i, hi⟩ := hex
  have hdim : 2 ≤ Module.finrank ℂ (E D) := by
    rw [finrank_E]
    exact hrank
  let i0 : Fin (Module.finrank ℂ (E D)) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank ℂ (E D)) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  have hexj : ∃ j : Fin (Module.finrank ℂ (E D)), j ≠ i := by
    by_cases h : i0 = i
    · exact ⟨i1, fun hji => h01 (h.trans hji.symm)⟩
    · exact ⟨i0, h⟩
  obtain ⟨j, hji⟩ := hexj
  have hij : g D (b i) (b j) = 0 := by
    simpa only [gramBilin_apply] using hb hji.symm
  have hji' : g D (b j) (b i) = 0 := by
    rw [g_symm]
    exact hij
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(g D (b i) (b i)) / g D (b j) (b j)) zero_lt_two
  have hnull (c : ℂ)
      (hc : c ^ 2 = -(g D (b i) (b i)) / g D (b j) (b j)) :
      g D (b i + c • b j) (b i + c • b j) = 0 := by
    calc
      _ = g D (b i) (b i) + c ^ 2 * g D (b j) (b j) := by
        simp only [g_add_left, g_add_right, g_smul_left, g_smul_right, hij, hji']
        ring
      _ = 0 := by
        rw [hc, div_mul_cancel₀ _ (hdiag j), add_neg_cancel]
  have hzneg : (-z) ^ 2 = -(g D (b i) (b i)) / g D (b j) (b j) := by
    simpa only [neg_sq] using hz
  by_cases hplus : g D (b i + z • b j) q ≠ 0
  · exact ⟨b i + z • b j, hnull z hz, hplus⟩
  · have hplus0 : g D (b i + z • b j) q = 0 := not_ne_iff.mp hplus
    refine ⟨b i + (-z) • b j, hnull (-z) hzneg, ?_⟩
    intro hminus0
    apply hi
    have hsum : (2 : ℂ) * g D (b i) q = 0 := by
      calc
        _ = g D (b i + z • b j) q + g D (b i + (-z) • b j) q := by
          simp only [g_add_left, g_smul_left]
          ring
        _ = 0 := by rw [hplus0, hminus0, add_zero]
    exact (mul_eq_zero.mp hsum).resolve_left (by norm_num)

/-- Normalize a genuine nonzero null vector and remove the self-pairing of its
partner. Every field of the original NullFrame is proved by bilinear algebra. -/
private theorem exists_frame_with_plus (D : LatticeData)
    (hB : (gramBilin D).Nondegenerate) (v : E D)
    (hv : v ≠ 0) (hvv : g D v v = 0) :
    ∃ F : NullFrame D, F.ePlus = v := by
  classical
  have hex : ∃ u : E D, g D v u ≠ 0 := by
    by_contra! hz
    apply hv
    apply hB.1 v
    intro u
    simpa only [gramBilin_apply] using hz u
  obtain ⟨u, hu⟩ := hex
  let s : E D := (g D v u)⁻¹ • u
  have hvs : g D v s = 1 := by
    change g D v ((g D v u)⁻¹ • u) = 1
    rw [g_smul_right, inv_mul_cancel₀ hu]
  have hsv : g D s v = 1 := by rw [g_symm, hvs]
  let w : E D := s + (-(g D s s / 2)) • v
  have hvw : g D v w = 1 := by
    change g D v (s + (-(g D s s / 2)) • v) = 1
    rw [g_add_right, hvs, g_smul_right, hvv, mul_zero, add_zero]
  have hww : g D w w = 0 := by
    change g D (s + (-(g D s s / 2)) • v)
      (s + (-(g D s s / 2)) • v) = 0
    simp only [g_add_left, g_add_right, g_smul_left, g_smul_right, hvv, hvs, hsv]
    ring
  exact ⟨⟨v, w, hvv, hww, hvw⟩, rfl⟩

/-- For EACH nonzero original integral charge, a genuine null frame can be
chosen with nonzero pPlus. The zero charge is outside this theorem. -/
theorem exists_nullFrame_pPlus_ne_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hrank : 2 ≤ D.rank)
    (p : Charge D) (hp : p ≠ 0) :
    ∃ F : NullFrame D, F.pPlus p ≠ 0 := by
  have hpC : chargeVector p ≠ 0 := by
    intro hzero
    apply hp
    apply chargeVector_injective D
    simpa only [chargeVector_zero] using hzero
  have hB := gramBilin_nondegenerate D H hHG
  obtain ⟨v, hvv, hvp⟩ :=
    exists_null_vector_pairing_ne_zero D hB hrank (chargeVector p) hpC
  have hv : v ≠ 0 := by
    intro hzero
    apply hvp
    rw [hzero, g_symm, g_zero_right]
  obtain ⟨F, hF⟩ := exists_frame_with_plus D hB v hv hvv
  refine ⟨F, ?_⟩
  change g D F.ePlus (chargeVector p) ≠ 0
  rw [hF]
  exact hvp

end D5.S3.VertexAlgebra.LatticeNullFrameExistence

namespace D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame

open LatticeGeneratingFieldLocality
open LatticeNullFrameExistence

variable {D : LatticeData} (F : NullFrame D)

/-- The genuine transverse dimension comes from the already explicit frame
equivalence. It does not assume a nondegenerate complement or a basis of K. -/
theorem finrank_K_add_two : Module.finrank ℂ F.K + 2 = D.rank := by
  have h := F.frameEquiv.finrank_eq
  rw [finrank_E] at h
  have hdim : D.rank = 1 + (1 + Module.finrank ℂ F.K) := by
    simpa only [Module.finrank_prod, Module.finrank_self] using h
  omega

theorem finrank_K : Module.finrank ℂ F.K = D.rank - 2 := by
  have h := F.finrank_K_add_two
  omega

/-- A basis of the ACTUAL simultaneous orthogonal complement, indexed by the
derived rank minus two. finBasisOfFinrankEq reindexes Module.finBasis. -/
def transverseBasis : Module.Basis (Fin (D.rank - 2)) ℂ F.K :=
  Module.finBasisOfFinrankEq ℂ F.K F.finrank_K

end D5.S3.VertexAlgebra.LatticeLightConeCoordinates.NullFrame
