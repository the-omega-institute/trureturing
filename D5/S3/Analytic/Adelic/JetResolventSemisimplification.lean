/- GID: D5/S3/Analytic/Adelic/JetResolventSemisimplification
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/JetResolventSemisimplification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Nilpotent jet trace and log derivative reduce to one weighted pole. -/

import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/- Library-search audit trail (2026-08-30):
   * Exact-name and statement-shape searches for jet resolvents, nilpotent
     pencils, trace resolvents, and logarithmic determinant derivatives found
     no frozen D5 theorem with either boxed identity.
   * Body-shape searches for a lower shift with entry test
     `i.val = j.val + 1` and for `(s - rho) • 1 - N` found no canonical D5
     definitions. The two source objects are therefore constructed below.
   * `ToroidalJetDepth` concerns the first nonzero derivative layer of a
     twisted xi reading; it supplies no matrix-jet carrier or pencil primitive.
   * Pinned Mathlib supplies `Matrix.det_of_lowerTriangular`, preservation of
     block triangularity by inverse, `Matrix.mul_nonsing_inv`, and
     `logDeriv_fun_pow`. These are applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.JetResolventSemisimplification

open scoped BigOperators Matrix

/-- The source lower nilpotent shift on a finite jet. -/
def nilpotentJetShift (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if i.1 = j.1 + 1 then 1 else 0

/-- The affine spectral pencil of the lower nilpotent jet shift. -/
def jetPencil (m : ℕ) (rho s : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (s - rho) • (1 : Matrix (Fin m) (Fin m) ℂ) - nilpotentJetShift m

private theorem jetPencil_lowerTriangular (m : ℕ) (rho s : ℂ) :
    (jetPencil m rho s).BlockTriangular
      (OrderDual.toDual : Fin m → OrderDual (Fin m)) := by
  intro i j hji
  have hij : i < j := by simpa using hji
  simp [jetPencil, nilpotentJetShift, Matrix.smul_apply, hij.ne]
  omega

private theorem jetPencil_diagonal (m : ℕ) (rho s : ℂ) (i : Fin m) :
    jetPencil m rho s i i = s - rho := by
  simp [jetPencil, nilpotentJetShift, Matrix.smul_apply]

private theorem jetPencil_det (m : ℕ) (rho s : ℂ) :
    (jetPencil m rho s).det = (s - rho) ^ m := by
  rw [Matrix.det_of_lowerTriangular (jetPencil m rho s)
    (jetPencil_lowerTriangular m rho s)]
  simp [jetPencil_diagonal]

private theorem lowerTriangular_nonsing_inv_diagonal
    {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ)
    (hM : M.BlockTriangular (OrderDual.toDual : Fin m → OrderDual (Fin m)))
    (hdet : IsUnit M.det) (i : Fin m) :
    M⁻¹ i i = (M i i)⁻¹ := by
  letI : Invertible M := M.invertibleOfIsUnitDet hdet
  have hInv : M⁻¹.BlockTriangular
      (OrderDual.toDual : Fin m → OrderDual (Fin m)) :=
    Matrix.blockTriangular_inv_of_blockTriangular hM
  have hproduct := congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A i i)
    (M.mul_nonsing_inv hdet)
  simp only [Matrix.mul_apply, Matrix.one_apply, if_pos] at hproduct
  rw [Finset.sum_eq_single i] at hproduct
  · exact eq_inv_of_mul_eq_one_right hproduct
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [hInv (by simpa using hji), mul_zero]
    · rw [hM (by simpa using hij), zero_mul]
  · simp

private theorem jetPencil_nonsing_inv_diagonal (m : ℕ) (rho s : ℂ)
    (hs : s ≠ rho) (i : Fin m) :
    (jetPencil m rho s)⁻¹ i i = (s - rho)⁻¹ := by
  have hunit : IsUnit (jetPencil m rho s).det := by
    rw [jetPencil_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero m (sub_ne_zero.mpr hs))
  rw [lowerTriangular_nonsing_inv_diagonal (jetPencil m rho s)
    (jetPencil_lowerTriangular m rho s) hunit i, jetPencil_diagonal]

private theorem jetPencil_trace_nonsing_inv (m : ℕ) (rho s : ℂ)
    (hs : s ≠ rho) :
    Matrix.trace (jetPencil m rho s)⁻¹ = (m : ℂ) / (s - rho) := by
  change (∑ i, (jetPencil m rho s)⁻¹ i i) = _
  simp_rw [jetPencil_nonsing_inv_diagonal m rho s hs]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp [div_eq_mul_inv]

private theorem jetPencil_logDeriv_det (m : ℕ) (rho s : ℂ) :
    logDeriv (fun z => (jetPencil m rho z).det) s = (m : ℂ) / (s - rho) := by
  have hdet : (fun z => (jetPencil m rho z).det) = fun z => (z - rho) ^ m := by
    funext z
    exact jetPencil_det m rho z
  rw [hdet, logDeriv_fun_pow (by fun_prop)]
  simp [logDeriv_apply, div_eq_mul_inv]

/--
The trace resolvent and the logarithmic determinant derivative of a length-`m`
nilpotent jet both reduce to the simple pole of weight `m`. The final public
conjunct exposes the jet-to-mass identification between the two channels.
-/
theorem jet_resolvent_semisimplification (m : ℕ) (rho s : ℂ) (hs : s ≠ rho) :
    Matrix.trace (jetPencil m rho s)⁻¹ = (m : ℂ) / (s - rho) ∧
      logDeriv (fun z => (jetPencil m rho z).det) s = (m : ℂ) / (s - rho) ∧
      Matrix.trace (jetPencil m rho s)⁻¹ =
        logDeriv (fun z => (jetPencil m rho z).det) s := by
  have htrace := jetPencil_trace_nonsing_inv m rho s hs
  have hlog := jetPencil_logDeriv_det m rho s
  exact ⟨htrace, hlog, htrace.trans hlog.symm⟩

#print axioms jet_resolvent_semisimplification

end D5.S3.Analytic.Adelic.JetResolventSemisimplification
