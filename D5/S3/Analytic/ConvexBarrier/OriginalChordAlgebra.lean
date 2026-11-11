/- GID: D5/S3/Analytic/ConvexBarrier/OriginalChordAlgebra
   generality: I
   mirror-B: D5/B/S3/Analytic/ConvexBarrier/OriginalChordAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.OriginalConeRecession

/-!
Exact endpoint coordinates and the algebraic dualQuadratic supplier.
The supplier is deduced by completing the square from original-cone
gradient control; it is NOT a dual Dikin or conjugate-barrier premise.
The scalar chord estimate is the known Zhang--Fu--Dai Lemma 3.2.
SOURCE ONLY, UNCOMPILED; no kernel/CI/official/novelty claim.
-/

open Set

namespace D5.S3.Analytic.ConvexBarrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact gradient and Hessian of the actual affine endpoint. -/
theorem IsLHSCB.original_chord_coordinates {ν : ℝ} {D B : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) {x : E} (hx : x ∈ D) (h : E) (δ : ℝ) :
    -fderiv ℝ F x (x+δ • h) = ν*(1-normalizedFirst ν F x h*δ) ∧
    diagonal 2 D F x (x+δ • h) =
      ν*((1-normalizedFirst ν F x h*δ)^2+projectiveHessian ν D F x h*δ^2) := by
  have hn : ν ≠ 0 := hF.parameter_pos.ne'
  constructor
  · simp only [map_add, map_smul, smul_eq_mul]
    rw [hF.euler hx]
    unfold normalizedFirst
    field_simp [hn]
    <;> ring
  · obtain ⟨hxx, hxh, hhx⟩ := hF.hessian_radial_coordinates hx h
    rw [hF.diagonal_two_eq_hessian hx]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hxx, hxh, hhx, ← hF.diagonal_two_eq_hessian hx h]
    unfold projectiveHessian normalizedFirst
    field_simp [hn]
    <;> ring

/-- Original-cone control at any closed endpoint. The endpoint need not
be interior or smooth, and delta may have either sign. -/
theorem IsLHSCB.original_chord_control {ν : ℝ} {D B K : Set E} {F : E → ℝ}
    (hF : IsLHSCB ν D B F) (hgeom : ConeRayGeometry D K)
    {x h : E} (hx : x ∈ D) (hq : 0 < projectiveHessian ν D F x h)
    {δ : ℝ} (hδ : δ ≠ 0) (hy : x+δ • h ∈ K) :
    let a := normalizedFirst ν F x h
    let q := projectiveHessian ν D F x h
    0 < 1-a*δ ∧ 0 < q*δ^2 ∧ q*δ^2 ≤ (ν-1)*(1-a*δ)^2 := by
  let A := 1-normalizedFirst ν F x h*δ
  let Q := projectiveHessian ν D F x h*δ^2
  change 0 < A ∧ 0 < Q ∧ Q ≤ (ν-1)*A^2
  have hQ : 0 < Q := mul_pos hq (sq_pos_of_ne_zero hδ)
  obtain ⟨hgrad, hmetric⟩ := hF.original_chord_coordinates hx h δ
  change -fderiv ℝ F x (x+δ • h) = ν*A at hgrad
  change diagonal 2 D F x (x+δ • h) = ν*(A^2+Q) at hmetric
  have hH : 0 < ν*(A^2+Q) := mul_pos hF.parameter_pos (by positivity)
  have hb := hF.original_cone_gradient_hessian hgeom hx hy
  rw [hmetric, hgrad] at hb
  have hνA : 0 < ν*A := lt_of_lt_of_le (Real.sqrt_pos.mpr hH) hb
  have hA : 0 < A := (mul_pos_iff_of_pos_left hF.parameter_pos).mp hνA
  have hsq : ν*(A^2+Q) ≤ (ν*A)^2 := by
    calc
      ν*(A^2+Q) = (Real.sqrt (ν*(A^2+Q)))^2 := (Real.sq_sqrt hH.le).symm
      _ ≤ (ν*A)^2 := by
        simpa only [pow_two] using mul_self_le_mul_self (Real.sqrt_nonneg _) hb
  have hm : ν*Q ≤ ν*((ν-1)*A^2) := by nlinarith [hsq]
  exact ⟨hA, hQ, le_of_mul_le_mul_left hm hF.parameter_pos⟩

/-- Complete-square identity. This is pure algebra for all real t and
does not refer to a dual domain, support covector, or inverse Hessian. -/
theorem dualQuadratic_complete_square {ν A Q : ℝ} (hν : 0 < ν) (hQ : 0 < Q)
    (t : ℝ) :
    dualQuadratic ν A Q t =
      ((A^2+Q)*t-ν*Q)^2/(ν*Q*(A^2+Q)) + ν*A^2/(A^2+Q) := by
  have hS : 0 < A^2+Q := by positivity
  unfold dualQuadratic
  field_simp [hν.ne', hQ.ne', hS.ne']
  <;> ring

/-- The missing dualQuadratic input is proved from the original-gradient
bound Q <= (nu-1) A^2. No dual-Dikin property is assumed or asserted. -/
theorem dualQuadratic_from_original_control {ν A Q : ℝ}
    (hν : 0 < ν) (hQ : 0 < Q) (hcontrol : Q ≤ (ν-1)*A^2) :
    ∀ t : ℝ, 1 ≤ dualQuadratic ν A Q t := by
  have hS : 0 < A^2+Q := by positivity
  have hmin : 1 ≤ ν*A^2/(A^2+Q) := (le_div_iff₀ hS).mpr (by nlinarith)
  intro t
  rw [dualQuadratic_complete_square hν hQ]
  have hsquare : 0 ≤ ((A^2+Q)*t-ν*Q)^2/(ν*Q*(A^2+Q)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith

/-- A conclusion record, not an assumed supplier. All entries are produced
in scalar_original_boundary_chord from an actual barrier and endpoint. -/
structure OriginalChordBounds (ν a q δ : ℝ) : Prop where
  projective_pos : 0 < q
  first_factor_pos : 0 < 1-a*δ
  metric_factor_pos : 0 < q*δ^2
  gradient_side : q*δ^2 ≤ (ν-1)*(1-a*δ)^2
  primal_side : (1-a*δ)^2 ≤ (ν-1)*(q*δ^2)
  parameter_ge_two : 2 ≤ ν
  rho_ge_one : 1 ≤ ν-1
  sqrt_rho_ge_one : 1 ≤ Real.sqrt (ν-1)
  normalized : 1/Real.sqrt (ν-1) ≤ (1-a*δ)/Real.sqrt (q*δ^2) ∧
    (1-a*δ)/Real.sqrt (q*δ^2) ≤ Real.sqrt (ν-1)

/-- Finish the existing scalar algebra after the original-side control.
The dual input to dikin_quadratic_consequences is derived above. -/
theorem originalChordBounds_of_control {ν a q δ : ℝ} (hν : 0 < ν)
    (hq : 0 < q) (hA : 0 < 1-a*δ) (hQ : 0 < q*δ^2)
    (hcontrol : q*δ^2 ≤ (ν-1)*(1-a*δ)^2)
    (hprimal : ∀ t : ℝ, 0 < t → 1 ≤ primalQuadratic ν (1-a*δ) (q*δ^2) t) :
    OriginalChordBounds ν a q δ := by
  have hdual := dualQuadratic_from_original_control hν hQ hcontrol
  obtain ⟨hp, hd, hν2⟩ := dikin_quadratic_consequences hν hA hQ
    hprimal (fun t _ => hdual t)
  have hρ1 : 1 ≤ ν-1 := by linarith
  have hρ : 0 < ν-1 := lt_of_lt_of_le zero_lt_one hρ1
  have hs : 0 < Real.sqrt (ν-1) := Real.sqrt_pos.mpr hρ
  have hs2 := Real.sq_sqrt hρ.le
  have hs1 : 1 ≤ Real.sqrt (ν-1) := by
    apply le_of_sq_le_sq _ hs.le
    nlinarith
  have hnorm := normalized_chord_bounds hA hQ hs
    (by nlinarith [hp]) (by nlinarith [hd])
  exact ⟨hq, hA, hQ, hd, hp, hν2, hρ1, hs1, hnorm⟩

end D5.S3.Analytic.ConvexBarrier
