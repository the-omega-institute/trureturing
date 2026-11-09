/- GID: D5/S3/Geometry/PowerCone/OriginalConeChords
   generality: I
   mirror-B: D5/B/S3/Geometry/PowerCone/OriginalConeChords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Geometry.PowerCone.ConvexGeometry
import D5.S3.Analytic.ConvexBarrier.OriginalChordAlgebra

/-!
Both actual scalar boundary chord bounds, obtained entirely on the
original power cone. No conjugate, dual Dikin, assumed support covector,
fullCurve, scalar lower/optimality, or domain replacement is a hypothesis.
Nonradiality is the usual explicit condition h != t*x for every real t.

Attribution: the scalar chord estimate and scalar optimum mechanism are
due to Rui-Jin Zhang, Wenhao Fu and Yu-Hong Dai, arXiv:2611.06404v1,
Lemma 3.2 and Theorem 3.5. The direct recession facts are standard
self-concordance mathematics; the supplied Pro derivation was fallible
mathematical data, not a validation vote or Lean verification receipt.

This file supplies the chord foundation only. It does not construct the
minimizer/envelope Curve or prove ScalarLowerClaim or vector optimality.
Coordinate-zero faces remain in coneBoundary. All final theorems here
are scalar (V=R), with no complex or vector optimality scope added.
SOURCE ONLY, UNCOMPILED. No kernel/requiredCI/official/novelty claim.
-/

open Set
open D5.S3.Analytic.ConvexBarrier

namespace D5.S3.Geometry.PowerCone

/-- The gradient sign for every actual closed-cone direction. -/
theorem scalar_original_gradient_nonpos {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (interior (closedCone c)) (frontier (closedCone c)) F)
    {x y : Point ℝ} (hx : x ∈ interior (closedCone c)) (hy : y ∈ closedCone c) :
    fderiv ℝ F x y ≤ 0 := by
  rw [← coneInterior_eq_interior hc.le hc1.le,
    ← coneBoundary_eq_frontier hc.le hc1.le] at hF
  rw [← coneInterior_eq_interior hc.le hc1.le] at hx
  exact hF.gradient_nonpos_cone (actual_powerCone_rayGeometry hc hc1) hx hy

/-- The direct gradient/Hessian theorem on the actual original scalar
closed cone, including y=0 and every non-interior face direction. -/
theorem scalar_original_gradient_hessian {c ν : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (interior (closedCone c)) (frontier (closedCone c)) F)
    {x y : Point ℝ} (hx : x ∈ interior (closedCone c)) (hy : y ∈ closedCone c) :
    Real.sqrt (diagonal 2 (interior (closedCone c)) F x y) ≤ -fderiv ℝ F x y := by
  rw [← coneInterior_eq_interior hc.le hc1.le,
    ← coneBoundary_eq_frontier hc.le hc1.le] at hF
  rw [← coneInterior_eq_interior hc.le hc1.le] at hx ⊢
  exact hF.original_cone_gradient_hessian (actual_powerCone_rayGeometry hc hc1) hx hy

/-- One actual scalar boundary endpoint, with either sign of delta.
The projective Hessian is proved positive from the actual radial
identities. Both quadratic bounds and nu>=2 are conclusions. -/
theorem scalar_original_boundary_chord {c ν δ : ℝ}
    (hc : 0 < c) (hc1 : c < 1) {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {x h : Point ℝ} (hx : x ∈ coneInterior c)
    (hnonradial : ∀ t : ℝ, h ≠ t • x) (hδ : δ ≠ 0)
    (hy : x+δ • h ∈ coneBoundary c) :
    OriginalChordBounds ν (normalizedFirst ν F x h)
      (projectiveHessian ν (coneInterior c) F x h) δ := by
  have hq := hF.projectiveHessian_pos hx h hnonradial
  obtain ⟨hA, hQ, hcontrol⟩ := hF.original_chord_control
    (actual_powerCone_rayGeometry hc hc1) hx hq hδ hy.1
  have hprimal : ∀ t : ℝ, 0 < t →
      1 ≤ primalQuadratic ν (1-normalizedFirst ν F x h*δ)
        (projectiveHessian ν (coneInterior c) F x h*δ^2) t := by
    intro t ht
    have hout : t • (x+δ • h) ∉ coneInterior c := (coneBoundary_posScale ht hy).2
    have hh := hF.primal_exclusion (coneInterior_frontier_subset hc.le hc1.le) hx hout
    rwa [hF.primal_chord_polynomial hx h δ t] at hh
  exact originalChordBounds_of_control hF.parameter_pos hq hA hQ hcontrol hprimal

/-- BOTH signs on the original explicit scalar boundary. The negative
endpoint uses signed delta=-deltaMinus, so its A is 1+a*deltaMinus. -/
theorem scalar_original_chord_bounds {c ν δminus δplus : ℝ}
    (hc : 0 < c) (hc1 : c < 1) {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {x h : Point ℝ} (hx : x ∈ coneInterior c)
    (hnonradial : ∀ t : ℝ, h ≠ t • x)
    (hδminus : 0 < δminus) (hδplus : 0 < δplus)
    (hminus : x-δminus • h ∈ coneBoundary c)
    (hplus : x+δplus • h ∈ coneBoundary c) :
    let a := normalizedFirst ν F x h
    let q := projectiveHessian ν (coneInterior c) F x h
    OriginalChordBounds ν a q (-δminus) ∧ OriginalChordBounds ν a q δplus := by
  refine ⟨scalar_original_boundary_chord hc hc1 hF hx hnonradial
    (neg_ne_zero.mpr hδminus.ne') ?_,
    scalar_original_boundary_chord hc hc1 hF hx hnonradial hδplus.ne' hplus⟩
  simpa only [sub_eq_add_neg, neg_smul] using hminus

/-- Same theorem with the actual topological interior and frontier.
No assumed convex/ray/domain replacement survives this interface. -/
theorem actual_scalar_original_chord_bounds {c ν δminus δplus : ℝ}
    (hc : 0 < c) (hc1 : c < 1) {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (interior (closedCone c)) (frontier (closedCone c)) F)
    {x h : Point ℝ} (hx : x ∈ interior (closedCone c))
    (hnonradial : ∀ t : ℝ, h ≠ t • x)
    (hδminus : 0 < δminus) (hδplus : 0 < δplus)
    (hminus : x-δminus • h ∈ frontier (closedCone c))
    (hplus : x+δplus • h ∈ frontier (closedCone c)) :
    let a := normalizedFirst ν F x h
    let q := projectiveHessian ν (interior (closedCone c)) F x h
    OriginalChordBounds ν a q (-δminus) ∧ OriginalChordBounds ν a q δplus := by
  rw [← coneInterior_eq_interior hc.le hc1.le,
    ← coneBoundary_eq_frontier hc.le hc1.le] at hF
  rw [← coneInterior_eq_interior hc.le hc1.le] at hx ⊢
  rw [← coneBoundary_eq_frontier hc.le hc1.le] at hminus hplus
  exact scalar_original_chord_bounds hc hc1 hF hx hnonradial hδminus hδplus hminus hplus

/-- The familiar coefficient form of BOTH normalized scalar chords,
matching (3.4)--(3.5), supplied by actual barriers and endpoints. -/
theorem scalar_original_normalized_chords {c ν δminus δplus : ℝ}
    (hc : 0 < c) (hc1 : c < 1) {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {x h : Point ℝ} (hx : x ∈ coneInterior c)
    (hnonradial : ∀ t : ℝ, h ≠ t • x)
    (hδminus : 0 < δminus) (hδplus : 0 < δplus)
    (hminus : x-δminus • h ∈ coneBoundary c)
    (hplus : x+δplus • h ∈ coneBoundary c) :
    let a := normalizedFirst ν F x h
    let q := projectiveHessian ν (coneInterior c) F x h
    let s := Real.sqrt (ν-1)
    0 < q ∧ 2 ≤ ν ∧ 1 ≤ ν-1 ∧ 1 ≤ s ∧
      (1/s ≤ (a+1/δminus)/Real.sqrt q ∧ (a+1/δminus)/Real.sqrt q ≤ s) ∧
      (1/s ≤ (-a+1/δplus)/Real.sqrt q ∧ (-a+1/δplus)/Real.sqrt q ≤ s) := by
  let a := normalizedFirst ν F x h
  let q := projectiveHessian ν (coneInterior c) F x h
  obtain ⟨hm, hp⟩ := scalar_original_chord_bounds hc hc1 hF hx hnonradial
    hδminus hδplus hminus hplus
  have hq : 0 < q := hm.projective_pos
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hminus_eq : (1-a*(-δminus))/Real.sqrt (q*(-δminus)^2) =
      (a+1/δminus)/Real.sqrt q := by
    rw [neg_sq, Real.sqrt_mul hq.le, Real.sqrt_sq hδminus.le]
    field_simp [hsqrt, hδminus.ne']
    <;> ring
  have hplus_eq : (1-a*δplus)/Real.sqrt (q*δplus^2) =
      (-a+1/δplus)/Real.sqrt q := by
    rw [Real.sqrt_mul hq.le, Real.sqrt_sq hδplus.le]
    field_simp [hsqrt, hδplus.ne']
    <;> ring
  refine ⟨hq, hm.parameter_ge_two, hm.rho_ge_one, hm.sqrt_rho_ge_one, ?_, ?_⟩
  · have hmn := hm.normalized
    rw [hminus_eq] at hmn
    exact hmn
  · have hpn := hp.normalized
    rw [hplus_eq] at hpn
    exact hpn

end D5.S3.Geometry.PowerCone
