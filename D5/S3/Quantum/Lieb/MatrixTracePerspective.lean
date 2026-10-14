/- GID: D5/S3/Quantum/Lieb/MatrixTracePerspective
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/MatrixTracePerspective
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Matrix trace perspective convexity with all adjoints and finite dimensions. -/

import D5.S3.Quantum.Lieb.TracePerspectiveConvexity
import Mathlib.Analysis.Matrix.Order

noncomputable section
namespace D5.S3.Quantum.Lieb.MatrixTracePerspective
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix GeneralizedPerspectiveFunction LownerHeinzTheorem LiebAndoTrace
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

private abbrev transport : Matrix d d ℂ ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)

private lemma transport_pd {X : Matrix d d ℂ} (hX : X.PosDef) :
    transport X ∈ pdSet (ℋ := EuclideanSpace ℂ d) := by
  have hpos : IsStrictlyPositive (transport X) :=
    (hX.isUnit.map transport).isStrictlyPositive (map_nonneg transport hX.posSemidef.nonneg)
  exact ⟨IsSelfAdjoint.of_nonneg hpos.nonneg, fun _ hx => hpos.spectrum_pos hx⟩

private lemma transport_power {X : Matrix d d ℂ} (hX : X.PosDef) (p : ℝ) :
    transport (X ^ p) = (transport X) ^ p := by
  have hpos := map_nonneg transport hX.posSemidef.nonneg
  rw [CFC.rpow_eq_cfc_real hX.posSemidef.nonneg, CFC.rpow_eq_cfc_real hpos]
  exact StarAlgHomClass.map_cfc transport (fun x : ℝ => x ^ p) X
    (by intro x hx; exact (Real.continuousAt_rpow_const x p
      (Or.inl (hX.isStrictlyPositive.spectrum_pos hx).ne')).continuousWithinAt)
    (StarAlgEquiv.isometry (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ))).continuous
    hX.isHermitian (IsSelfAdjoint.of_nonneg hpos)

private lemma transport_trace (X : Matrix d d ℂ) :
    traceRe (ℋ := EuclideanSpace ℂ d) (transport X) = (Matrix.trace X).re := by
  unfold traceRe
  change (LinearMap.trace ℂ (EuclideanSpace ℂ d) (Matrix.toEuclideanLin X)).re = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

private lemma transport_lieb {a : ℝ} (Z X W : Matrix d d ℂ)
    (hX : X.PosDef) (hW : W.PosDef) :
    liebTraceMap a (star (transport Z)) (transport X) (transport W) =
      (Matrix.trace (Zᴴ * (X ^ a) * Z * (W ^ (1 - a)))).re := by
  unfold liebTraceMap
  rw [star_star, ← transport_power hX, ← transport_power hW,
    ← map_star transport Z, ← map_mul transport, ← map_mul transport, ← map_mul transport,
    transport_trace, Matrix.trace_mul_comm]
  simp only [mul_assoc]
  rfl

/-- Matrix form of Ando trace perspective convexity, preserving arbitrary nonselfadjoint Z. -/
theorem trace_perspective_jointly_convex {a : ℝ} (ha : a ∈ Set.Icc 1 2)
    (Z : Matrix d d ℂ) :
    JointlyConvexOn {X : Matrix d d ℂ | X.PosDef} {W : Matrix d d ℂ | W.PosDef}
      (fun X W => (Matrix.trace (Zᴴ * (X ^ a) * Z * (W ^ (1 - a)))).re) := by
  classical
  cases isEmpty_or_nonempty d with
  | inl hd =>
    letI := hd
    intro X₁ X₂ W₁ W₂ t _ _ _ _ _ _
    simp [Matrix.trace]
  | inr hd =>
    letI := hd
    intro X₁ X₂ W₁ W₂ t hX₁ hX₂ hW₁ hW₂ ht0 ht1
    have hXm : ((1 - t) • X₁ + t • X₂).PosDef := by
      by_cases ht : t = 1
      · simp only [ht, sub_self, zero_smul, one_smul, zero_add]; exact hX₂
      · have ht' : t < 1 := lt_of_le_of_ne ht1 ht
        exact ((hX₁.isStrictlyPositive.smul (sub_pos.mpr ht')).add_nonneg
          (smul_nonneg ht0 hX₂.posSemidef.nonneg)).posDef
    have hWm : ((1 - t) • W₁ + t • W₂).PosDef := by
      by_cases ht : t = 1
      · simp only [ht, sub_self, zero_smul, one_smul, zero_add]; exact hW₂
      · have ht' : t < 1 := lt_of_le_of_ne ht1 ht
        exact ((hW₁.isStrictlyPositive.smul (sub_pos.mpr ht')).add_nonneg
          (smul_nonneg ht0 hW₂.posSemidef.nonneg)).posDef
    have hh := TracePerspectiveConvexity.trace_perspective_jointly_convex ha (star (transport Z))
      (transport_pd hX₁) (transport_pd hX₂) (transport_pd hW₁) (transport_pd hW₂) ht0 ht1
    have hmX : (1 - t) • transport X₁ + t • transport X₂ =
        transport ((1 - t) • X₁ + t • X₂) := by
          simp only [map_add, ← Complex.coe_smul, map_smul]
    have hmW : (1 - t) • transport W₁ + t • transport W₂ =
        transport ((1 - t) • W₁ + t • W₂) := by
          simp only [map_add, ← Complex.coe_smul, map_smul]
    rw [hmX, hmW, transport_lieb _ _ _ hXm hWm,
      transport_lieb _ _ _ hX₁ hW₁, transport_lieb _ _ _ hX₂ hW₂] at hh
    exact hh

end D5.S3.Quantum.Lieb.MatrixTracePerspective
