/- GID: D5/S3/Quantum/Hiai/CarlenLiebConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/CarlenLiebConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed invertible congruence trace power convexity by explicit optimizer interpolation. -/

import D5.S3.Quantum.Lieb.MatrixTracePerspective
import D5.S3.Quantum.Hiai.ReverseTraceYoung

/- Classical Carlen-Lieb convexity, arXiv:0710.4167, Theorem 1.1 at q=1.
   This source consumes the dimension-independent Jensen supplier and the
   tracial Young minimum, without a target-convexity hypothesis. -/

noncomputable section
namespace D5.S3.Quantum.Hiai.CarlenLiebConvexity
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix InverseMeanVariational
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

private lemma posDef_mix {X Y : Matrix d d ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ((1 - t) • X + t • Y).PosDef := by
  by_cases ht : t = 1
  · simp only [ht, sub_self, zero_smul, one_smul, zero_add]; exact hY
  · have ht' : t < 1 := lt_of_le_of_ne ht1 ht
    exact ((hX.isStrictlyPositive.smul (sub_pos.mpr ht')).add_nonneg
      (smul_nonneg ht0 hY.posSemidef.nonneg)).posDef

private lemma congruence_posDef {X Z : Matrix d d ℂ} (hX : X.PosDef) (hZ : IsUnit Z)
    (a : ℝ) : (Zᴴ * (X ^ a) * Z).PosDef := by
  exact ((hX.isStrictlyPositive.rpow X a).posDef).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.mpr hZ)

/-- The exact Carlen-Lieb fixed-congruence trace functional is convex for all 1 ≤ a ≤ 2.
The fixed invertible Z may be nonselfadjoint and finite dimension may be empty. -/
theorem fixed_congruence_trace_convex {a : ℝ} (ha : a ∈ Set.Icc 1 2)
    (Z : Matrix d d ℂ) (hZ : IsUnit Z) :
    ConvexOn ℝ {X : Matrix d d ℂ | X.PosDef}
      (fun X => tracePower (1 / a) (Zᴴ * (X ^ a) * Z)) := by
  have ha0 : 0 < a := by linarith [ha.1]
  have hc : Convex ℝ {X : Matrix d d ℂ | X.PosDef} := by
    intro X hX Y hY s t hs ht hst
    change (s • X + t • Y).PosDef
    have hX' := posDef_mix hX hY ht (by linarith)
    simpa only [show 1 - t = s by linarith] using hX'
  refine ⟨hc, ?_⟩
  intro X hX Y hY s t hs ht hst
  have ht1 : t ≤ 1 := by linarith
  have hst' : 1 - t = s := by linarith
  let M₁ := Zᴴ * (X ^ a) * Z
  let M₂ := Zᴴ * (Y ^ a) * Z
  obtain ⟨W₁, hW₁, _, heq₁, _⟩ :=
    ReverseTraceYoung.minimum_and_attainment (congruence_posDef hX hZ a) ha.1
  obtain ⟨W₂, hW₂, _, heq₂, _⟩ :=
    ReverseTraceYoung.minimum_and_attainment (congruence_posDef hY hZ a) ha.1
  have hW : (s • W₁ + t • W₂).PosDef := by
    simpa only [hst'] using posDef_mix hW₁ hW₂ ht ht1
  have hXY : (s • X + t • Y).PosDef := hc hX hY hs ht hst
  have hlo := ReverseTraceYoung.reverse_trace_young
    (congruence_posDef hXY hZ a) hW ha.1
  have hh := D5.S3.Quantum.Lieb.MatrixTracePerspective.trace_perspective_jointly_convex ha Z
    hX hY hW₁ hW₂ ht ht1
  rw [hst'] at hh
  have htrace : (Matrix.trace (s • W₁ + t • W₂)).re =
      s * (Matrix.trace W₁).re + t * (Matrix.trace W₂).re := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hobj : ReverseTraceYoung.objective a (Zᴴ * ((s • X + t • Y) ^ a) * Z)
      (s • W₁ + t • W₂) ≤
      s * ReverseTraceYoung.objective a M₁ W₁ +
        t * ReverseTraceYoung.objective a M₂ W₂ := by
    unfold ReverseTraceYoung.objective
    dsimp [M₁, M₂]
    rw [htrace]
    change (Matrix.trace (Zᴴ * ((s • X + t • Y) ^ a) * Z *
      ((s • W₁ + t • W₂) ^ (1 - a)))).re +
      (a - 1) * (s * (Matrix.trace W₁).re + t * (Matrix.trace W₂).re) ≤ _
    simp only [smul_eq_mul] at hh
    nlinarith [hh]
  have hcombined := hlo.trans hobj
  rw [heq₁, heq₂] at hcombined
  simp only [smul_eq_mul]
  nlinarith

#print axioms fixed_congruence_trace_convex
end D5.S3.Quantum.Hiai.CarlenLiebConvexity
