/- GID: D5/S3/Quantum/Hiai/GeometricTraceConvexity
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/GeometricTraceConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint convexity of Hiai's original spectral geometric trace on the SPD rectangle. -/

import D5.S3.Quantum.Hiai.InverseGeometricIdentification
import D5.S3.Quantum.Hiai.CarlenLiebConvexity

noncomputable section
namespace D5.S3.Quantum.Hiai.GeometricTraceConvexity

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix InverseMeanVariational PsiMeanTraceConcavity GeneralizedPerspectiveFunction
variable {d : Type*} [Fintype d] [DecidableEq d]
local instance : Pow (Matrix d d ℂ) ℝ := ⟨CFC.rpow⟩

/-- Hiai (2.1)/(2.2): the first powered input is the geometric-mean base. -/
def geometricTrace (α p : ℝ) (A B : Matrix d d ℂ) : ℝ :=
  tracePower (1 / p) (geometricMean α (A ^ p) (B ^ p))

/-- The fixed congruence objective used by the inverse variational formula. -/
def variationalObjective (p θ : ℝ) (Z A B : Matrix d d ℂ) : ℝ :=
  2 * tracePower (1 / (2 * p)) (Zᴴ * (B ^ (2 * p)) * Z) - psi p θ Z A B

private lemma mean_posDef {X Y : Matrix d d ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    (θ : ℝ) : (geometricMean θ X Y).PosDef := by
  have hI := hX.isStrictlyPositive.rpow X (-1 / 2)
  have hS := hX.isStrictlyPositive.rpow X (1 / 2)
  have hinner : (X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)).PosDef := by
    simpa only [hI.isSelfAdjoint.star_eq] using
      (hI.isUnit.posDef_star_left_conjugate_iff (x := Y)).mpr hY
  have hpower := (hinner.isStrictlyPositive.rpow _ θ).posDef
  simpa only [geometricMean, hS.isSelfAdjoint.star_eq] using
    (hS.isUnit.posDef_star_right_conjugate_iff
      (x := (X ^ (-1 / 2 : ℝ) * Y * X ^ (-1 / 2 : ℝ)) ^ θ)).mpr hpower

private lemma original_mean_inverse {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (α p : ℝ) :
    geometricMean α (A ^ p) (B ^ p) =
      B ^ p * (geometricMean (α - 1) (B ^ p) (A ^ p))⁻¹ * B ^ p := by
  have hAp := (hA.isStrictlyPositive.rpow A p).posDef
  have hBp := (hB.isStrictlyPositive.rpow B p).posDef
  rw [(InverseGeometricIdentification.geometricMean_identification hAp hBp α).1,
    show 1 - α = -(α - 1) by ring,
    (InverseGeometricIdentification.geometricMean_identification hBp hAp (α - 1)).2,
    Matrix.nonsing_inv_eq_ringInverse]

private lemma objective_identification {A B : Matrix d d ℂ} (hB : B.PosDef)
    (p θ : ℝ) (Z : Matrix d d ℂ) :
    objective (1 / p) (B ^ p) (geometricMean θ (B ^ p) (A ^ p)) Z =
      variationalObjective p θ Z A B := by
  have hsquare : B ^ p * B ^ p = B ^ (2 * p) := by
    rw [← CFC.rpow_add hB.isUnit]
    congr 1
    ring
  have hexponent : (1 / p) / 2 = 1 / (2 * p) := by field_simp
  simp only [objective, variationalObjective, psi, hsquare, hexponent]

private lemma objective_jointly_convex {p θ : ℝ}
    (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (Z : Matrix d d ℂ) (hZ : IsUnit Z) :
    JointlyConvexOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (variationalObjective p θ Z) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hC := CarlenLiebConvexity.fixed_congruence_trace_convex
    (a := 2 * p) ⟨by linarith [hp.1], by linarith [hp.2]⟩ Z hZ
  have hPsi := psi_jointly_concave hp0 hp.2 hθ Z hZ
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hc := hC.2 hB₀ hB₁ (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  have hpsi := hPsi hA₀ hA₁ hB₀ hB₁ ht0 ht1
  simp only [smul_eq_mul] at hc hpsi ⊢
  unfold variationalObjective
  linarith

private lemma variational_formula {A B : Matrix d d ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (α : ℝ) {p : ℝ} (hp : 0 < p) :
    ∃ Z₀ : Matrix d d ℂ, IsUnit Z₀ ∧
      variationalObjective p (α - 1) Z₀ A B = geometricTrace α p A B ∧
      ∀ Z : Matrix d d ℂ,
        variationalObjective p (α - 1) Z A B ≤ geometricTrace α p A B := by
  have hAp := (hA.isStrictlyPositive.rpow A p).posDef
  have hBp := (hB.isStrictlyPositive.rpow B p).posDef
  obtain ⟨Z₀, hZ₀, _, heq, hbound⟩ :=
    variational_bound_and_attainment hBp (mean_posDef hBp hAp (α - 1))
      (one_div_pos.mpr hp)
  have htarget : tracePower (1 / p)
      (B ^ p * (geometricMean (α - 1) (B ^ p) (A ^ p))⁻¹ * B ^ p) =
      geometricTrace α p A B := by
    rw [geometricTrace, original_mean_inverse hA hB α p]
  rw [htarget, objective_identification hB p] at heq
  refine ⟨Z₀, hZ₀, heq, fun Z => ?_⟩
  simpa only [htarget, objective_identification hB p] using hbound Z

/-- Joint convexity of the original spectral functional for every finite complex matrix
dimension, including empty, all noncommuting SPD inputs, and both parameter boundaries.
Only the attained optimizer at the mixed point is chosen. -/
theorem geometric_trace_jointly_convex {α p : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2) (hp : p ∈ Set.Icc (1 / 2 : ℝ) 1) :
    JointlyConvexOn {A : Matrix d d ℂ | A.PosDef} {B : Matrix d d ℂ | B.PosDef}
      (geometricTrace α p) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have hθ : α - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hα.1], by linarith [hα.2]⟩
  have hdomain := (CarlenLiebConvexity.fixed_congruence_trace_convex
    (d := d) (a := 1) (by norm_num) 1 isUnit_one).1
  intro A₀ A₁ B₀ B₁ t hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hAm := hdomain hA₀ hA₁ (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  have hBm := hdomain hB₀ hB₁ (sub_nonneg.mpr ht1) ht0 (by ring : 1 - t + t = 1)
  obtain ⟨Zm, hZm, heqm, _⟩ := variational_formula hAm hBm α hp0
  have hc := objective_jointly_convex hp hθ Zm hZm hA₀ hA₁ hB₀ hB₁ ht0 ht1
  have hb₀ := (variational_formula hA₀ hB₀ α hp0).elim (fun _ h => h.2.2 Zm)
  have hb₁ := (variational_formula hA₁ hB₁ α hp0).elim (fun _ h => h.2.2 Zm)
  rw [heqm] at hc
  simp only [smul_eq_mul] at hc ⊢
  exact hc.trans (add_le_add
    (mul_le_mul_of_nonneg_left hb₀ (sub_nonneg.mpr ht1))
    (mul_le_mul_of_nonneg_left hb₁ ht0))

#print axioms geometric_trace_jointly_convex
end D5.S3.Quantum.Hiai.GeometricTraceConvexity
