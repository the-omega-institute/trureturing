/- GID: D5/S3/Quantum/Matrix/HsfIdentityCubicCompatibility
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfIdentityCubicCompatibility
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Matrix.Order]
   utility: none
   digest: Actual arbitrary-dimensional cubic HSF compatibility at identity with sharp constant five. -/

/-
admission_basis: escape-witness
proof_shape: identity_cubic_compatibility: content
escape_witness: HsfContractionCubic.coefficient_gap_identity
The actual CFC derivative bridge is applied to the signed and positive pencils.
The full contraction certificate keeps all four PSD endpoints.
-/

module
public import D5.S3.Quantum.Matrix.HsfContractionCubic
public import D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives

/-! Actual CFC derivatives at Y=I and signed endpoint transfer. -/
@[expose] public section
noncomputable section
open Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
namespace D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility
open HsfQubitMixedCubic HsfIdentityCubicDerivatives HsfContractionCubic
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The original sandwiched cubic trace with actual CFC powers. -/
def curve (U H K : Matrix n n ℂ) (t : ℝ) : ℝ :=
  (Matrix.trace ((CFC.rpow (1+t • K) (-(1 : ℝ)/3) * (U+t • H) *
    CFC.rpow (1+t • K) (-(1 : ℝ)/3))^3)).re

section Rotations
variable (U H K : Matrix n n ℂ)
private theorem w_huh : Matrix.trace (H*(U*(H))) =
    Matrix.trace (H*(H*(U))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (H*U) (H))
private theorem w_kuuku : Matrix.trace (K*(U*(U*(K*(U))))) =
    Matrix.trace (K*(U*(K*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (K*U*U) (K*U))
private theorem w_uhh : Matrix.trace (U*(H*(H))) =
    Matrix.trace (H*(H*(U))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (H*H))
private theorem w_uhku : Matrix.trace (U*(H*(K*(U)))) =
    Matrix.trace (H*(K*(U*(U)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (H*K*U))
private theorem w_uhu : Matrix.trace (U*(H*(U))) =
    Matrix.trace (H*(U*(U))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (H*U))
private theorem w_uhuk : Matrix.trace (U*(H*(U*(K)))) =
    Matrix.trace (H*(U*(K*(U)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (H*U*K))
private theorem w_ukhu : Matrix.trace (U*(K*(H*(U)))) =
    Matrix.trace (H*(U*(U*(K)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*K) (H*U))
private theorem w_ukkuu : Matrix.trace (U*(K*(K*(U*(U))))) =
    Matrix.trace (K*(K*(U*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (K*K*U*U))
private theorem w_ukuku : Matrix.trace (U*(K*(U*(K*(U))))) =
    Matrix.trace (K*(U*(K*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (K*U*K*U))
private theorem w_ukuu : Matrix.trace (U*(K*(U*(U)))) =
    Matrix.trace (K*(U*(U*(U)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U) (K*U*U))
private theorem w_ukuuk : Matrix.trace (U*(K*(U*(U*(K))))) =
    Matrix.trace (K*(U*(K*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*K*U*U) (K))
private theorem w_uuh : Matrix.trace (U*(U*(H))) =
    Matrix.trace (H*(U*(U))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*U) (H))
private theorem w_uukku : Matrix.trace (U*(U*(K*(K*(U))))) =
    Matrix.trace (K*(K*(U*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*U) (K*K*U))
private theorem w_uuku : Matrix.trace (U*(U*(K*(U)))) =
    Matrix.trace (K*(U*(U*(U)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*U) (K*U))
private theorem w_uukuk : Matrix.trace (U*(U*(K*(U*(K))))) =
    Matrix.trace (K*(U*(K*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*U) (K*U*K))
private theorem w_uuuk : Matrix.trace (U*(U*(U*(K)))) =
    Matrix.trace (K*(U*(U*(U)))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*U*U) (K))
private theorem w_uuukk : Matrix.trace (U*(U*(U*(K*(K))))) =
    Matrix.trace (K*(K*(U*(U*(U))))) := by
  simpa only [Matrix.mul_assoc] using
    (Matrix.trace_mul_comm (U*U*U) (K*K))
end Rotations

private theorem coefficient_transfer (U H K : Matrix n n ℂ) :
    coefficient2 U H K = 4*coefficient2 U ((1/2 : ℝ) • (U+H)) ((1/2 : ℝ) • (1+K)) ∧
    coefficient3 U H K = 4*coefficient2 U ((1/2 : ℝ) • (U+H)) ((1/2 : ℝ) • (1+K)) +
      8*coefficient3 U ((1/2 : ℝ) • (U+H)) ((1/2 : ℝ) • (1+K)) := by
  constructor <;>
    simp only [coefficient2, coefficient3, traceCoefficient2, traceCoefficient3,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul,
      Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re,
      Complex.real_smul, Matrix.mul_assoc] <;>
    simp only [
w_huh U H K,
      w_kuuku U H K,
      w_uhh U H K,
      w_uhku U H K,
      w_uhu U H K,
      w_uhuk U H K,
      w_ukhu U H K,
      w_ukkuu U H K,
      w_ukuku U H K,
      w_ukuu U H K,
      w_ukuuk U H K,
      w_uuh U H K,
      w_uukku U H K,
      w_uuku U H K,
      w_uukuk U H K,
      w_uuuk U H K,
      w_uuukk U H K] <;>
    norm_num <;> ring

/-- Actual positive-direction third derivative is bounded by the actual second derivative. -/
theorem positive_direction_bound (U H K : Matrix n n ℂ)
    (hH : H.PosSemidef) (hUH : (U-H).PosSemidef)
    (hK : K.PosSemidef) (hIK : (1-K).PosSemidef) :
    iteratedDeriv 3 (curve U H K) 0 ≤ iteratedDeriv 2 (curve U H K) 0 := by
  obtain ⟨hd2, hd3⟩ := identity_cubic_trace_derivatives U H K hK.isHermitian
  change iteratedDeriv 2 (curve U H K) 0 = _ at hd2
  change iteratedDeriv 3 (curve U H K) 0 = _ at hd3
  rw [hd2, hd3]
  exact coefficient_gap_nonneg U H K hH hUH hK hIK

/-- The exact signed transfer is obtained from the actual derivative supplier.
It includes all noncommuting matrix terms of the fractional linear reparametrization. -/
theorem signed_derivative_transfer (U H K : Matrix n n ℂ) (hK : K.IsHermitian) :
    let g := curve U ((1/2 : ℝ) • (U+H)) ((1/2 : ℝ) • (1+K))
    iteratedDeriv 2 (curve U H K) 0 = 4*iteratedDeriv 2 g 0 ∧
    iteratedDeriv 3 (curve U H K) 0 =
      12*iteratedDeriv 2 g 0 + 8*iteratedDeriv 3 g 0 := by
  dsimp only
  have hk : (((1/2 : ℝ) • (1+K))).IsHermitian :=
    (Matrix.isHermitian_one.add hK).smul _
  obtain ⟨hf2, hf3⟩ := identity_cubic_trace_derivatives U H K hK
  obtain ⟨hg2, hg3⟩ := identity_cubic_trace_derivatives U
    ((1/2 : ℝ) • (U+H)) ((1/2 : ℝ) • (1+K)) hk
  obtain ⟨hc2, hc3⟩ := coefficient_transfer U H K
  change iteratedDeriv 2 (curve U H K) 0 = _ at hf2
  change iteratedDeriv 3 (curve U H K) 0 = _ at hf3
  change iteratedDeriv 2 (curve U _ _) 0 = _ at hg2
  change iteratedDeriv 3 (curve U _ _) 0 = _ at hg3
  rw [hf2, hf3, hg2, hg3]
  constructor <;> linarith

private theorem signed_upper (U H K : Matrix n n ℂ) (hK : K.IsHermitian)
    (hp : (U+H).PosSemidef) (hn : (U-H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    iteratedDeriv 3 (curve U H K) 0 ≤ 5*iteratedDeriv 2 (curve U H K) 0 := by
  let A := (1/2 : ℝ) • (U+H)
  let P := (1/2 : ℝ) • (1+K)
  have ha : A.PosSemidef := hp.smul (by norm_num : (0 : ℝ) ≤ 1/2)
  have hb : (U-A).PosSemidef := by
    have he : U-A = (1/2 : ℝ) • (U-H) := by dsimp [A]; module
    rw [he]
    exact hn.smul (by norm_num : (0 : ℝ) ≤ 1/2)
  have hp' : P.PosSemidef := kp.smul (by norm_num : (0 : ℝ) ≤ 1/2)
  have hq : (1-P).PosSemidef := by
    have he : 1-P = (1/2 : ℝ) • (1-K) := by dsimp [P]; module
    rw [he]
    exact kn.smul (by norm_num : (0 : ℝ) ≤ 1/2)
  have hbnd := positive_direction_bound U A P ha hb hp' hq
  obtain ⟨h2,h3⟩ := signed_derivative_transfer U H K hK
  change iteratedDeriv 2 (curve U H K) 0 = 4*iteratedDeriv 2 (curve U A P) 0 at h2
  change iteratedDeriv 3 (curve U H K) 0 =
    12*iteratedDeriv 2 (curve U A P) 0+8*iteratedDeriv 3 (curve U A P) 0 at h3
  linarith

/-- Arbitrary finite complex dimension, all signed PSD endpoints, actual CFC derivatives.
Positive definiteness of U is not needed for this identity-denominator derivative estimate. -/
theorem identity_cubic_compatibility (U H K : Matrix n n ℂ) (hK : K.IsHermitian)
    (hp : (U+H).PosSemidef) (hn : (U-H).PosSemidef)
    (kp : (1+K).PosSemidef) (kn : (1-K).PosSemidef) :
    0 ≤ iteratedDeriv 2 (curve U H K) 0 ∧
      |iteratedDeriv 3 (curve U H K) 0| ≤ 5*iteratedDeriv 2 (curve U H K) 0 := by
  have hu := signed_upper U H K hK hp hn kp kn
  have hl := signed_upper U (-H) (-K) hK.neg
    (by simpa using hn) (by simpa using hp)
    (by simpa using kn) (by simpa using kp)
  obtain ⟨hf2,hf3⟩ := identity_cubic_trace_derivatives U H K hK
  obtain ⟨hr2,hr3⟩ := identity_cubic_trace_derivatives U (-H) (-K) hK.neg
  have he2 : coefficient2 U (-H) (-K) = coefficient2 U H K := by
    simp [coefficient2, traceCoefficient2]
  have he3 : coefficient3 U (-H) (-K) = -coefficient3 U H K := by
    simp only [coefficient3, traceCoefficient3, neg_mul, mul_neg, neg_neg,
      Matrix.trace_neg, Complex.neg_re, Complex.add_re, Complex.sub_re, Complex.mul_re]
    ring
  change iteratedDeriv 2 (curve U H K) 0 = _ at hf2
  change iteratedDeriv 3 (curve U H K) 0 = _ at hf3
  change iteratedDeriv 2 (curve U (-H) (-K)) 0 = _ at hr2
  change iteratedDeriv 3 (curve U (-H) (-K)) 0 = _ at hr3
  rw [hr2,hr3,he2,he3,← hf2,← hf3] at hl
  have hab := abs_le.mpr ⟨by linarith, hu⟩
  exact ⟨by nlinarith [abs_nonneg (iteratedDeriv 3 (curve U H K) 0)], hab⟩

/-- The scalar feasible direction H=U=I, K=-I attains the constant five. -/
theorem sharp5 :
    iteratedDeriv 2 (curve (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1)) 0 = 24 ∧
    iteratedDeriv 3 (curve (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1)) 0 = 120 := by
  have hk : (-1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian := Matrix.isHermitian_one.neg
  obtain ⟨h2,h3⟩ := identity_cubic_trace_derivatives
    (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1) hk
  change iteratedDeriv 2 (curve (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1)) 0 = _ at h2
  change iteratedDeriv 3 (curve (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 (-1)) 0 = _ at h3
  rw [h2,h3]
  norm_num [coefficient2, coefficient3, traceCoefficient2, traceCoefficient3,
    Matrix.trace, Fin.sum_univ_succ]

end D5.S3.Quantum.Matrix.HsfIdentityCubicCompatibility
