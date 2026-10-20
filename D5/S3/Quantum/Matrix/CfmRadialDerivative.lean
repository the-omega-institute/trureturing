/- GID: D5/S3/Quantum/Matrix/CfmRadialDerivative
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CfmRadialDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.FDeriv.Mul]
   utility: none
   digest: Resolvent derivatives turn endpoint positivity into Frobenius radial inequalities. -/

/-
admission_basis: escape-witness
proof_shape: radial_of_endpoint_positive: content
escape_witness: radial_of_endpoint_positive
-/

import D5.S3.Quantum.Matrix.RadialConvexity
import D5.S3.Quantum.Matrix.CayleyResolvent
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open Matrix Set
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator RealInnerProductSpace

namespace D5.S3.Quantum.Matrix.CfmRadialDerivative

open CayleyResolvent RadialConvexity CartesianVariance

variable {n : ℕ}

abbrev Mat (n : ℕ) := _root_.Matrix (Fin n) (Fin n) ℂ

/-- The bounded Hermitian Cayley interval. -/
def cayleyDomain (n : ℕ) : Set (Mat n) := {X | (1 + X).PosDef ∧ (1 - X).PosDef}

/-- Sandwich derivative of a resolvent. -/
def resolventDerivative (s : ℝ) (X : Mat n) : Mat n →L[ℝ] Mat n :=
  ContinuousLinearMap.mulLeftRight ℝ (Mat n) (resolvent s X) (resolvent s X)

/-- The rational matrix map in bounded Cayley coordinates. -/
def resolventSum (ε : ℝ) (X : Mat n) : Mat n :=
  resolvent 2 X + resolvent 3 X - ε • resolvent 4 X

/-- The actual derivative, including the negative resolvent term. -/
def resolventSumDerivative (ε : ℝ) (X : Mat n) : Mat n →L[ℝ] Mat n :=
  resolventDerivative 2 X + resolventDerivative 3 X - ε • resolventDerivative 4 X

private theorem shift_posdef (s : ℝ) (hs : 2 ≤ s) {X : Mat n}
    (hX : X ∈ cayleyDomain n) : (s • (1 : Mat n) - X).PosDef := by
  have h := hX.2.add_posSemidef (Matrix.PosSemidef.one.smul (by linarith : 0 ≤ s - 1))
  convert h using 1 <;> module

private theorem hasFDerivAt_resolvent (s : ℝ) (X : Mat n)
    (hX : (s • (1 : Mat n) - X).PosDef) :
    HasFDerivAt (resolvent s) (resolventDerivative s X) X := by
  rcases hX.isUnit with ⟨u, hu⟩
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (Mat n)
        (Ring.inverse (s • (1 : Mat n) - X))
        (Ring.inverse (s • (1 : Mat n) - X))) (s • (1 : Mat n) - X) := by
    simpa only [← Ring.inverse_unit, hu] using hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have hc := hi.comp X ((hasFDerivAt_id X).const_sub (s • (1 : Mat n)))
  convert hc using 1
  · ext Y
    simp [CayleyResolvent.resolvent, Matrix.nonsing_inv_eq_ringInverse, Function.comp_def]
  · ext K i j
    simp [resolventDerivative, CayleyResolvent.resolvent, Matrix.nonsing_inv_eq_ringInverse,
      ContinuousLinearMap.mulLeftRight_apply]

private theorem hasFDerivAt_resolventSum (ε : ℝ) {X : Mat n}
    (hX : X ∈ cayleyDomain n) :
    HasFDerivAt (resolventSum ε) (resolventSumDerivative ε X) X := by
  exact ((hasFDerivAt_resolvent 2 X (shift_posdef 2 (by norm_num) hX)).add
    (hasFDerivAt_resolvent 3 X (shift_posdef 3 (by norm_num) hX))).sub
      ((hasFDerivAt_resolvent 4 X (shift_posdef 4 (by norm_num) hX)).const_smul ε)

private theorem cayley_segment {U V : Mat n} (hU : U ∈ cayleyDomain n)
    (hV : V ∈ cayleyDomain n) (hUV : U ≤ V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    U + t • (V - U) ∈ cayleyDomain n ∧
      U ≤ U + t • (V - U) ∧ U + t • (V - U) ≤ V := by
  have hH := (sub_nonneg.mpr hUV).posSemidef
  have hl : U ≤ U + t • (V - U) := by
    apply sub_nonneg.mp
    simpa using (hH.smul ht.1).nonneg
  have hr : U + t • (V - U) ≤ V := by
    apply sub_nonneg.mp
    convert (hH.smul (sub_nonneg.mpr ht.2)).nonneg using 1 <;> module
  have hp := hU.1.add_posSemidef (sub_nonneg.mpr hl).posSemidef
  have hq := hV.2.add_posSemidef (sub_nonneg.mpr hr).posSemidef
  refine ⟨⟨?_, ?_⟩, hl, hr⟩
  · convert hp using 1 <;> module
  · convert hq using 1 <;> module

private theorem resolventSum_hermitian (ε : ℝ) {X : Mat n}
    (hX : X ∈ cayleyDomain n) : (resolventSum ε X).IsHermitian := by
  exact (((shift_posdef 2 (by norm_num) hX).inv.isHermitian).add
    ((shift_posdef 3 (by norm_num) hX).inv.isHermitian)).sub
      (((shift_posdef 4 (by norm_num) hX).inv.isHermitian).smul (IsSelfAdjoint.all ε))

private theorem trace_sandwich_pairing (R H K : Mat n) :
    Matrix.trace (H * (R * K * R)) = Matrix.trace ((R * H * R) * K) := by
  calc
    _ = Matrix.trace ((H * R * K) * R) := by congr 1 <;> noncomm_ring
    _ = Matrix.trace (R * (H * R * K)) := Matrix.trace_mul_comm _ _
    _ = _ := by congr 1 <;> noncomm_ring

private theorem trace_derivative_pairing (ε : ℝ) (X H K : Mat n) :
    Matrix.trace (H * resolventSumDerivative ε X K) =
      Matrix.trace (resolventSumDerivative ε X H * K) := by
  simp only [resolventSumDerivative, resolventDerivative,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.mulLeftRight_apply,
    mul_sub, mul_add, sub_mul, add_mul, mul_smul_comm, smul_mul_assoc,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul]
  rw [trace_sandwich_pairing, trace_sandwich_pairing, trace_sandwich_pairing]

private def vectorizeReal (n : ℕ) : Mat n →L[ℝ] EuclideanSpace ℂ (Fin n × Fin n) :=
  ((vectorize n).toLinearMap.restrictScalars ℝ).toContinuousLinearMap

/-- Positivity at both endpoints of every ordered pair in the Cayley interval. -/
def EndpointPositive (n : ℕ) (ε : ℝ) : Prop :=
  ∀ U ∈ cayleyDomain n, ∀ V ∈ cayleyDomain n, U ≤ V →
    (resolventSumDerivative ε U (resolventSum ε V - resolventSum ε U)).PosSemidef ∧
    (resolventSumDerivative ε V (resolventSum ε V - resolventSum ε U)).PosSemidef

/-- Endpoint positivity of the sandwich derivative suffices throughout the
entire Cayley interval; no commutativity of the endpoints is assumed. -/
theorem radial_of_endpoint_positive (ε : ℝ)
    (hpositive : EndpointPositive n ε)
    {A C B : Mat n} (hA : A ∈ cayleyDomain n) (hC : C ∈ cayleyDomain n)
    (hB : B ∈ cayleyDomain n) (hAC : A ≤ C) (hCB : C ≤ B) :
    frobeniusNorm (resolventSum ε C - resolventSum ε A) ≤
        frobeniusNorm (resolventSum ε B - resolventSum ε A) ∧
      frobeniusNorm (resolventSum ε B - resolventSum ε C) ≤
        frobeniusNorm (resolventSum ε B - resolventSum ε A) := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n × Fin n)) :=
    InnerProductSpace.rclikeToReal ℂ _
  have hp (U : Mat n) (hU : U ∈ cayleyDomain n) (V : Mat n)
      (hV : V ∈ cayleyDomain n) (hUV : U ≤ V) (K : Mat n) (hK : 0 ≤ K) :
      0 ≤ ⟪vectorizeReal n (resolventSum ε V) - vectorizeReal n (resolventSum ε U),
        vectorizeReal n (resolventSumDerivative ε U K)⟫ ∧
      0 ≤ ⟪vectorizeReal n (resolventSum ε V) - vectorizeReal n (resolventSum ε U),
        vectorizeReal n (resolventSumDerivative ε V K)⟫ := by
    have hh := (resolventSum_hermitian ε hV).sub (resolventSum_hermitian ε hU)
    have pair (X : Mat n) :
        ⟪vectorizeReal n (resolventSum ε V) - vectorizeReal n (resolventSum ε U),
          vectorizeReal n (resolventSumDerivative ε X K)⟫ =
          (Matrix.trace (resolventSumDerivative ε X
            (resolventSum ε V - resolventSum ε U) * K)).re := by
      rw [← map_sub]
      change (inner ℂ (vectorize n _) (vectorize n _)).re = _
      rw [matrix_pairing, hh.eq, trace_derivative_pairing]
    rw [pair U, pair V]
    exact ⟨RHLinalg.trace_mul_nonneg_of_posSemidef (hpositive U hU V hV hUV).1 hK.posSemidef,
      RHLinalg.trace_mul_nonneg_of_posSemidef (hpositive U hU V hV hUV).2 hK.posSemidef⟩
  have h := radial_inequalities_of_endpoint_derivative (cayleyDomain n)
    (fun X => vectorizeReal n (resolventSum ε X))
    (fun X => (vectorizeReal n).comp (resolventSumDerivative ε X))
    (fun U hU V hV hUV t ht => cayley_segment hU hV hUV ht)
    (fun X hX => (vectorizeReal n).hasFDerivAt.comp X (hasFDerivAt_resolventSum ε hX))
    hp hA hC hB hAC hCB
  simpa only [← map_sub, vectorizeReal, frobeniusNorm,
    LinearMap.coe_toContinuousLinearMap', LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe] using h

end D5.S3.Quantum.Matrix.CfmRadialDerivative
