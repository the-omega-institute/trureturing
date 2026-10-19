/- GID: D5/S3/Quantum/QuantumChannels/QuantitativeCPRankHorizon
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QuantitativeCPRankHorizon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native positive compression controls coherent orbit leakage and density observations. -/

import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder MatrixOrder

namespace D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 400000 in
-- The matrix square root is transported to the operator-norm carrier in this proof.
/-- The actual corner leakage controls all coherent blocks of a subunital CP orbit.
The orbit comparison and the density observation use the same projection. -/
theorem coherent_compression_trace_transfer
    {d : ℕ}
    (T : CompletelyPositiveMap (CStarMatrix (Fin d) (Fin d) ℂ)
      (CStarMatrix (Fin d) (Fin d) ℂ))
    (hT : T 1 ≤ 1)
    (P X σ : CStarMatrix (Fin d) (Fin d) ℂ)
    (hP : IsStarProjection P) (hXP : X ≤ P)
    (hσ : 0 ≤ σ) (hσtr : Matrix.trace (CStarMatrix.ofMatrix.symm σ) = 1) :
    let α := Real.sqrt ‖(1 - P) * T P * (1 - P)‖
    ∀ n : ℕ,
      T^[n] X ≤ P + (2 * (n : ℝ) * α) • 1 ∧
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[n] X))).re ≤
        (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * P))).re + 2 * (n : ℝ) * α := by
  classical
  let Q : (CStarMatrix (Fin d) (Fin d) ℂ) := 1 - P
  let α : ℝ := Real.sqrt ‖Q * T P * Q‖
  have hα : 0 ≤ α := Real.sqrt_nonneg _
  have hQ : IsSelfAdjoint Q := hP.one_sub.isSelfAdjoint
  have hPstar : star P = P := hP.isSelfAdjoint
  have hQstar : star Q = Q := hQ
  have conjugate_mono {U V : (CStarMatrix (Fin d) (Fin d) ℂ)} (h : U ≤ V) (R : (CStarMatrix (Fin d) (Fin d) ℂ)) :
      R * U * star R ≤ R * V * star R := star_right_conjugate_le_conjugate h R
  have compressed_bounds {Y : (CStarMatrix (Fin d) (Fin d) ℂ)} (hY : 0 ≤ Y) (hYP : Y ≤ P) :
      0 ≤ P * T Y * P ∧ P * T Y * P ≤ P := by
    have hTY : 0 ≤ T Y := map_nonneg T hY
    constructor
    · simpa only [hPstar] using star_right_conjugate_nonneg hTY P
    · calc
        P * T Y * P ≤ P * 1 * P := by
          simpa only [hPstar] using conjugate_mono
            ((OrderHomClass.mono T (hYP.trans hP.le_one)).trans hT) P
        _ = P := by rw [mul_one]; exact hP.isIdempotentElem
  have step {Y : (CStarMatrix (Fin d) (Fin d) ℂ)} (hY : 0 ≤ Y) (hYP : Y ≤ P) :
      T Y ≤ P * T Y * P + (2 * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) := by
    let Z : (CStarMatrix (Fin d) (Fin d) ℂ) := T Y
    have hZ : 0 ≤ Z := map_nonneg T hY
    have hZP : Z ≤ T P := OrderHomClass.mono T hYP
    have hZ1 : Z ≤ 1 := (OrderHomClass.mono T (hYP.trans hP.le_one)).trans hT
    have hZstar : star Z = Z := IsSelfAdjoint.of_nonneg hZ
    have hZm : 0 ≤ CStarMatrix.ofMatrix.symm Z :=
      map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hZ
    let S : CStarMatrix (Fin d) (Fin d) ℂ :=
      CStarMatrix.ofMatrix (CFC.sqrt (CStarMatrix.ofMatrix.symm Z))
    have hsstar : star S = S := by
      change star (CFC.sqrt (CStarMatrix.ofMatrix.symm Z)) = _
      exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
    have hSS : S * S = Z := by
      change CFC.sqrt (CStarMatrix.ofMatrix.symm Z) *
        CFC.sqrt (CStarMatrix.ofMatrix.symm Z) = CStarMatrix.ofMatrix.symm Z
      exact CFC.sqrt_mul_sqrt_self _ hZm
    have hsquare : ‖S‖ ^ 2 = ‖Z‖ := by
      rw [pow_two, ← CStarRing.norm_star_mul_self, hsstar, hSS]
    have hs : ‖S‖ ≤ 1 := by
      have hz := (CStarAlgebra.norm_le_one_iff_of_nonneg Z hZ).mpr hZ1
      apply (sq_le_sq₀ (norm_nonneg S) zero_le_one).mp
      simpa only [one_pow] using hsquare.trans_le hz
    have hqpos : 0 ≤ Q * Z * Q := by
      simpa only [hQstar] using star_right_conjugate_nonneg hZ Q
    have hqle : Q * Z * Q ≤ Q * T P * Q := by
      simpa only [hQstar] using conjugate_mono hZP Q
    have hqsquare : ‖Q * S‖ ^ 2 = ‖Q * Z * Q‖ := by
      rw [pow_two, ← CStarRing.norm_self_mul_star, star_mul, hsstar, hQstar]
      rw [mul_assoc, ← mul_assoc (S), hSS, ← mul_assoc]
    have hqs : ‖Q * S‖ ≤ α := by
      have hh := CStarAlgebra.norm_le_norm_of_le_of_nonneg hqle hqpos
      have ha2 : α ^ 2 = ‖Q * T P * Q‖ := Real.sq_sqrt (norm_nonneg _)
      apply (sq_le_sq₀ (norm_nonneg (Q * S)) hα).mp
      rw [hqsquare, ha2]
      exact hh
    have hQZ : ‖Q * Z‖ ≤ α := by
      calc
        ‖Q * Z‖ = ‖(Q * S) * S‖ := by
          rw [mul_assoc, hSS]
        _ ≤ ‖Q * S‖ * ‖S‖ := norm_mul_le _ _
        _ ≤ α * 1 := mul_le_mul hqs hs (norm_nonneg _) hα
        _ = α := mul_one _
    have hZQ : ‖Z * Q‖ ≤ α := by
      calc
        ‖Z * Q‖ = ‖star (Z * Q)‖ := (norm_star _).symm
        _ = ‖Q * Z‖ := by rw [star_mul, hQstar, hZstar]
        _ ≤ α := hQZ
    have hnorm : ‖Z - P * Z * P‖ ≤ 2 * α := by
      have hid : Z - P * Z * P = Q * Z + P * (Z * Q) := by
        dsimp only [Q]
        simp only [sub_mul, mul_sub, one_mul, mul_one, mul_assoc]
        abel
      rw [hid]
      calc
        _ ≤ ‖Q * Z‖ + ‖P * (Z * Q)‖ := norm_add_le _ _
        _ ≤ α + 1 * α := add_le_add hQZ
          ((norm_mul_le _ _).trans (mul_le_mul (hP.norm_le P) hZQ
            (norm_nonneg _) zero_le_one))
        _ = 2 * α := by ring
    have hself : IsSelfAdjoint (Z - P * Z * P) :=
      (IsSelfAdjoint.of_nonneg hZ).sub
        (IsSelfAdjoint.of_nonneg (compressed_bounds hY hYP).1)
    have horder := hself.le_algebraMap_norm_self
    have hscalar : algebraMap ℝ (CStarMatrix (Fin d) (Fin d) ℂ) ‖Z - P * Z * P‖ ≤ (2 * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact smul_le_smul_of_nonneg_right hnorm zero_le_one
    exact sub_le_iff_le_add.mp (horder.trans hscalar) |>.trans_eq (add_comm _ _)
  have hstepP : T P ≤ P + (2 * α) • (1 : CStarMatrix (Fin d) (Fin d) ℂ) := by
    have hsp : T P ≤ P * T P * P + (2 * α) • (1 : CStarMatrix (Fin d) (Fin d) ℂ) :=
      step (Y := P) hP.nonneg le_rfl
    have hpp : P * T P * P ≤ P :=
      (compressed_bounds (Y := P) hP.nonneg le_rfl).2
    exact hsp.trans (add_le_add hpp le_rfl)
  have orbit_order (n : ℕ) : T^[n] X ≤ P + (2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) := by
    induction n with
    | zero =>
      simpa only [Function.iterate_zero_apply, Nat.cast_zero, mul_zero, zero_mul,
        zero_smul, add_zero] using hXP
    | succ n ih =>
      have hc : 0 ≤ 2 * (n : ℝ) * α := by positivity
      have hmap := OrderHomClass.mono T ih
      have hscale : T ((2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ))) ≤
          (2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) := by
        rw [LinearMapClass.map_smul_of_tower]
        exact smul_le_smul_of_nonneg_left hT hc
      calc
        T^[n + 1] X = T (T^[n] X) := Function.iterate_succ_apply' _ _ _
        _ ≤ T P + (2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) := by
          exact (show T (T^[n] X) ≤ T P + T ((2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)))
            by simpa only [map_add] using hmap).trans (add_le_add le_rfl hscale)
        _ ≤ (P + (2 * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ))) + (2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) :=
          add_le_add hstepP le_rfl
        _ = P + (2 * ((n + 1 : ℕ) : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) := by
          have hcoef : 2 * α + 2 * (n : ℝ) * α =
              2 * ((n + 1 : ℕ) : ℝ) * α := by push_cast; ring
          rw [add_assoc, ← add_smul, hcoef]
  have trace_mono {U V : (CStarMatrix (Fin d) (Fin d) ℂ)} (hUV : U ≤ V) :
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * U))).re ≤
        (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * V))).re := by
    have hσm := Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hσ)
    have hVm := Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (sub_nonneg.mpr hUV))
    have htr := hσm.trace_mul_nonneg hVm
    have hre : 0 ≤ (Matrix.trace
        (CStarMatrix.ofMatrix.symm σ * CStarMatrix.ofMatrix.symm (V - U))).re := htr.1
    change 0 ≤ (CStarMatrix.ofMatrix.symm σ *
      (CStarMatrix.ofMatrix.symm V - CStarMatrix.ofMatrix.symm U)).trace.re at hre
    change (CStarMatrix.ofMatrix.symm σ * CStarMatrix.ofMatrix.symm U).trace.re ≤
      (CStarMatrix.ofMatrix.symm σ * CStarMatrix.ofMatrix.symm V).trace.re
    simpa only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hre
  change ∀ n : ℕ, T^[n] X ≤ P + (2 * (n : ℝ) * α) • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)) ∧
    (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * T^[n] X))).re ≤
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * P))).re + 2 * (n : ℝ) * α
  intro n
  have ho := orbit_order n
  refine ⟨ho, ?_⟩
  have ht := trace_mono ho
  have heq (c : ℝ) :
      (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * (P + c • (1 : (CStarMatrix (Fin d) (Fin d) ℂ)))))).re =
        (Matrix.trace (CStarMatrix.ofMatrix.symm (σ * P))).re + c := by
    change (Matrix.trace (CStarMatrix.ofMatrix.symm σ *
      (CStarMatrix.ofMatrix.symm P + c • (1 : Matrix (Fin d) (Fin d) ℂ)))).re = _
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_add,
      Matrix.trace_smul, hσtr]
    simp
    rfl
  rwa [heq] at ht

#print axioms coherent_compression_trace_transfer

end D5.S3.Quantum.QuantumChannels.QuantitativeCPRankHorizon
