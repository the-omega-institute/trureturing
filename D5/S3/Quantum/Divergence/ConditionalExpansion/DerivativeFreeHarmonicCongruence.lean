/- GID: D5/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/ConditionalExpansion/DerivativeFreeHarmonicCongruence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthogonal Jordan ranges give quadratic and harmonic lower bounds for a positive congruence. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Matrix.Order

/-! The quadratic harmonic congruence bound from orthogonality of the two
modified Jordan ranges. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace DerivativeFreeHarmonicCongruence

open Matrix
open scoped ComplexOrder MatrixOrder
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (posTrace)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (effect_le_posTrace)
open RHLinalg (rtrace rtrace_add rtrace_sub trace_mul_nonneg_of_posSemidef)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "Mat" => Matrix ι ι ℂ

/-- The PSD matrix recording the positive and negative Jordan mass on the two sectors. -/
def harmonicB (X Q : Mat) : Mat :=
  Q * X⁺ * Q + (1 - Q) * X⁻ * (1 - Q)

def harmonicDelta (X Q : Mat) : ℝ := posTrace (-X) + rtrace (Q * X)

def harmonicValue (S X Q : Mat) : ℝ :=
  posTrace (-(S * X * S)) + rtrace (Q * (S * X * S))

private theorem complement_sq {P : Mat} (hPP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  simp only [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hPP, sub_self, sub_zero]

private theorem projection_effect {P : Mat} (hP : P.IsHermitian) (hPP : P * P = P) :
    0 ≤ P ∧ P ≤ 1 := by
  have hPc := Matrix.isHermitian_one.sub hP
  have hp := Matrix.posSemidef_conjTranspose_mul_self P
  have hc := Matrix.posSemidef_conjTranspose_mul_self (1 - P)
  rw [hP.eq, hPP] at hp
  rw [hPc.eq, complement_sq hPP] at hc
  exact ⟨hp.nonneg, sub_nonneg.mp hc.nonneg⟩

/-- Project onto the range of B and annihilate the orthogonal range of A. -/
private theorem exists_range_projection (A B : Mat) (hBA : Bᴴ * A = 0) :
    ∃ T : Mat, T.IsHermitian ∧ T * T = T ∧ T * A = 0 ∧ T * B = B := by
  let K := LinearMap.range B.toEuclideanLin
  have : IsBoundedSMul ℂ (EuclideanSpace ℂ ι) := by
    apply PiLp.instIsBoundedSMul
  have : ContinuousSMul ℂ (EuclideanSpace ℂ ι) := IsBoundedSMul.continuousSMul
  have : CompleteSpace K := K.complete_of_finiteDimensional.completeSpace_coe
  let p : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι := K.starProjection
  let T : Mat := Matrix.toEuclideanLin.symm p
  have hT : T.toEuclideanLin = p := Matrix.toEuclideanLin.apply_symm_apply p
  have hmul (L R : Mat) :
      (L * R).toEuclideanLin = L.toEuclideanLin.comp R.toEuclideanLin :=
    Matrix.toLpLin_mul_same 2 L R
  have hfix (x : EuclideanSpace ℂ ι) (hx : x ∈ K) : p x = x :=
    K.starProjection_eq_self_iff.mpr hx
  have horth : B.toEuclideanLin.adjoint.comp A.toEuclideanLin = 0 := by
    calc
      _ = (Bᴴ).toEuclideanLin.comp A.toEuclideanLin := by
        rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      _ = (Bᴴ * A).toEuclideanLin := by rw [hmul]
      _ = 0 := by rw [hBA, map_zero]
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    rw [hT]
    exact K.starProjection_isSymmetric
  · apply Matrix.toEuclideanLin.injective
    have hp : p.comp p = p := by
      apply LinearMap.ext
      intro x
      exact hfix (p x) (Submodule.coe_mem (K.orthogonalProjectionOnto x))
    rw [hmul, hT]
    exact hp
  · apply Matrix.toEuclideanLin.injective
    have hz : p.comp A.toEuclideanLin = 0 := by
      apply LinearMap.ext
      intro x
      change p (A.toEuclideanLin x) = 0
      apply K.starProjection_apply_eq_zero_iff.mpr
      change A.toEuclideanLin x ∈ B.toEuclideanLin.rangeᗮ
      rw [LinearMap.orthogonal_range, LinearMap.mem_ker]
      simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using DFunLike.congr_fun horth x
    rw [hmul, hT, map_zero]
    exact hz
  · apply Matrix.toEuclideanLin.injective
    have hp : p.comp B.toEuclideanLin = B.toEuclideanLin := by
      apply LinearMap.ext
      intro x
      exact hfix (B.toEuclideanLin x) ⟨x, rfl⟩
    rw [hmul, hT]
    exact hp

private theorem sqrt_mul_eq_zero {A Z : Mat} (hA : A.PosSemidef) (hAZ : A * Z = 0) :
    CFC.sqrt A * Z = 0 := by
  have hR := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  calc
    (CFC.sqrt A * Z)ᴴ * (CFC.sqrt A * Z) =
        Zᴴ * ((CFC.sqrt A * CFC.sqrt A) * Z) := by
          simp only [Matrix.conjTranspose_mul, hR.eq, mul_assoc]
    _ = 0 := by rw [CFC.sqrt_mul_sqrt_self A hA.nonneg, hAZ, Matrix.mul_zero]

private theorem sqrt_parts_mul_eq_zero (X : Mat) :
    CFC.sqrt (X⁻) * CFC.sqrt (X⁺) = 0 := by
  have hp := (CFC.posPart_nonneg X).posSemidef
  have hm := (CFC.negPart_nonneg X).posSemidef
  have hp' := (CFC.sqrt_nonneg (X⁺)).posSemidef.isHermitian
  have h := congrArg Matrix.conjTranspose (sqrt_mul_eq_zero hp (CFC.posPart_mul_negPart X))
  have hm' : X⁻ * CFC.sqrt (X⁺) = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero, hm.isHermitian.eq, hp'.eq]
      using h
  exact sqrt_mul_eq_zero hm hm'

private theorem sqrt_commute {W Q : Mat} (hW : W.PosSemidef) (hWQ : Commute W Q) :
    Commute (CFC.sqrt W) Q := by
  rw [CFC.sqrt_eq_real_sqrt W hW.nonneg]
  exact hWQ.cfcₙ_real Real.sqrt

private theorem inverse_commute {S U Q : Mat} (hSU : S * U = 1) (hUS : U * S = 1)
    (hSQ : Commute S Q) : Commute U Q := by
  change U * Q = Q * U
  calc
    U * Q = U * (Q * (S * U)) := by rw [hSU, Matrix.mul_one]
    _ = U * ((Q * S) * U) := by rw [mul_assoc]
    _ = (U * S) * (Q * U) := by rw [← hSQ.eq]; simp only [mul_assoc]
    _ = Q * U := by rw [hUS, Matrix.one_mul]

private theorem mul_corners (A P B R : Mat) (hPB : Commute P B) :
    (A * P) * (B * R) = (A * B) * (P * R) := by
  calc
    (A * P) * (B * R) = A * ((P * B) * R) := by simp only [mul_assoc]
    _ = (A * B) * (P * R) := by rw [hPB.eq]; simp only [mul_assoc]

private theorem modified_product {S U Q : Mat} (hSU : S * U = 1) (hUS : U * S = 1)
    (hSQ : Commute S Q) (hUQ : Commute U Q) (hQQ : Q * Q = Q) (t : ℝ) :
    (S * (1 - Q) + t • (U * Q)) * (S * Q + t • (U * (1 - Q))) = t • (1 : Mat) := by
  have hQcQ : (1 - Q) * Q = 0 := by rw [sub_mul, Matrix.one_mul, hQQ, sub_self]
  have hQQc : Q * (1 - Q) = 0 := by rw [mul_sub, Matrix.mul_one, hQQ, sub_self]
  have hQcU : Commute (1 - Q) U := (Commute.one_left U).sub_left hUQ.symm
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    mul_corners S (1 - Q) S Q ((Commute.one_left S).sub_left hSQ.symm),
    mul_corners S (1 - Q) U (1 - Q) hQcU, mul_corners U Q S Q hSQ.symm,
    mul_corners U Q U (1 - Q) hUQ.symm, hQcQ, hQQc, complement_sq hQQ, hQQ,
    hSU, hUS, Matrix.mul_zero, Matrix.one_mul, smul_zero, add_zero, zero_add]
  rw [← smul_add, add_comm Q (1 - Q), sub_add_cancel]

private theorem difference_sq {S U W : Mat} (hSS : S * S = W)
    (hSU : S * U = 1) (hUS : U * S = 1) (t : ℝ) :
    W - (S - t • U) * (S - t • U) =
      (2 * t) • (1 : Mat) - t ^ 2 • (U * U) := by
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hSS, hSU, hUS, pow_two, two_mul, add_smul]
  abel

private theorem rtrace_sandwich (A B : Mat) : rtrace (A * B * A) = rtrace (A * A * B) :=
  congrArg Complex.re (Matrix.trace_mul_cycle A B A)

private theorem rtrace_project {P : Mat} (hPP : P * P = P) (A : Mat) :
    rtrace (P * A) = rtrace (P * A * P) := by
  rw [rtrace_sandwich, hPP]

private theorem rtrace_filtered_sector {S P : Mat} (hSP : Commute S P)
    (hPP : P * P = P) (A : Mat) :
    rtrace (P * (S * A * S)) = rtrace ((S * S) * (P * A * P)) := by
  rw [rtrace_project hPP (S * A * S)]
  have heq : P * (S * A * S) * P = S * (P * A * P) * S := by
    calc
      _ = (P * S) * A * (S * P) := by simp only [mul_assoc]
      _ = (S * P) * A * (P * S) :=
        congrArg₂ (fun L R : Mat => L * A * R) hSP.eq.symm hSP.eq
      _ = _ := by simp only [mul_assoc]
  rw [heq, rtrace_sandwich]

private theorem rtrace_project_gram {P : Mat} (hP : P.IsHermitian)
    (hPP : P * P = P) (A : Mat) :
    rtrace (P * (A * Aᴴ)) = rtrace ((P * A) * (P * A)ᴴ) := by
  simpa only [Matrix.conjTranspose_mul, hP.eq, mul_assoc] using rtrace_project hPP (A * Aᴴ)

private theorem rtrace_effect_gram_le {P : Mat} (hP : P.IsHermitian)
    (hPP : P * P = P) (hP1 : P ≤ 1) (A : Mat) :
    rtrace ((P * A) * (P * A)ᴴ) ≤ rtrace (A * Aᴴ) := by
  rw [← rtrace_project_gram hP hPP A]
  have hn : 0 ≤ rtrace ((1 - P) * (A * Aᴴ)) :=
    trace_mul_nonneg_of_posSemidef (sub_nonneg.mpr hP1).posSemidef
      (Matrix.posSemidef_self_mul_conjTranspose A)
  rw [sub_mul, Matrix.one_mul, rtrace_sub] at hn
  exact sub_nonneg.mp hn

private theorem rtrace_harmonicB {X Q : Mat} (hX : X.IsHermitian) (hQQ : Q * Q = Q) :
    rtrace (harmonicB X Q) = harmonicDelta X Q := by
  have hXdec : X⁺ - X⁻ = X := CFC.posPart_sub_negPart X hX
  have hQX : Q * X = Q * X⁺ - Q * X⁻ := by
    calc
      _ = Q * (X⁺ - X⁻) := by rw [hXdec]
      _ = _ := mul_sub _ _ _
  have hneg : posTrace (-X) = rtrace (X⁻) := by
    change rtrace ((-X)⁺) = _
    rw [CFC.posPart_neg]
  rw [harmonicB, rtrace_add, ← rtrace_project hQQ (X⁺),
    ← rtrace_project (complement_sq hQQ) (X⁻), sub_mul, Matrix.one_mul,
    rtrace_sub, harmonicDelta, hneg, hQX, rtrace_sub]
  abel

private theorem harmonicB_psd (X : Mat) {Q : Mat} (hQ : Q.IsHermitian) :
    (harmonicB X Q).PosSemidef := by
  have hp := (CFC.posPart_nonneg X).posSemidef.conjTranspose_mul_mul_same Q
  have hm := (CFC.negPart_nonneg X).posSemidef.conjTranspose_mul_mul_same (1 - Q)
  simpa only [harmonicB, hQ.eq, (Matrix.isHermitian_one.sub hQ).eq] using hp.add hm

private theorem rtrace_pos_pairing {A B : Mat} (hA : A.PosDef) (hB : B.PosSemidef)
    (hB0 : B ≠ 0) : 0 < rtrace (A * B) := by
  let V := CFC.sqrt A
  have hV : V.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have hVV : V * V = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hunit : IsUnit V := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hunit
  have hc : (V * B * V).PosSemidef := by
    simpa only [hV.eq] using hB.conjTranspose_mul_mul_same V
  have hc0 : V * B * V ≠ 0 := by
    intro hz
    apply hB0
    calc
      B = (V⁻¹ * V) * B * (V * V⁻¹) := by
        rw [Matrix.nonsing_inv_mul V hdet, Matrix.mul_nonsing_inv V hdet,
          Matrix.one_mul, Matrix.mul_one]
      _ = V⁻¹ * (V * B * V) * V⁻¹ := by simp only [mul_assoc]
      _ = 0 := by rw [hz, Matrix.mul_zero, Matrix.zero_mul]
  have htr0 : (V * B * V).trace ≠ 0 := fun hz => hc0 (hc.trace_eq_zero_iff.mp hz)
  have hr0 : rtrace (V * B * V) ≠ 0 := by
    intro hz
    apply htr0
    have hr := D5.S3.Quantum.Foundation.FiniteTraceDistance.re_trace_eq_trace hc.isHermitian
    change ((rtrace (V * B * V) : ℝ) : ℂ) = _ at hr
    simpa only [hz, Complex.ofReal_zero] using hr.symm
  have hrn : 0 ≤ rtrace (V * B * V) := (RCLike.nonneg_iff.mp hc.trace_nonneg).1
  have hr := lt_of_le_of_ne hrn hr0.symm
  rwa [rtrace_sandwich, hVV] at hr

private theorem rtrace_real_smul (a : ℝ) (M : Mat) : rtrace (a • M) = a * rtrace M := by
  change (Matrix.trace (a • M)).re = a * M.trace.re
  rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

/-- For every real t, including when X has a kernel, the congruence gap is
bounded below by the quadratic with coefficients tr B and tr (W⁻¹ B). -/
theorem derivative_free_harmonic_congruence
    (W X Q : Mat) (hW : W.PosDef) (hX : X.IsHermitian) (hQ : Q.IsHermitian)
    (hQQ : Q * Q = Q) (hWQ : Commute W Q) (t : ℝ) :
    2 * t * harmonicDelta X Q - t ^ 2 * rtrace (W⁻¹ * harmonicB X Q) ≤
      harmonicValue (CFC.sqrt W) X Q := by
  let S := CFC.sqrt W
  let U := S⁻¹
  let Qc : Mat := 1 - Q
  let D := S - t • U
  let Mp := S * Qc + t • (U * Q)
  let Mm := S * Q + t • (U * Qc)
  let Rp := CFC.sqrt (X⁺)
  let Rm := CFC.sqrt (X⁻)
  let Y := S * X * S
  let Yp := S * X⁺ * S
  let Ym := S * X⁻ * S
  let B := harmonicB X Q
  have hS : S.IsHermitian := (CFC.sqrt_nonneg W).posSemidef.isHermitian
  have hSS : S * S = W := CFC.sqrt_mul_sqrt_self W hW.posSemidef.nonneg
  have hSunit : IsUnit S := (CFC.isUnit_sqrt_iff W hW.posSemidef.nonneg).mpr hW.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  have hSU : S * U = 1 := Matrix.mul_nonsing_inv S hSdet
  have hUS : U * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hUU : U * U = W⁻¹ := by rw [← hSS, Matrix.mul_inv_rev]
  have hU : U.IsHermitian := by
    change (S⁻¹)ᴴ = S⁻¹
    rw [Matrix.conjTranspose_nonsing_inv, hS.eq]
  have hSQ : Commute S Q := sqrt_commute hW.posSemidef hWQ
  have hUQ : Commute U Q := inverse_commute hSU hUS hSQ
  have hSQc : Commute S Qc := (Commute.one_right S).sub_right hSQ
  have hUQc : Commute U Qc := (Commute.one_right U).sub_right hUQ
  have hQc : Qc.IsHermitian := Matrix.isHermitian_one.sub hQ
  have hQcQc : Qc * Qc = Qc := complement_sq hQQ
  have hD : D.IsHermitian := hS.sub (hU.smul (IsSelfAdjoint.all t))
  -- The products of the two modified filters are scalar, even at t = 0.
  have hMm : Mm.IsHermitian :=
    ((hS.commute_iff hQ).mp hSQ).add (((hU.commute_iff hQc).mp hUQc).smul (IsSelfAdjoint.all t))
  have hMpMm : Mp * Mm = t • (1 : Mat) := modified_product hSU hUS hSQ hUQ hQQ t
  have hMmMp : Mm * Mp = t • (1 : Mat) := by
    have hMp : Mp.IsHermitian :=
      ((hS.commute_iff hQc).mp hSQc).add (((hU.commute_iff hQ).mp hUQ).smul
        (IsSelfAdjoint.all t))
    simpa only [Matrix.conjTranspose_mul, hMm.eq, hMp.eq, Matrix.conjTranspose_smul,
      star_trivial, Matrix.conjTranspose_one] using congrArg Matrix.conjTranspose hMpMm
  have hSp : S = Mp + D * Q := by
    dsimp only [Mp, Qc, D]
    simp only [mul_sub, sub_mul, Matrix.mul_one, Matrix.smul_mul]
    abel
  have hSm : S = Mm + D * Qc := by
    dsimp only [Mm, Qc, D]
    simp only [mul_sub, sub_mul, Matrix.mul_one, Matrix.smul_mul, smul_sub]
    abel
  have hRp : Rp.IsHermitian := (CFC.sqrt_nonneg (X⁺)).posSemidef.isHermitian
  have hRm : Rm.IsHermitian := (CFC.sqrt_nonneg (X⁻)).posSemidef.isHermitian
  have hRpRp : Rp * Rp = X⁺ := CFC.sqrt_mul_sqrt_self _ (CFC.posPart_nonneg X)
  have hRmRm : Rm * Rm = X⁻ := CFC.sqrt_mul_sqrt_self _ (CFC.negPart_nonneg X)
  have hRmRp : Rm * Rp = 0 := sqrt_parts_mul_eq_zero X
  have horth : (Mm * Rm)ᴴ * (Mp * Rp) = 0 := by
    rw [Matrix.conjTranspose_mul, hRm.eq, hMm.eq]
    calc
      _ = Rm * ((Mm * Mp) * Rp) := by simp only [mul_assoc]
      _ = 0 := by rw [hMmMp, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hRmRp, smul_zero]
  -- Project onto the modified negative range. Only the D terms survive
  -- when measuring the two filtered Jordan parts on the opposite sectors.
  obtain ⟨T, hT, hTT, hTp, hTm⟩ := exists_range_projection (Mp * Rp) (Mm * Rm) horth
  let Tc : Mat := 1 - T
  have hTc : Tc.IsHermitian := Matrix.isHermitian_one.sub hT
  have hTcTc : Tc * Tc = Tc := complement_sq hTT
  obtain ⟨hT0, hT1⟩ := projection_effect hT hTT
  have hTc1 : Tc ≤ 1 := (projection_effect hTc hTcTc).2
  have hTcm : Tc * (Mm * Rm) = 0 := by
    change (1 - T) * (Mm * Rm) = 0
    rw [sub_mul, Matrix.one_mul, hTm, sub_self]
  have htransportP : T * (S * Rp) = T * (D * Q * Rp) := by
    conv_lhs => rw [hSp, add_mul, mul_add, hTp, zero_add]
  have htransportM : Tc * (S * Rm) = Tc * (D * Qc * Rm) := by
    conv_lhs => rw [hSm, add_mul, mul_add, hTcm, zero_add]
  have hYp : (S * Rp) * (S * Rp)ᴴ = Yp := by
    change (S * Rp) * (S * Rp)ᴴ = S * X⁺ * S
    simpa only [Matrix.conjTranspose_mul, hS.eq, hRp.eq, mul_assoc] using
      congrArg (fun K : Mat => S * K * S) hRpRp
  have hYm : (S * Rm) * (S * Rm)ᴴ = Ym := by
    change (S * Rm) * (S * Rm)ᴴ = S * X⁻ * S
    simpa only [Matrix.conjTranspose_mul, hS.eq, hRm.eq, mul_assoc] using
      congrArg (fun K : Mat => S * K * S) hRmRm
  have hDp : (D * Q * Rp) * (D * Q * Rp)ᴴ = D * (Q * X⁺ * Q) * D := by
    simpa only [Matrix.conjTranspose_mul, hD.eq, hQ.eq, hRp.eq, mul_assoc] using
      congrArg (fun K : Mat => D * (Q * K * Q) * D) hRpRp
  have hDm : (D * Qc * Rm) * (D * Qc * Rm)ᴴ = D * (Qc * X⁻ * Qc) * D := by
    simpa only [Matrix.conjTranspose_mul, hD.eq, hQc.eq, hRm.eq, mul_assoc] using
      congrArg (fun K : Mat => D * (Qc * K * Qc) * D) hRmRm
  have hlossP : rtrace (T * Yp) ≤ rtrace (D * D * (Q * X⁺ * Q)) := by
    rw [← hYp, rtrace_project_gram hT hTT, htransportP, ← rtrace_sandwich D (Q * X⁺ * Q)]
    exact (rtrace_effect_gram_le hT hTT hT1 (D * Q * Rp)).trans_eq (congrArg rtrace hDp)
  have hlossM : rtrace (Tc * Ym) ≤ rtrace (D * D * (Qc * X⁻ * Qc)) := by
    rw [← hYm, rtrace_project_gram hTc hTcTc, htransportM,
      ← rtrace_sandwich D (Qc * X⁻ * Qc)]
    exact (rtrace_effect_gram_le hTc hTcTc hTc1 (D * Qc * Rm)).trans_eq (congrArg rtrace hDm)
  have hloss : rtrace (T * Yp) + rtrace (Tc * Ym) ≤ rtrace (D * D * B) := by
    change _ ≤ rtrace (D * D * (Q * X⁺ * Q + Qc * X⁻ * Qc))
    rw [mul_add, rtrace_add]
    exact add_le_add hlossP hlossM
  have hbase : rtrace (Q * Yp) + rtrace (Qc * Ym) = rtrace (W * B) := by
    change rtrace (Q * (S * X⁺ * S)) + rtrace (Qc * (S * X⁻ * S)) =
      rtrace (W * (Q * X⁺ * Q + Qc * X⁻ * Qc))
    rw [rtrace_filtered_sector hSQ hQQ, rtrace_filtered_sector hSQc hQcQc,
      hSS, mul_add, rtrace_add]
  have hYdec : Y = Yp - Ym := by
    change S * X * S = S * X⁺ * S - S * X⁻ * S
    calc
      _ = S * (X⁺ - X⁻) * S := by rw [CFC.posPart_sub_negPart X hX]
      _ = _ := by rw [mul_sub, sub_mul]
  have hYh : Y.IsHermitian := by
    simpa only [hS.eq] using Matrix.isHermitian_conjTranspose_mul_mul S hX
  -- The effect bound pays for the two losses from the baseline tr(WB).
  have he : -rtrace (T * Y) ≤ posTrace (-Y) := by
    have h := effect_le_posTrace hYh.neg hT0 hT1
    simpa only [rtrace, mul_neg, Matrix.trace_neg, map_neg] using h
  have hrewrite : rtrace (W * B) - (rtrace (T * Yp) + rtrace (Tc * Ym)) =
      -rtrace (T * Y) + rtrace (Q * Y) := by
    rw [← hbase, hYdec, mul_sub, mul_sub, rtrace_sub, rtrace_sub]
    simp only [Qc, Tc, sub_mul, Matrix.one_mul, rtrace_sub]
    ring
  have htrace : rtrace (W * B) - rtrace (D * D * B) ≤ harmonicValue S X Q := by
    change _ ≤ posTrace (-Y) + rtrace (Q * Y)
    linarith only [hloss, hrewrite, he]
  have hDsq : W - D * D = (2 * t) • (1 : Mat) - t ^ 2 • W⁻¹ := by
    simpa only [hUU] using difference_sq hSS hSU hUS t
  have hscalar : rtrace (W * B) - rtrace (D * D * B) =
      2 * t * harmonicDelta X Q - t ^ 2 * rtrace (W⁻¹ * B) := by
    rw [← rtrace_sub, ← sub_mul, hDsq, sub_mul, rtrace_sub, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, rtrace_real_smul, rtrace_real_smul]
    rw [show rtrace B = harmonicDelta X Q from rtrace_harmonicB hX hQQ]
  change 2 * t * harmonicDelta X Q - t ^ 2 * rtrace (W⁻¹ * B) ≤ harmonicValue S X Q
  rw [← hscalar]
  exact htrace

/-- A positive input gap implies a positive denominator, and choosing t = δ / c
gives the harmonic quotient. -/
theorem derivative_free_harmonic_congruence_optimized
    (W X Q : Mat) (hW : W.PosDef) (hX : X.IsHermitian) (hQ : Q.IsHermitian)
    (hQQ : Q * Q = Q) (hWQ : Commute W Q)
    (hδ : 0 < harmonicDelta X Q) :
    harmonicDelta X Q ^ 2 / rtrace (W⁻¹ * harmonicB X Q) ≤
      harmonicValue (CFC.sqrt W) X Q := by
  let δ := harmonicDelta X Q
  let c := rtrace (W⁻¹ * harmonicB X Q)
  have hB0 : harmonicB X Q ≠ 0 := by
    intro hz
    have h := rtrace_harmonicB hX hQQ
    rw [hz] at h
    have hzero : (0 : ℝ) = δ := by
      simpa only [rtrace, Matrix.trace_zero, map_zero, δ] using h
    exact hδ.ne' hzero.symm
  have hc : 0 < c := rtrace_pos_pairing hW.inv (harmonicB_psd X hQ) hB0
  have h := derivative_free_harmonic_congruence W X Q hW hX hQ hQQ hWQ (δ / c)
  change 2 * (δ / c) * δ - (δ / c) ^ 2 * c ≤ harmonicValue (CFC.sqrt W) X Q at h
  change δ ^ 2 / c ≤ harmonicValue (CFC.sqrt W) X Q
  have hc0 : c ≠ 0 := ne_of_gt hc
  have heq : 2 * (δ / c) * δ - (δ / c) ^ 2 * c = δ ^ 2 / c := by
    field_simp [hc0]
    ring
  rw [heq] at h
  exact h

end DerivativeFreeHarmonicCongruence
