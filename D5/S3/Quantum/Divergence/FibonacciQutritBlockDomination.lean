/- GID: D5/S3/Quantum/Divergence/FibonacciQutritBlockDomination
   generality: S
   mirror-B: D5/B/S3/Quantum/Divergence/FibonacciQutritBlockDomination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strict improvement by compressing the comparison and relocating the null state. -/

import D5.S3.Quantum.Divergence.PositiveReferenceReplacement
import D5.S3.Quantum.Divergence.SingleCoordinatePinchingEntropy
import D5.S3.Quantum.Divergence.UmegakiNullReferencePenalty
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Orthogonal null placement strictly improves a full-rank comparison in
the prescribed qubit-plus-ray coordinates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination

private abbrev Qubit := Matrix (Fin 2) (Fin 2) ℂ
private abbrev Ray := Matrix Unit Unit ℂ
private abbrev Qutrit := Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) ℂ

private def D {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n ℂ) : ℝ :=
  (X * (CFC.log X - CFC.log Y)).trace.re

private def blockHom : (Qubit × Ray) →⋆ₐ[ℝ] Qutrit where
  toFun X := fromBlocks X.1 0 0 X.2
  map_zero' := by ext (i | i) (j | j) <;> rfl
  map_one' := fromBlocks_one
  map_add' X Y := by simp [fromBlocks_add]
  map_mul' X Y := by simp [fromBlocks_multiply]
  commutes' x := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change fromBlocks (x • (1 : Qubit)) 0 0 (x • (1 : Ray)) = x • (1 : Qutrit)
    simpa only [smul_zero, fromBlocks_one] using
      (fromBlocks_smul x (1 : Qubit) 0 0 (1 : Ray)).symm
  map_star' X := by simp [Matrix.star_eq_conjTranspose, fromBlocks_conjTranspose]

private lemma log_block (X : Qubit) (Y : Ray) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    CFC.log (fromBlocks X 0 0 Y) = fromBlocks (CFC.log X) 0 0 (CFC.log Y) := by
  let : ContinuousFunctionalCalculus ℝ (Qubit × Ray) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hxy : IsSelfAdjoint (X, Y) := Prod.ext hX hY
  have hf : ContinuousOn Real.log (spectrum ℝ X ∪ spectrum ℝ Y) :=
    (X.finite_real_spectrum.union Y.finite_real_spectrum).continuousOn _
  have hc : Continuous blockHom := blockHom.toLinearMap.continuous_of_finiteDimensional
  have hm := blockHom.map_cfc Real.log (X, Y) (by rwa [Prod.spectrum_eq]) hc hxy (hxy.map _)
  rw [cfc_map_prod (S := ℝ) Real.log X Y hf hxy hX hY] at hm
  exact hm.symm

private lemma trace_blocks (X : Qubit) (Y : Ray) (H : Matrix (Fin 2) Unit ℂ)
    (J : Matrix Unit (Fin 2) ℂ) :
    (fromBlocks X H J Y).trace.re = X.trace.re + Y.trace.re := by
  simp [Matrix.trace, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₂₂]

private lemma ray_log (x : ℝ) :
    CFC.log (x • (1 : Ray)) = Real.log x • (1 : Ray) := by
  rw [← Algebra.algebraMap_eq_smul_one, CFC.log_algebraMap, Algebra.algebraMap_eq_smul_one]

private lemma null_penalty (A C ρ : Qutrit) (u lam e : ℝ)
    (hu : 0 < u) (hlam : 0 < lam) (he : 0 ≤ e) (hA : u • C ≤ A)
    (hC : lam • (1 : Qutrit) ≤ C) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    u * lam * Real.log (1 + e / lam) ≤ (A * (CFC.log (C + e • ρ) - CFC.log C)).trace.re := by
  let f := Fintype.equivFin (Fin 2 ⊕ Unit)
  let E := Matrix.reindexAlgEquiv ℝ ℂ f
  have mono : Monotone E := by
    intro X Y h
    exact Matrix.le_iff.mpr ((Matrix.le_iff.mp h).submatrix f.symm)
  have logmap (X : Qutrit) : E (CFC.log X) = CFC.log (E X) :=
    (Matrix.cfc_reindex Real.log f (A := X)).symm
  have traceE (X : Qutrit) : (E X).trace = X.trace :=
    ConditionalHockeyStickOrthogonalReduction.trace_reindex f X
  have hh := UmegakiNullReferencePenalty.log_increment_ge (E A) (E C) (E ρ) u lam e
    hu hlam he (by simpa only [map_smul] using mono hA)
    (by simpa only [map_smul, map_one] using mono hC)
    (hρ.submatrix f.symm) ((traceE ρ).trans htr)
  rw [← map_smul, ← map_add, ← logmap, ← logmap,
    ← map_sub, ← map_mul, traceE] at hh
  exact hh

private lemma strict_scalar_margin {c lam e : ℝ}
    (hc : 11 / 19 ≤ c) (hl : 0 < lam) (hsmall : lam < 1 / 500) (he : c / 3 ≤ e) :
    0 < (4 / 3 : ℝ) * lam * Real.log (1 + e / lam) -
      (18 / 55 : ℝ) * lam * Real.log (c / lam) - 2 * lam := by
  have h64 : 64 < c / lam := (lt_div_iff₀ hl).mpr (by linarith)
  have hlog64 : Real.log (64 : ℝ) < Real.log (c / lam) := Real.log_lt_log (by norm_num) h64
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow] at hlog64
  have hlog3 : Real.log (3 : ℝ) < 2 * Real.log 2 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) < 2 ^ (2 : ℕ))
    simpa [Real.log_pow] using h
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hrat : c / lam / 3 ≤ 1 + e / lam := by
    have h := div_le_div_of_nonneg_right he hl.le
    rw [div_div, mul_comm (3 : ℝ), ← div_div] at h
    linarith
  have hN := Real.log_le_log (by positivity : 0 < c / lam / 3) hrat
  rw [Real.log_div (by positivity : c / lam ≠ 0) (by norm_num)] at hN
  have hbase : 0 < (4 / 3 : ℝ) * Real.log (1 + e / lam) -
        (18 / 55 : ℝ) * Real.log (c / lam) - 2 := by
    norm_num at hlog64
    linarith
  nlinarith [mul_pos hl hbase]

set_option maxHeartbeats 1000000 in
/-- Once the smallest reference block is below the Fibonacci threshold,
replacing that coordinate and moving the null state onto its ray gives a
strictly larger actual matrix divergence. The displayed lower bound keeps
the pinching coefficient before relaxation and the quadratic Klein gain. -/
theorem strict_block_domination (Cₚ F : Qubit) (h : Matrix (Fin 2) Unit ℂ)
    (ρ : Qutrit) (a lam e : ℝ) (hCₚ : Cₚ.PosDef)
    (hlam : 0 < lam) (hsmall : lam < 1 / 500) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1)
    (hc : 11 / 19 ≤ Cₚ.trace.re + lam) (he : (Cₚ.trace.re + lam) / 3 ≤ e)
    (hfloor : lam • (1 : Qubit) ≤ Cₚ)
    (htr : F.trace.re + a = 1)
    (hlo : (4 / 3 : ℝ) • fromBlocks Cₚ 0 0 (lam • (1 : Ray)) ≤
      fromBlocks F h hᴴ (a • (1 : Ray)))
    (hhi : fromBlocks F h hᴴ (a • (1 : Ray)) ≤
      (7 / 3 : ℝ) • fromBlocks Cₚ 0 0 (lam • (1 : Ray))) :
    let b := Cₚ.trace.re
    let c := b + lam
    let τ := b⁻¹ • Cₚ
    let F' := F + a • τ
    let C' := c • τ
    let C := fromBlocks Cₚ 0 0 (lam • (1 : Ray))
    let A := fromBlocks F h hᴴ (a • (1 : Ray))
    let A' := fromBlocks F' 0 0 (0 : Ray)
    let B' := fromBlocks C' 0 0 (e • (1 : Ray))
    let bound := (4 / 3 : ℝ) * lam * Real.log (1 + e / lam) -
      (12 / 55 : ℝ) * lam * (c / b) * Real.log (c / lam) -
      (a * (Real.log (a / (lam * (4 / 3))) - 1) + Real.log (c / b)) +
      ((a • τ)ᴴ * (a • τ)).trace.re / 2
    0 < bound ∧ bound ≤ D A' B' - D A (C + e • ρ) := by
  intro b c τ F' C' C A A' B' bound
  change 11 / 19 ≤ c at hc
  change c / 3 ≤ e at he
  have hb : 1 / 2 < b := by dsimp [c] at hc; linarith
  have hcpos : 0 < c := by linarith
  have hepos : 0 < e := by linarith
  have hFfloor : (4 / 3 : ℝ) • Cₚ ≤ F := by
    apply Matrix.le_iff.mpr
    exact (Matrix.le_iff.mp hlo).submatrix (Sum.inl : Fin 2 → Fin 2 ⊕ Unit)
  have hamin : 4 / 3 * lam ≤ a := by
    have hh := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hlo).diag_nonneg (i := Sum.inr ()))).1
    simpa [Matrix.sub_apply, Matrix.smul_apply, fromBlocks_apply₂₂, Complex.smul_re, smul_eq_mul] using hh
  have hamax : a ≤ 7 / 3 * lam := by
    have hh := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hhi).diag_nonneg (i := Sum.inr ()))).1
    simpa [Matrix.sub_apply, Matrix.smul_apply, fromBlocks_apply₂₂, Complex.smul_re, smul_eq_mul] using hh
  have ha : 0 < a := by linarith
  have hCFloor : lam • (1 : Qutrit) ≤ C := by
    apply Matrix.le_iff.mpr
    rw [← fromBlocks_one (l := Fin 2) (m := Unit), fromBlocks_smul]
    have heq : C - fromBlocks (lam • (1 : Qubit)) (lam • (0 : Matrix (Fin 2) Unit ℂ))
        (lam • (0 : Matrix Unit (Fin 2) ℂ)) (lam • (1 : Ray)) =
        fromBlocks (Cₚ - lam • (1 : Qubit)) 0 0 (0 : Ray) := by
      ext (i | i) (j | j) <;> simp [C, Matrix.sub_apply]
    rw [heq]
    have hd := (Matrix.le_iff.mp hfloor).nonneg
    let S := CFC.sqrt (Cₚ - lam • (1 : Qubit))
    have hS : star S = S := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
    have hsq : star S * S = Cₚ - lam • (1 : Qubit) := by
      rw [hS, CFC.sqrt_mul_sqrt_self _ hd]
    have hprod := star_mul_self_nonneg (blockHom (S, 0))
    rw [← map_star, ← map_mul] at hprod
    exact Matrix.nonneg_iff_posSemidef.mp (by simpa [blockHom, hsq] using hprod)
  have hnull := null_penalty A C ρ (4 / 3) lam e (by norm_num) hlam hepos.le hlo hCFloor hρ hρtr
  have hcap : Cₚ ≤ c • (1 : Qubit) := by
    let H : HermitianMat (Fin 2) ℂ := ⟨Cₚ, hCₚ.isHermitian⟩
    have hH : 0 ≤ H := HermitianMat.zero_le_iff.mpr hCₚ.posSemidef
    have hh := HermitianMat.le_trace_smul_one hH
    change Cₚ ≤ b • (1 : Qubit) at hh
    have hbcap := hh
    exact hbcap.trans (smul_le_smul_of_nonneg_right (by dsimp [c]; linarith) zero_le_one)
  have hp := (SingleCoordinatePinchingEntropy.trace_entropy_pinching_bound Cₚ F h a lam c
    (4 / 3) (7 / 3) hCₚ hlam (by dsimp [c]; linarith) (by norm_num) (by norm_num)
    (by norm_num) hcap hlo hhi).2
  let A₀ : Qutrit := fromBlocks F 0 0 (a • (1 : Ray))
  have hpinch : (A * CFC.log A).trace.re - (A₀ * CFC.log A₀).trace.re ≤
      (12 / 55 : ℝ) * lam * (c / b) * Real.log (c / lam) := by
    exact sub_le_iff_le_add.mpr (by
      norm_num at hp
      simpa only [A, A₀, c, add_sub_cancel_right] using hp)
  have hreplace := (PositiveReferenceReplacement.positive_reference_replacement Cₚ F lam
    (4 / 3) a hCₚ hlam (by norm_num) ha hFfloor).2.2.2
  change D F Cₚ + a * Real.log (a / lam) - D F' C' ≤
    a * (Real.log (a / (lam * (4 / 3))) - 1) + (F.trace.re + a) * Real.log (c / b) -
      ((a • τ)ᴴ * (a • τ)).trace.re / (2 * (F.trace.re + a)) at hreplace
  rw [htr, one_mul, mul_one] at hreplace
  have hF := ((hCₚ.smul (by norm_num : (0 : ℝ) < 4 / 3)).isStrictlyPositive.of_le hFfloor).posDef
  have hτ := hCₚ.smul (inv_pos.mpr (by linarith : 0 < b))
  have hF' : F'.PosDef := hF.add_posSemidef (hτ.posSemidef.smul ha.le)
  have hC' : C'.PosDef := hτ.smul hcpos
  have hCLog : CFC.log C = fromBlocks (CFC.log Cₚ) 0 0 (Real.log lam • (1 : Ray)) := by
    rw [show C = fromBlocks Cₚ 0 0 (lam • (1 : Ray)) from rfl,
      log_block _ _ hCₚ.isHermitian (Matrix.PosDef.one.smul hlam).isHermitian, ray_log lam]
  have href : (A * CFC.log C).trace.re = (A₀ * CFC.log C).trace.re := by
    rw [hCLog]
    simp [A, A₀, fromBlocks_multiply, trace_blocks]
  have hD₀ : D A₀ C = D F Cₚ + a * Real.log (a / lam) := by
    have hA₀Log : CFC.log A₀ = fromBlocks (CFC.log F) 0 0 (Real.log a • (1 : Ray)) := by
      rw [show A₀ = fromBlocks F 0 0 (a • (1 : Ray)) from rfl,
        log_block _ _ hF.isHermitian (Matrix.PosDef.one.smul ha).isHermitian, ray_log a]
    simp only [D, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hA₀Log, hCLog]
    simp [A₀, fromBlocks_multiply, trace_blocks, Real.log_div ha.ne' hlam.ne']
    ring
  have hD' : D A' B' = D F' C' := by
    have hA'Log : CFC.log A' = fromBlocks (CFC.log F') 0 0 (0 : Ray) := by
      rw [show A' = fromBlocks F' 0 0 (0 : Ray) from rfl,
        log_block _ _ hF'.isHermitian Matrix.isHermitian_zero, CFC.log_zero]
    have hB'Log : CFC.log B' = fromBlocks (CFC.log C') 0 0 (Real.log e • (1 : Ray)) := by
      rw [show B' = fromBlocks C' 0 0 (e • (1 : Ray)) from rfl,
        log_block _ _ hC'.isHermitian (Matrix.PosDef.one.smul hepos).isHermitian, ray_log e]
    simp [D, A', Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hA'Log, hB'Log,
      fromBlocks_multiply, trace_blocks]
  constructor
  · have hlogr : Real.log (a / (lam * (4 / 3))) < 1 := by
      have hratio : a / (lam * (4 / 3)) ≤ 7 / 4 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      exact (Real.log_le_log (by positivity) hratio).trans_lt (by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 7 / 4)])
    have hlogc : Real.log (c / b) < 2 * lam := by
      have h := Real.log_le_sub_one_of_pos (show 0 < c / b by positivity)
      have hr : c / b - 1 = lam / b := by dsimp [c]; field_simp; ring
      rw [hr] at h
      exact h.trans_lt ((div_lt_iff₀ (by positivity)).mpr (by nlinarith [mul_pos hlam (sub_pos.mpr hb)]))
    have hpinch' : (12 / 55 : ℝ) * lam * (c / b) * Real.log (c / lam) ≤
        (18 / 55 : ℝ) * lam * Real.log (c / lam) := by
      have hr : c / b ≤ 3 / 2 := (div_le_iff₀ (by positivity)).mpr (by dsimp [c]; linarith)
      have hlogpos : 0 ≤ Real.log (c / lam) :=
        Real.log_nonneg ((le_div_iff₀ hlam).mpr (by dsimp [c]; linarith))
      have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ (12 / 55 : ℝ) * lam * Real.log (c / lam) by positivity)
      nlinarith
    have hquad : 0 ≤ ((a • τ)ᴴ * (a • τ)).trace.re / 2 :=
      div_nonneg (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self (a • τ)).trace_nonneg).1
        (by norm_num)
    dsimp only [bound]
    linarith [strict_scalar_margin hc hlam hsmall he, mul_neg_of_pos_of_neg ha (sub_neg.mpr hlogr)]
  · rw [hD']
    simp only [D, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re] at hnull hD₀ hreplace ⊢
    dsimp only [bound]
    linarith [hreplace]

#print axioms strict_block_domination

end D5.S3.Quantum.Divergence.FibonacciQutritBlockDomination
