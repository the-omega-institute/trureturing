/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickSingularCriterion
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: All-threshold optimization for singular contractions on their actual common corner. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickCornerCriterion

/-! The common-corner residual condition is derived from actual feasible overlaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
open D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight
open D5.S3.Quantum.Divergence.MaximalHockeyStickCornerCriterion
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickSingularCriterion

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem eigenvalue_bounds (C : Matrix n n ℂ) (hC : C.PosSemidef) (hC1 : C ≤ 1) :
    ∀ i, 0 ≤ hC.isHermitian.eigenvalues i ∧ hC.isHermitian.eigenvalues i ≤ 1 := by
  have hf : cfc (fun x : ℝ => 1 - x) C = 1 - C := by
    rw [cfc_sub _ _ C (by fun_prop) (by fun_prop),
      cfc_const 1 C hC.isHermitian.isSelfAdjoint,
      cfc_id' ℝ C hC.isHermitian.isSelfAdjoint]
    simp
  have hp : 0 ≤ cfc (fun x : ℝ => 1 - x) C := hf.symm ▸ sub_nonneg.mpr hC1
  have hb := (cfc_nonneg_iff _ C (by fun_prop) hC.isHermitian.isSelfAdjoint).mp hp
  exact fun i => ⟨hC.eigenvalues_nonneg i,
    sub_nonneg.mp (hb _ (hC.isHermitian.eigenvalues_mem_spectrum_real i))⟩

/-- The canonical minimum is a genuine PSD overlap for every positive
contraction, including eigenvalues at both endpoints. -/
theorem canonical_feasible (C : Matrix n n ℂ) (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) : canonicalOverlap C t ∈ positiveOverlaps C (t • (1 - C)) := by
  have hb := eigenvalue_bounds C hC hC1
  obtain ⟨hrA, hrB⟩ := canonical_residuals C hC.isHermitian t
  refine ⟨?_, ?_, ?_⟩
  · apply cfc_nonneg
    intro x hx
    rw [hC.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact le_min (hb i).1 (mul_nonneg ht (sub_nonneg.mpr (hb i).2))
  · rw [← sub_nonneg, hrA]
    exact cfc_nonneg fun _ _ => le_max_right _ _
  · rw [← sub_nonneg, hrB]
    exact cfc_nonneg fun _ _ => le_max_right _ _

/-- Exact one-threshold criterion on the actual interior corner. Strict
positivity is required only for the compression of the trace weight. -/
theorem common_canonical_optimal_iff (C W : Matrix n n ℂ)
    (hC : C.PosSemidef) (hC1 : C ≤ 1)
    (hW : ((interiorEmbedding hC.isHermitian)ᴴ * W *
      interiorEmbedding hC.isHermitian).PosDef) (t : ℝ) (ht : 0 < t) :
    let P := interiorProjection C
    (∀ X ∈ positiveOverlaps C (t • (1 - C)),
      (W * X).trace.re ≤ (W * canonicalOverlap C t).trace.re) ↔
      thresholdPositive C t * (P * W * P) * thresholdNegative C t = 0 := by
  classical
  dsimp only
  let hH := hC.isHermitian
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  let d := hH.eigenvalues
  let D := diagonal (fun i => (d i : ℂ))
  let Y := diagonal (fun i => ((min (d i) (t * (1 - d i)) : ℝ) : ℂ))
  let F : Matrix n n ℂ := diagonal (fun i => if 0 < d i ∧ d i < 1 then 1 else 0)
  let V := e.symm W
  have hD : e D = C := by
    simpa only [e, D, d, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hH.spectral_theorem.symm
  have hY : e Y = canonicalOverlap C t := by
    rw [canonicalOverlap, hH.cfc_eq]
    rfl
  have hF : e F = interiorProjection C := by
    have he : interiorProjection C = e (diagonal (fun i =>
        ((if 0 < d i ∧ d i < 1 then 1 else 0 : ℝ) : ℂ))) := by
      rw [interiorProjection, hH.cfc_eq]
      rfl
    simpa only [F, apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using he.symm
  have hV : (V.submatrix (fun i : {i // 0 < d i ∧ d i < 1} => i.val)
      (fun i : {i // 0 < d i ∧ d i < 1} => i.val)).PosDef := by
    rw [← inclusion_compress]
    simpa only [V, e, Unitary.conjStarAlgAut_symm_apply, interiorEmbedding,
      Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose, Matrix.mul_assoc] using hW
  have hm {X Z : Matrix n n ℂ} (h : X ≤ Z) : e X ≤ e Z := by
    have hh := map_nonneg e (sub_nonneg.mpr h)
    simpa only [map_sub, sub_nonneg] using hh
  have hm' {X Z : Matrix n n ℂ} (h : X ≤ Z) : e.symm X ≤ e.symm Z := by
    have hh := map_nonneg e.symm (sub_nonneg.mpr h)
    simpa only [map_sub, sub_nonneg] using hh
  have hs (Z : Matrix n n ℂ) : e (t • Z) = t • e Z := by
    rw [← Complex.coe_smul t Z, ← Complex.coe_smul t (e Z), map_smul]
  have hB : e (t • (1 - D)) = t • (1 - C) := by rw [hs, map_sub, map_one, hD]
  have htrace (Z : Matrix n n ℂ) : (e Z).trace = Z.trace := by
    simp only [e, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hopt : (∀ X ∈ positiveOverlaps C (t • (1 - C)),
      (W * X).trace.re ≤ (W * canonicalOverlap C t).trace.re) ↔
      (∀ X ∈ positiveOverlaps D (t • (1 - D)),
        (V * X).trace.re ≤ (V * Y).trace.re) := by
    constructor
    · intro h X hX
      have hx : e X ∈ positiveOverlaps C (t • (1 - C)) :=
        ⟨map_nonneg e hX.1, (hm hX.2.1).trans_eq hD, (hm hX.2.2).trans_eq hB⟩
      have hh := h (e X) hx
      have hxtr : (W * e X).trace = (V * X).trace := by
        rw [show W = e V from (e.apply_symm_apply W).symm, ← map_mul, htrace]
      have hytr : (W * canonicalOverlap C t).trace = (V * Y).trace := by
        rw [← hY, show W = e V from (e.apply_symm_apply W).symm, ← map_mul, htrace]
      simpa only [hxtr, hytr] using hh
    · intro h X hX
      have hx : e.symm X ∈ positiveOverlaps D (t • (1 - D)) := by
        refine ⟨map_nonneg e.symm hX.1, ?_, ?_⟩
        · simpa only [← hD, e.symm_apply_apply] using hm' hX.2.1
        · simpa only [← hB, e.symm_apply_apply] using hm' hX.2.2
      have hh := h (e.symm X) hx
      have hxtr : (V * e.symm X).trace = (W * X).trace := by
        rw [← htrace (V * e.symm X), map_mul, e.apply_symm_apply, e.apply_symm_apply]
      have hytr : (V * Y).trace = (W * canonicalOverlap C t).trace := by
        rw [← htrace (V * Y), map_mul, e.apply_symm_apply, hY]
      simpa only [hxtr, hytr] using hh
  have hdiag := diagonal_optimal_iff d (eigenvalue_bounds C hC hC1) V hV t ht
  dsimp only at hdiag
  rw [hopt, hdiag]
  have hp : thresholdPositive C t =
      e (diagonal (fun i => ((max (d i - t * (1 - d i)) 0 : ℝ) : ℂ))) := by
    rw [thresholdPositive, hH.cfc_eq]
    rfl
  have hn : thresholdNegative C t =
      e (diagonal (fun i => ((max (t * (1 - d i) - d i) 0 : ℝ) : ℂ))) := by
    rw [thresholdNegative, hH.cfc_eq]
    rfl
  rw [hp, hn, ← hF, show W = e V from (e.apply_symm_apply W).symm,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    have hh := congrArg (fun Z : Matrix n n ℂ => e.symm Z) h
    simpa only [e.symm_apply_apply, map_zero, F] using hh

/-- The exact all-threshold criterion on the common interior corner of a
singular positive contraction. Only the compressed weight must be faithful. -/
theorem common_all_thresholds_iff_commute (C W : Matrix n n ℂ)
    (hC : C.PosSemidef) (hC1 : C ≤ 1) (hWH : W.IsHermitian)
    (hW : ((interiorEmbedding hC.isHermitian)ᴴ * W *
      interiorEmbedding hC.isHermitian).PosDef) :
    let P := interiorProjection C
    (∀ t : ℝ, 0 < t → ∀ X ∈ positiveOverlaps C (t • (1 - C)),
      (W * X).trace.re ≤ (W * canonicalOverlap C t).trace.re) ↔
      (P * W * P) * (P * C * P) = (P * C * P) * (P * W * P) := by
  dsimp only
  let P := interiorProjection C
  let R := P * W * P
  have hPP : P * P = P := by
    dsimp only [P, interiorProjection]
    rw [← cfc_mul _ _ C (C.finite_real_spectrum.continuousOn _)
      (C.finite_real_spectrum.continuousOn _)]
    apply cfc_congr
    intro x _
    dsimp only
    split_ifs <;> norm_num
  have hPC : P * C = C * P := by
    have hh := (cfc_commute_cfc (fun x : ℝ => if 0 < x ∧ x < 1 then 1 else 0)
      (fun x : ℝ => x) C).eq
    simpa only [P, interiorProjection, cfc_id' ℝ C hC.isHermitian.isSelfAdjoint] using hh
  have hRP : R * P = R := by simp only [R, Matrix.mul_assoc, hPP]
  have hPR : P * R = R := by simp only [R, ← Matrix.mul_assoc, hPP]
  have hleft : R * (P * C * P) = R * C := by
    calc
      _ = R * P * C * P := by simp only [Matrix.mul_assoc]
      _ = R * (C * P) := by rw [hRP, Matrix.mul_assoc]
      _ = R * (P * C) := by rw [hPC]
      _ = R * C := by rw [← Matrix.mul_assoc, hRP]
  have hright : (P * C * P) * R = C * R := by
    calc
      _ = P * C * (P * R) := by rw [Matrix.mul_assoc]
      _ = C * P * R := by rw [hPR, hPC]
      _ = C * R := by rw [Matrix.mul_assoc, hPR]
  change _ ↔ R * (P * C * P) = (P * C * P) * R
  rw [hleft, hright]
  have he := all_common_thresholds_iff_commute C W hC.isHermitian hWH
  dsimp only at he
  rw [← he]
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro ht
  exact common_canonical_optimal_iff C W hC hC1 hW t ht

end D5.S3.Quantum.Divergence.MaximalHockeyStickSingularCriterion
