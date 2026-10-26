/- GID: D5/S3/Observer/Linear/GainRayScalarIdentity
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayScalarIdentity
   mirror-E: none(waiver:whole-source-linear-identity)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Center]
   utility: none
   digest: Whole-source collinearity annihilates drift and extends to a scalar linear identity on all real matrices. -/

import D5.S3.Observer.Linear.GainRaySources
import D5.S3.Observer.CubicGain.FullWorldMeanSpan
import Mathlib.LinearAlgebra.Center

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

private theorem cubic_source_legal (a b : ℝ) (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) :
    LegalSource (D5.S3.Observer.CubicGain.sourceMatrix a b) := by
  have hne : a ≠ 0 := ne_of_gt ha
  have hbe : b ≠ 0 := ne_of_gt hb
  have he : D5.S3.Observer.CubicGain.sourceMatrix a b =
      sourceChart ((1-a)/b) (b/a) := by
    have hi : (1 + (1-a)/b * (b/a))⁻¹ = a := by
      apply inv_eq_of_mul_eq_one_right
      field_simp
      ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sourceChart, D5.S3.Observer.CubicGain.sourceMatrix, hi] <;> field_simp <;> ring
  rw [he]
  exact source_chart_legal _ _ (div_pos (by linarith) hb) (div_pos hb ha)

/-- The original positive rank-one trace-one matrices span the full auxiliary matrix space. -/
theorem legal_source_span : Submodule.span ℝ {P : Mat | LegalSource P} = ⊤ := by
  let K := Submodule.span ℝ {P : Mat | LegalSource P}
  let v : Mat → (Fin 4 → ℝ) := fun P => ![P 0 0, P 1 0, P 0 1, P 1 1]
  let P : Fin 4 → Mat := fun i => D5.S3.Observer.CubicGain.sourceMatrix
    (D5.S3.Observer.CubicGain.FullWorldMeanSpan.sourceR i)
    (D5.S3.Observer.CubicGain.FullWorldMeanSpan.sourceB i)
  have hp (i : Fin 4) : P i ∈ K := by
    obtain ⟨ha, ha', hb⟩ := D5.S3.Observer.CubicGain.FullWorldMeanSpan.source_certificate.1 i
    exact Submodule.subset_span (cubic_source_legal _ _ ha ha' hb)
  apply top_unique
  intro S _
  have hu : IsUnit D5.S3.Observer.CubicGain.FullWorldMeanSpan.programColumns.det := by
    rw [D5.S3.Observer.CubicGain.FullWorldMeanSpan.source_certificate.2]
    norm_num
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr hu) (v S)
  have hs : S = ∑ i : Fin 4, c i • P i := by
    have hh (j : Fin 4) := congrFun hc j
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      first
      | simpa [v, Matrix.mulVec, dotProduct,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.programColumns,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.sourceVector, P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using (hh 0).symm
      | simpa [v, Matrix.mulVec, dotProduct,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.programColumns,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.sourceVector, P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using (hh 1).symm
      | simpa [v, Matrix.mulVec, dotProduct,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.programColumns,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.sourceVector, P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using (hh 2).symm
      | simpa [v, Matrix.mulVec, dotProduct,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.programColumns,
          D5.S3.Observer.CubicGain.FullWorldMeanSpan.sourceVector, P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm] using (hh 3).symm
  rw [hs]
  exact K.sum_mem fun i _ => K.smul_mem _ (hp i)

/-- The matrix of whole-coefficient contributions at every original clock. -/
def responseMatrix (d : ℕ) (w : List Bool) (S : Mat) :
    Matrix (Fin (w.length + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Matrix.trace (acquisition (w.take i.val) * S) * (i.val : ℝ) ^ k.val

/-- Source-linear coefficient response after the fixed readout. -/
def response (d : ℕ) (w : List Bool) (C : Readout d w) :
    Mat →ₗ[ℝ] Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ where
  toFun S := C * responseMatrix d w S
  map_add' S T := by
    have h : responseMatrix d w (S+T) = responseMatrix d w S + responseMatrix d w T := by
      ext i k
      simp [responseMatrix, Matrix.mul_add, Matrix.trace_add, add_mul]
    rw [h, Matrix.mul_add]
  map_smul' a S := by
    have h : responseMatrix d w (a • S) = a • responseMatrix d w S := by
      ext i k
      simp [responseMatrix, Matrix.mul_smul, Matrix.trace_smul, mul_assoc]
    rw [h, Matrix.mul_smul]
    rfl

/-- The scalar functional is a fixed diagonal coordinate of the source-linear response. -/
def scalarFunctional (d : ℕ) (w : List Bool) (C : Readout d w) : Mat →ₗ[ℝ] ℝ where
  toFun S := response d w C S 0 0
  map_add' S T := by simp
  map_smul' a S := by simp

/-- All worlds retain their actual source, whole coefficients and arbitrary drift. -/
theorem output_decomposition {d : ℕ} (W : World d) (w : List Bool) (C : Readout d w) :
    C.mulVec (readings W w) = (response d w C W.source).mulVec W.coeff +
      W.drift • C.mulVec (fun _ => 1) := by
  have hz : readings W w = (responseMatrix d w W.source).mulVec W.coeff +
      W.drift • (fun _ => 1) := by
    ext i
    simp [readings, readAt, responseMatrix, Matrix.mulVec, dotProduct,
      gain, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum, Finset.sum_mul]
    congr 1
    funext j
    ring
  rw [hz, Matrix.mulVec_add, Matrix.mulVec_smul]
  exact congrArg (fun v => v + W.drift • C.mulVec (fun _ => 1))
    (Matrix.mulVec_mulVec W.coeff C (responseMatrix d w W.source))

private theorem collinear_wedge {d : ℕ} {β v : Coeff d} (h : Collinear β v)
    (j k : Fin (d+1)) : β j * v k = β k * v j := by
  obtain ⟨s, rfl⟩ := h
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- An affine map preserving every nonzero coefficient line has zero translation. -/
theorem affine_collinearity_scalar (d : ℕ) (hd : 1 ≤ d) (F : Coeff d →ₗ[ℝ] Coeff d)
    (b : Coeff d)
    (h : ∀ β : Coeff d, β ≠ 0 → ∀ δ : ℝ, Collinear β (F β + δ • b)) :
    b = 0 ∧ ∃ s : ℝ, F = s • LinearMap.id := by
  classical
  have hb : b = 0 := by
    ext k
    let j : Fin (d+1) := if k = 0 then ⟨1, by omega⟩ else 0
    have hjk : j ≠ k := by
      dsimp [j]
      split_ifs with hk
      · subst k; simp
      · exact Ne.symm hk
    let β : Coeff d := Pi.single j 1
    have hn : β ≠ 0 := by
      intro hz
      have := congrFun hz j
      simpa [β] using this
    have h0 := collinear_wedge (h β hn 0) j k
    have h1 := collinear_wedge (h β hn 1) j k
    simp [β, Pi.single_apply, hjk, Ne.symm hjk] at h0 h1
    simp only [Pi.zero_apply]
    linarith
  refine ⟨hb, ?_⟩
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro β hi
  by_cases hn : β = 0
  · exact hi.ne_zero 0 (by simp [hn])
  · obtain ⟨s, hs⟩ := h β hn 0
    simp only [zero_smul, add_zero] at hs
    have he := hi.eq_zero_of_pair' (show s • β = (1 : ℝ) • F β by simpa using hs.symm)
    exact one_ne_zero he.2

/-- Universal collinearity on the original domain implies the full auxiliary scalar identity. -/
theorem universal_scalar_identity (d : ℕ) (hd : 1 ≤ d) (w : List Bool) (C : Readout d w)
    (h : ∀ W : World d, Collinear W.coeff (C.mulVec (readings W w))) :
    C.mulVec (fun _ => 1) = 0 ∧
      ∀ S : Mat, response d w C S = scalarFunctional d w C S • (1 : Matrix _ _ ℝ) := by
  have localScalar (P : Mat) (hP : LegalSource P) :
      C.mulVec (fun _ => 1) = 0 ∧ ∃ s : ℝ, response d w C P = s • (1 : Matrix _ _ ℝ) := by
    have hf := affine_collinearity_scalar d hd (response d w C P).mulVecLin (C.mulVec (fun _ => 1))
      (by
        intro β hn δ
        have hh := h (⟨P, hP, β, hn, δ⟩ : World d)
        rw [output_decomposition] at hh
        exact hh)
    refine ⟨hf.1, ?_⟩
    obtain ⟨s, hs⟩ := hf.2
    refine ⟨s, ?_⟩
    apply Matrix.ext_of_mulVec_single
    intro j
    have he := congrArg (fun f : Coeff d →ₗ[ℝ] Coeff d => f (Pi.single j 1)) hs
    ext i
    simpa [Matrix.col, Pi.single_apply, Matrix.one_apply, eq_comm] using congrFun he i
  refine ⟨(localScalar (sourceChart 1 1) (source_chart_legal 1 1 zero_lt_one zero_lt_one)).1, ?_⟩
  let K : Submodule ℝ Mat :=
    LinearMap.ker (response d w C - (scalarFunctional d w C).smulRight (1 : Matrix _ _ ℝ))
  have hk : Submodule.span ℝ {P : Mat | LegalSource P} ≤ K := by
    apply Submodule.span_le.mpr
    intro P hP
    obtain ⟨s, hs⟩ := (localScalar P hP).2
    change response d w C P - scalarFunctional d w C P • (1 : Matrix _ _ ℝ) = 0
    apply sub_eq_zero.mpr
    have hl : scalarFunctional d w C P = s := by
      change response d w C P 0 0 = s
      simp [hs]
    rw [hl]
    exact hs
  rw [legal_source_span] at hk
  intro S
  have hs := hk (show S ∈ (⊤ : Submodule ℝ Mat) from trivial)
  exact sub_eq_zero.mp hs

/-- At an actual successful world the universal scalar has the same nonzero scale. -/
theorem successful_scalar_nonzero {d : ℕ} (w : List Bool) (C : Readout d w)
    (hb : C.mulVec (fun _ => 1) = 0)
    (hs : ∀ S : Mat, response d w C S = scalarFunctional d w C S • (1 : Matrix _ _ ℝ))
    (W : World d) (hW : Succeeds W w C) : scalarFunctional d w C W.source ≠ 0 := by
  obtain ⟨s, hn, he⟩ := hW
  rw [output_decomposition, hb, smul_zero, add_zero, hs, Matrix.smul_mulVec,
    Matrix.one_mulVec] at he
  intro hz
  rw [hz, zero_smul] at he
  exact W.nonzero ((smul_eq_zero.mp he.symm).resolve_left hn)

#print axioms legal_source_span
#print axioms universal_scalar_identity
#print axioms successful_scalar_nonzero
end D5.S3.Observer.Linear.GainRay
