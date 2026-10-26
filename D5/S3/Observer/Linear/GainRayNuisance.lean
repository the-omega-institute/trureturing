/- GID: D5/S3/Observer/Linear/GainRayNuisance
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayNuisance
   mirror-E: none(waiver:trace-kernel-nuisance-geometry)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Center, mathlib/module/Mathlib.LinearAlgebra.Matrix.Rank, mathlib/module/Mathlib.Algebra.MvPolynomial.Funext, mathlib/module/Mathlib.Algebra.Module.Submodule.Union]
   utility: none
   digest: Trace restriction and weighted evaluations identify the nuisance directions of a scalar readout. -/

import D5.S3.Observer.Linear.GainRayHistory
import D5.S3.Observer.CubicGain.FullWorldMeanSpan
import Mathlib.LinearAlgebra.Center
import Mathlib.Algebra.MvPolynomial.Funext
import D5.S3.Quantum.Algebra.GenericLieLength
import D5.S3.Observer.Linear.GainRayMixedGeometry
import D5.S3.Observer.Linear.GainRayWordGeometry
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
noncomputable section
open scoped Matrix
open MeasureTheory
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

/-- Drift consumes a nonzero kernel direction in addition to the d+1 output directions. -/
theorem scalar_identity_read_bound (d : ℕ) (w : List Bool) (C : Readout d w)
    (hb : C.mulVec (fun _ => 1) = 0) (S : Mat) (s : ℝ) (hs : s ≠ 0)
    (he : response d w C S = s • (1 : Matrix _ _ ℝ)) : d+2 ≤ w.length+1 := by
  have hsurj : Function.Surjective C.mulVec := by
    intro y
    refine ⟨(responseMatrix d w S).mulVec (s⁻¹ • y), ?_⟩
    rw [Matrix.mulVec_mulVec]
    change (response d w C S).mulVec (s⁻¹ • y) = y
    rw [he, Matrix.smul_mulVec, Matrix.one_mulVec, smul_inv_smul₀ hs]
  have hr : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi]
    simp
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker C.mulVecLin) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro hz
    have hm : (fun _ : Fin (w.length+1) => (1 : ℝ)) ∈ LinearMap.ker C.mulVecLin := hb
    rw [hz, Submodule.mem_bot] at hm
    have := congrFun hm (⟨0, by omega⟩ : Fin (w.length+1))
    norm_num at this
  have hd := C.mulVecLin.finrank_range_add_finrank_ker
  rw [hr, Module.finrank_pi] at hd
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at hd
  omega

/-- This covers every rank-deficient short word, including empty and pure words. -/
theorem short_word_no_universal_success (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hw : w.length+1 ≤ d+1) (C : Readout d w)
    (hu : ∀ W : World d, Collinear W.coeff (C.mulVec (readings W w))) :
    ∀ W : World d, ¬ Succeeds W w C := by
  intro W hW
  obtain ⟨hb, he⟩ := universal_scalar_identity d hd w C hu
  have hn := successful_scalar_nonzero w C hb he W hW
  have hr := scalar_identity_read_bound d w C hb W.source
    (scalarFunctional d w C W.source) hn (he W.source)
  omega

abbrev ChartPolynomial (d : ℕ) := MvPolynomial (Fin (d+4)) ℝ

/-- Coordinates are x,r, the d+1 ordinary coefficients, and the drift. -/
def chartParameters (d : ℕ) (x r : ℝ) (β : Coeff d) (δ : ℝ) : Fin (d+4) → ℝ :=
  fun i => if h : i.val < 2 then (if i.val = 0 then x else r)
    else if h' : i.val < d+3 then β ⟨i.val-2, by omega⟩ else δ

def chartDenominator (d : ℕ) : ChartPolynomial d :=
  1 + MvPolynomial.X 0 * MvPolynomial.X 1

def chartTracePolynomial (d : ℕ) (A : Mat) : ChartPolynomial d :=
  MvPolynomial.C (A 0 0) + MvPolynomial.C (A 0 1) * MvPolynomial.X 0 +
    MvPolynomial.C (A 1 0) * MvPolynomial.X 1 +
    MvPolynomial.C (A 1 1) * MvPolynomial.X 0 * MvPolynomial.X 1

def chartReadPolynomial (d : ℕ) (w : List Bool) (i : Fin (w.length+1)) : ChartPolynomial d :=
  (∑ k : Fin (d+1), MvPolynomial.C ((i.val : ℝ)^k.val) *
      MvPolynomial.X ⟨k.val+2, by omega⟩) *
    chartTracePolynomial d (acquisition (w.take i.val)) +
      MvPolynomial.X ⟨d+3, by omega⟩ * chartDenominator d

def chartOutputPolynomial (d : ℕ) (w : List Bool) (C : Readout d w)
    (k : Fin (d+1)) : ChartPolynomial d :=
  ∑ i : Fin (w.length+1), MvPolynomial.C (C k i) * chartReadPolynomial d w i

/-- The polynomial is the actual output wedge multiplied by the positive source denominator. -/
def chartWedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (j k : Fin (d+1)) : ChartPolynomial d :=
  MvPolynomial.X ⟨j.val+2, by omega⟩ * chartOutputPolynomial d w C k -
    MvPolynomial.X ⟨k.val+2, by omega⟩ * chartOutputPolynomial d w C j

private theorem parameter_coeff (d : ℕ) (x r : ℝ) (β : Coeff d) (δ : ℝ)
    (k : Fin (d+1)) : chartParameters d x r β δ ⟨k.val+2, by omega⟩ = β k := by
  simp [chartParameters, show ¬k.val+2 < 2 by omega, show k.val+2 < d+3 by omega]

private theorem eval_chart_trace (d : ℕ) (A : Mat) (x r : ℝ) (β : Coeff d) (δ : ℝ) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartTracePolynomial d A) =
      Matrix.trace (A * !![1,r;x,x*r]) := by
  simp [chartTracePolynomial, chartParameters, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem eval_chart_read (d : ℕ) (w : List Bool) (x r : ℝ)
    (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hn : β ≠ 0) (δ : ℝ)
    (i : Fin (w.length+1)) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartReadPolynomial d w i) =
      (1+x*r) * readings (chartWorld d x r hx hr β hn δ) w i := by
  have hd : 1+x*r ≠ 0 := ne_of_gt (show 0 < 1+x*r by positivity)
  simp only [chartReadPolynomial, map_add, map_mul, map_sum, MvPolynomial.eval_C,
    MvPolynomial.eval_X, parameter_coeff, eval_chart_trace]
  have hp : chartParameters d x r β δ ⟨d+3, by omega⟩ = δ := by simp [chartParameters]
  have he : MvPolynomial.eval (chartParameters d x r β δ) (chartDenominator d) = 1+x*r := by
    simp [chartDenominator, chartParameters]
  rw [hp, he]
  simp only [readings, readAt, chartWorld, sourceChart, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, gain, Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]
  rw [show (∑ k : Fin (d+1), (i.val : ℝ)^k.val * β k) =
      ∑ k : Fin (d+1), β k * (i.val : ℝ)^k.val by
        apply Finset.sum_congr rfl; intro k _; ring]
  field_simp
  <;> ring

/-- Evaluation agrees with the literal native output at every legal positive chart point. -/
theorem eval_chart_wedge (d : ℕ) (w : List Bool) (C : Readout d w)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hn : β ≠ 0) (δ : ℝ)
    (j k : Fin (d+1)) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) =
      (1+x*r) * (β j * C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) k -
        β k * C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) j) := by
  simp only [chartWedge, map_sub, map_mul, MvPolynomial.eval_X, parameter_coeff,
    chartOutputPolynomial, map_sum, MvPolynomial.eval_C,
    eval_chart_read d w x r hx hr β hn δ]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [← mul_assoc, mul_comm _ (1+x*r), mul_assoc, ← Finset.mul_sum]
  ring

theorem collinear_of_wedges {d : ℕ} (β v : Coeff d) (hn : β ≠ 0)
    (h : ∀ j k, β j * v k - β k * v j = 0) : Collinear β v := by
  have hex : ∃ j, β j ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hn (funext hh)
  obtain ⟨j, hj⟩ := hex
  refine ⟨v j / β j, ?_⟩
  ext k
  have hh := h j k
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  nlinarith

/-- A nonzero wedge exists precisely when whole-domain universal collinearity fails. -/
theorem chart_wedge_nonzero_iff (d : ℕ) (w : List Bool) (C : Readout d w) :
    (∃ j k, chartWedge d w C j k ≠ 0) ↔
      ¬ (∀ W : World d, Collinear W.coeff (C.mulVec (readings W w))) := by
  constructor
  · rintro ⟨j,k,hp⟩ hall
    apply hp
    apply MvPolynomial.funext_set
      (fun i : Fin (d+4) => if i.val < 2 then Set.Ioi 0 else Set.univ)
      (fun i => by
        split_ifs
        · exact Set.Ioi_infinite 0
        · exact Set.infinite_univ)
    intro a ha
    let x := a 0
    let r := a 1
    let β : Coeff d := fun k => a ⟨k.val+2, by omega⟩
    let δ := a ⟨d+3, by omega⟩
    have hx : 0 < x := by simpa [x] using ha 0 (Set.mem_univ _)
    have hr : 0 < r := by simpa [r] using ha 1 (Set.mem_univ _)
    have he : chartParameters d x r β δ = a := by
      ext i
      dsimp [chartParameters, x, r, β, δ]
      split_ifs with hi hz hi'
      · congr; exact Fin.ext hz.symm
      · have hv : i.val = 1 := by omega
        congr; exact Fin.ext hv.symm
      · exact congrArg a (Fin.ext (by dsimp; omega))
      · exact congrArg a (Fin.ext (by dsimp; omega))
    by_cases hn : β = 0
    · have hj : a ⟨j.val+2, by omega⟩ = 0 := congrFun hn j
      have hk : a ⟨k.val+2, by omega⟩ = 0 := congrFun hn k
      simp [chartWedge, hj, hk]
    · rw [← he, eval_chart_wedge d w C x r hx hr β hn δ]
      obtain ⟨s, hs⟩ := hall (chartWorld d x r hx hr β hn δ)
      change C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) = s • β at hs
      simp only [hs, Pi.smul_apply, smul_eq_mul, map_zero]
      ring
  · intro hn
    by_contra hh
    push_neg at hh
    apply hn
    intro W
    obtain ⟨x,r,hx,hr,he,-,-⟩ := source_chart_exact W.source W.legal
    have hw : W = chartWorld d x r hx hr W.coeff W.nonzero W.drift := by
      cases W
      simp_all [chartWorld]
    rw [hw]
    apply collinear_of_wedges _ _ W.nonzero
    intro j k
    have hv := eval_chart_wedge d w C x r hx hr W.coeff W.nonzero W.drift j k
    rw [hh j k, map_zero] at hv
    exact (mul_eq_zero.mp hv.symm).resolve_left (ne_of_gt (by positivity))

/-- Every actual nonzero success, of either sign, lies in each chart wedge zero set. -/
theorem success_chart_wedge_zero (d : ℕ) (w : List Bool) (C : Readout d w)
    (x r : ℝ) (hx : 0 < x) (hr : 0 < r) (β : Coeff d) (hn : β ≠ 0) (δ : ℝ)
    (hs : Succeeds (chartWorld d x r hx hr β hn δ) w C) (j k : Fin (d+1)) :
    MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) = 0 := by
  rw [eval_chart_wedge d w C x r hx hr β hn δ]
  obtain ⟨s, -, hs⟩ := hs
  change C.mulVec (readings (chartWorld d x r hx hr β hn δ) w) = s • β at hs
  simp only [hs, Pi.smul_apply, smul_eq_mul]
  ring

/-- Actual chart success is contained in a nonzero polynomial zero set of ambient measure zero. -/
theorem chart_success_certificate (d : ℕ) (w : List Bool) (C : Readout d w)
    (hu : ¬ (∀ W : World d, Collinear W.coeff (C.mulVec (readings W w)))) :
    ∃ j k : Fin (d+1), chartWedge d w C j k ≠ 0 ∧
      (∀ x r : ℝ, ∀ hx : 0 < x, ∀ hr : 0 < r, ∀ β : Coeff d, ∀ hn : β ≠ 0,
        ∀ δ : ℝ, Succeeds (chartWorld d x r hx hr β hn δ) w C →
          MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) = 0) ∧
      (∀ᵐ a : Fin (d+4) → ℝ ∂MeasureTheory.volume,
        MvPolynomial.eval a (chartWedge d w C j k) ≠ 0) := by
  obtain ⟨j,k,hp⟩ := (chart_wedge_nonzero_iff d w C).mpr hu
  exact ⟨j,k,hp,fun x r hx hr β hn δ hs =>
      success_chart_wedge_zero d w C x r hx hr β hn δ hs j k,
    D5.S3.Quantum.Algebra.GenericLieLength.ae_mvPolynomial_ne_zero (d+4) _ hp⟩

/-- The trace observation retains the entire auxiliary matrix, without positivity restrictions. -/
def traceObservation (A : Mat) : Mat →ₗ[ℝ] ℝ where
  toFun S := Matrix.trace (A * S)
  map_add' S T := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' a S := by simp [Matrix.mul_smul, Matrix.trace_smul]

private theorem trace_observation_injective : Function.Injective traceObservation := by
  intro A B h
  exact Matrix.ext_iff_trace_mul_right.mpr (fun S => congrArg (fun f : Mat →ₗ[ℝ] ℝ => f S) h)

/-- The representative is computed from the actual zeroth row and original prefixes. -/
def scalarRepresentative (d : ℕ) (w : List Bool) (C : Readout d w) : Mat :=
  ∑ i : Fin (w.length+1), C 0 i • acquisition (w.take i.val)

private theorem scalar_representative_trace (d : ℕ) (w : List Bool) (C : Readout d w) :
    traceObservation (scalarRepresentative d w C) = scalarFunctional d w C := by
  ext S
  simp [traceObservation, scalarRepresentative, scalarFunctional, response,
    responseMatrix, Matrix.mul_apply, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul]

private theorem restriction_zero_iff (ell : Mat →ₗ[ℝ] ℝ) (L A : Mat)
    (hL : traceObservation L = ell) :
    (∀ S : Mat, ell S = 0 → traceObservation A S = 0) ↔ ∃ c : ℝ, A = c • L := by
  constructor
  · intro h
    have hm : traceObservation A ∈ Submodule.span ℝ ({ell} : Set (Mat →ₗ[ℝ] ℝ)) := by
      have hx := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => ell)
        (K := traceObservation A) (by
          rw [iInf_const]
          intro S hS
          exact h S hS)
      simpa using hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨c, trace_observation_injective ?_⟩
    ext S
    have he := congrArg (fun f : Mat →ₗ[ℝ] ℝ => f S) hc
    simpa [traceObservation, Matrix.smul_mul, Matrix.trace_smul, ← hL] using he.symm
  · rintro ⟨c, rfl⟩ S hS
    simp [traceObservation, Matrix.smul_mul, Matrix.trace_smul,
      show Matrix.trace (L*S) = 0 by change traceObservation L S = 0; rw [hL]; exact hS]

/-- A single element of the actual scalar kernel realizes exactly the proportionality zeros. -/
theorem scalar_kernel_source (d : ℕ) (w : List Bool) (C : Readout d w)
    (hell : scalarFunctional d w C ≠ 0) :
    scalarRepresentative d w C ≠ 0 ∧
    (∀ T : Mat, Matrix.trace (scalarRepresentative d w C * T) = scalarFunctional d w C T) ∧
    ∃ S : Mat, scalarFunctional d w C S = 0 ∧
      ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val) * S) = 0 ↔
        ∃ c : ℝ, acquisition (w.take i.val) = c • scalarRepresentative d w C := by
  classical
  let ell := scalarFunctional d w C
  let L := scalarRepresentative d w C
  have hL : traceObservation L = ell := scalar_representative_trace d w C
  have hn : L ≠ 0 := by
    intro hz
    apply hell
    change ell = 0
    rw [← hL, hz]
    ext T
    simp [traceObservation]
  let Q (i : Fin (w.length+1)) : Prop :=
    ∃ c : ℝ, acquisition (w.take i.val) = c • L
  have hex (i : {i : Fin (w.length+1) // ¬ Q i}) :
      ∃ S ∈ LinearMap.ker ell, traceObservation (acquisition (w.take i.val.val)) S ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact i.property ((restriction_zero_iff ell L _ hL).mp hh)
  obtain ⟨S, hS, ha⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
    (LinearMap.ker ell) (fun i : {i : Fin (w.length+1) // ¬ Q i} =>
      traceObservation (acquisition (w.take i.val.val))) hex
  refine ⟨hn, fun T => congrArg (fun f : Mat →ₗ[ℝ] ℝ => f T) hL, S, hS, ?_⟩
  intro i
  constructor
  · intro hz
    by_contra hq
    exact ha ⟨i,hq⟩ hz
  · intro hq
    exact (restriction_zero_iff ell L _ hL).mpr hq S hS


/-- Multiplication by arbitrary clock weights retains exactly the available evaluation rank. -/
theorem weighted_evaluation_rank (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (a : Fin n → ℝ) :
    Matrix.rank (fun i k => a i * t i ^ k.val : Matrix (Fin n) (Fin (d+1)) ℝ) =
      min (Finset.univ.filter (fun i => a i ≠ 0)).card (d+1) := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  let r := min U.card (d+1)
  obtain ⟨K,hKU,hK⟩ := Finset.exists_subset_card_eq (show r ≤ U.card from min_le_left _ _)
  let e : Fin K.card ≃ K := K.equivFin.symm
  let f : Fin K.card → Fin n := fun j => (e j).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have ha (j : Fin K.card) : a (f j) ≠ 0 := (Finset.mem_filter.mp (hKU (e j).property)).2
  let B : Matrix (Fin n) (Fin (d+1)) ℝ := fun i k => a i * t i ^ k.val
  have hs : Function.Surjective (B.submatrix f id).mulVec := by
    intro y
    obtain ⟨β,hβ⟩ := evaluation_surjective d K.card (t ∘ f) (ht.comp hf)
      (by rw [hK]; exact min_le_right _ _) (fun j => y j / a (f j))
    refine ⟨β, ?_⟩
    ext j
    have he := congrFun hβ j
    change (∑ k : Fin (d+1), (a (f j) * t (f j)^k.val) * β k) = y j
    simp only [evaluate, evaluation, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Function.comp_apply] at he
    rw [show (∑ k : Fin (d+1), (a (f j) * t (f j)^k.val) * β k) =
        a (f j) * ∑ k : Fin (d+1), t (f j)^k.val * β k by rw [Finset.mul_sum]; congr 1; ext k; ring,
      he, mul_div_cancel₀ _ (ha j)]
  have hl : r ≤ B.rank := by
    have hr : (B.submatrix f id).rank = K.card := by
      rw [Matrix.rank, LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi]
      simp
    rw [← hK, ← hr]
    exact Matrix.rank_submatrix_le B f id
  apply le_antisymm _ hl
  apply le_min
  · apply Matrix.rank_le_card_of_support_subset B U
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hz
    apply hi
    ext k
    change a i * t i ^ k.val = 0
    rw [hz, zero_mul]
  · exact Matrix.rank_le_width B


private theorem scalar_readout_surjective (d : ℕ) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ)) :
    Function.Surjective C.mulVec := by
  obtain ⟨S,hS⟩ : ∃ S : Mat, ell S ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hell (LinearMap.ext hh)
  intro y
  refine ⟨(responseMatrix d w S).mulVec ((ell S)⁻¹ • y), ?_⟩
  rw [Matrix.mulVec_mulVec]
  change (response d w C S).mulVec ((ell S)⁻¹ • y) = y
  rw [he, Matrix.smul_mulVec, Matrix.one_mulVec, smul_inv_smul₀ hS]

private theorem response_range_le_kernel (d : ℕ) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ))
    (S : Mat) (hS : ell S = 0) :
    LinearMap.range (responseMatrix d w S).mulVecLin ≤ LinearMap.ker C.mulVecLin := by
  rintro _ ⟨β,rfl⟩
  change C.mulVec ((responseMatrix d w S).mulVec β) = 0
  rw [Matrix.mulVec_mulVec]
  change (response d w C S).mulVec β = 0
  rw [he,hS,zero_smul,Matrix.zero_mulVec]

/-- A nowhere-zero nuisance in the scalar kernel forces the exact twice-dimension endpoint. -/
theorem scalar_kernel_endpoint (d : ℕ) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ))
    (hN : w.length+1 ≤ 2*(d+1)) (S : Mat) (hS : ell S = 0)
    (ha : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) :
    w.length+1 = 2*(d+1) ∧
      LinearMap.ker C.mulVecLin = LinearMap.range (responseMatrix d w S).mulVecLin := by
  classical
  have hsurj := scalar_readout_surjective d w C ell hell he
  have hrC : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi]
    simp
  have hdim := C.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_self, mul_one, hrC] at hdim
  have hn : d+1 ≤ w.length+1 := by omega
  have ht : Function.Injective (clocks (w.length+1)) := by
    intro i j h
    apply Fin.ext
    dsimp [clocks] at h
    exact_mod_cast h
  have hrH : Module.finrank ℝ (LinearMap.range (responseMatrix d w S).mulVecLin) = d+1 := by
    have hh := weighted_evaluation_rank d (w.length+1) (clocks (w.length+1)) ht
      (fun i => Matrix.trace (acquisition (w.take i.val)*S))
    have hf : Finset.univ.filter (fun i : Fin (w.length+1) =>
        Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) = Finset.univ := by
      ext i
      simp [ha i]
    change Module.finrank ℝ (LinearMap.range (responseMatrix d w S).mulVecLin) =
      min (Finset.univ.filter (fun i : Fin (w.length+1) =>
        Matrix.trace (acquisition (w.take i.val)*S) ≠ 0)).card (d+1) at hh
    simpa only [hf, Finset.card_univ, Fintype.card_fin, Nat.min_eq_right hn] using hh
  have hle := response_range_le_kernel d w C ell he S hS
  have hbound := Submodule.finrank_mono hle
  refine ⟨by omega, ?_⟩
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

/-- At that endpoint every other scalar-kernel source induces a scalar trace ratio. -/
theorem scalar_kernel_ratios (d : ℕ) (hd : 1 ≤ d) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ))
    (hN : w.length+1 ≤ 2*(d+1)) (S : Mat) (hS : ell S = 0)
    (ha : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) :
    ∀ T : Mat, ell T = 0 → ∀ i j : Fin (w.length+1),
      Matrix.trace (acquisition (w.take i.val)*T) / Matrix.trace (acquisition (w.take i.val)*S) =
      Matrix.trace (acquisition (w.take j.val)*T) / Matrix.trace (acquisition (w.take j.val)*S) := by
  obtain ⟨hend,hker⟩ := scalar_kernel_endpoint d w C ell hell he hN S hS ha
  intro T hT
  apply diagonal_evaluation_rigid d (w.length+1) (by omega) (clocks (w.length+1))
    (by intro i j h; apply Fin.ext; dsimp [clocks] at h; exact_mod_cast h)
  intro p hp
  let β := Polynomial.toFn (d+1) p
  have hpβ : gain d β = p := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have hm := response_range_le_kernel d w C ell he T hT
    (show (responseMatrix d w T).mulVec β ∈ LinearMap.range (responseMatrix d w T).mulVecLin
      from ⟨β,rfl⟩)
  rw [hker] at hm
  obtain ⟨γ,hγ⟩ := hm
  refine ⟨gain d γ, ?_, ?_⟩
  · change (Polynomial.ofFn (d+1) γ).natDegree ≤ d
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ d+1) γ)
  · intro i
    have hresponse (U : Mat) (b : Coeff d) :
        (responseMatrix d w U).mulVec b i =
          Matrix.trace (acquisition (w.take i.val)*U) * (gain d b).eval (clocks (w.length+1) i) := by
      rw [← evaluation_polynomial]
      simp [responseMatrix, Matrix.mulVec, dotProduct, evaluate, evaluation, clocks,
        Finset.mul_sum, mul_assoc]
    have hh := congrFun hγ i
    change (responseMatrix d w S).mulVec γ i = (responseMatrix d w T).mulVec β i at hh
    rw [hresponse, hresponse, hpβ] at hh
    change (gain d γ).eval (clocks (w.length+1) i) =
      (Matrix.trace (acquisition (w.take i.val)*T) / Matrix.trace (acquisition (w.take i.val)*S)) *
        p.eval (clocks (w.length+1) i)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (ha i)).mpr
    simpa [mul_comm] using hh

/-- The endpoint ratio law bounds the actual cumulative matrix span by two. -/
theorem scalar_kernel_span_le_two (d : ℕ) (hd : 1 ≤ d) (w : List Bool) (C : Readout d w)
    (hell : scalarFunctional d w C ≠ 0)
    (he : ∀ T : Mat, response d w C T = scalarFunctional d w C T • (1 : Matrix _ _ ℝ))
    (hN : w.length+1 ≤ 2*(d+1)) (S : Mat) (hS : scalarFunctional d w C S = 0)
    (ha : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) ≤ 2 := by
  let i0 : Fin (w.length+1) := ⟨0,by omega⟩
  let A0 := acquisition (w.take i0.val)
  let L := scalarRepresentative d w C
  let K := Submodule.span ℝ ({L,A0} : Set Mat)
  have hle : Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let r := Matrix.trace (acquisition (w.take i.val)*S) / Matrix.trace (A0*S)
    have hvan : ∀ T : Mat, scalarFunctional d w C T = 0 →
        traceObservation (acquisition (w.take i.val) - r • A0) T = 0 := by
      intro T hT
      have hh := scalar_kernel_ratios d hd w C _ hell he hN S hS ha T hT i i0
      dsimp [i0] at hh
      dsimp [traceObservation]
      rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul]
      change Matrix.trace (acquisition (w.take i.val)*T) -
        (Matrix.trace (acquisition (w.take i.val)*S) / Matrix.trace (A0*S)) *
        Matrix.trace (A0*T) = 0
      have hi := ha i
      have h0 := ha i0
      change Matrix.trace (acquisition (w.take i.val)*T) /
          Matrix.trace (acquisition (w.take i.val)*S) =
        Matrix.trace (A0*T) / Matrix.trace (A0*S) at hh
      change Matrix.trace (A0*S) ≠ 0 at h0
      field_simp [hi,h0] at hh ⊢
      nlinarith
    obtain ⟨c,hc⟩ := (restriction_zero_iff _ L _ (scalar_representative_trace d w C)).mp hvan
    have hx : acquisition (w.take i.val) = c • L + r • A0 := by
      rw [← hc]
      module
    change acquisition (w.take i.val) ∈ K
    rw [hx]
    exact K.add_mem (K.smul_mem _ (Submodule.subset_span (by simp)))
      (K.smul_mem _ (Submodule.subset_span (by simp)))
  have hb : Module.finrank ℝ K ≤ 2 := by
    have hh := finrank_span_le_card (R := ℝ) ({L,A0} : Set Mat)
    apply hh.trans
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  exact (Submodule.finrank_mono hle).trans hb


/-- Every mixed Boolean word is obstructed through twice the whole coefficient dimension. -/
theorem mixed_scalar_obstruction (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hM : false ∈ w) (hJ : true ∈ w) (hN : w.length+1 ≤ 2*(d+1))
    (C : Readout d w) (hb : C.mulVec (fun _ => 1) = 0)
    (he : ∀ T : Mat, response d w C T = scalarFunctional d w C T • (1 : Matrix _ _ ℝ)) :
    scalarFunctional d w C = 0 := by
  classical
  by_contra hell
  obtain ⟨hL,htrace,S,hS,hpattern⟩ := scalar_kernel_source d w C hell
  let a : Fin (w.length+1) → ℝ := fun i => Matrix.trace (acquisition (w.take i.val)*S)
  let Q : Finset (Fin (w.length+1)) := Finset.univ.filter (fun i => a i = 0)
  have hq : Q.card ≤ d+1 := by
    have hQ : Q = Finset.univ.filter (fun i : Fin (w.length+1) =>
        ∃ c : ℝ, acquisition (w.take i.val) = c • scalarRepresentative d w C) := by
      ext i
      simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and,a,hpattern]
    rw [hQ]
    exact (cumulative_proportionality_card w _).trans (by omega)
  by_cases hq0 : Q.card = 0
  · have ha : ∀ i : Fin (w.length+1), a i ≠ 0 := by
      intro i hz
      have hm : i ∈ Q := by simp [Q,hz]
      rw [Finset.card_eq_zero.mp hq0] at hm
      exact Finset.notMem_empty _ hm
    have hh := scalar_kernel_span_le_two d hd w C hell he hN S hS ha
    have hthree := mixed_cumulative_span w hM hJ
    omega
  · obtain ⟨i0,hi0⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
    have hz : a i0 = 0 := (Finset.mem_filter.mp hi0).2
    have hsurj := scalar_readout_surjective d w C _ hell he
    have hrC : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
      rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,Module.finrank_pi]
      simp
    have hdim := C.mulVecLin.finrank_range_add_finrank_ker
    simp only [hrC,Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] at hdim
    let H := LinearMap.range (responseMatrix d w S).mulVecLin
    let K := LinearMap.ker C.mulVecLin
    have hle : H ≤ K := response_range_le_kernel d w C _ he S hS
    have hnot : (fun _ : Fin (w.length+1) => (1 : ℝ)) ∉ H := by
      rintro ⟨β,hβ⟩
      have hh := congrFun hβ i0
      have hzero : Matrix.trace (acquisition (w.take i0.val)*S) = 0 := hz
      simp [responseMatrix,Matrix.mulVec,dotProduct,hzero] at hh
    have hlt : H < K := lt_of_le_of_ne hle (by
      intro heq
      apply hnot
      rw [heq]
      exact hb)
    have hstrict := Submodule.finrank_lt_finrank_of_lt hlt
    have ht : Function.Injective (clocks (w.length+1)) := by
      intro i j h
      apply Fin.ext
      dsimp [clocks] at h
      exact_mod_cast h
    have hr := weighted_evaluation_rank d (w.length+1) (clocks (w.length+1)) ht a
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (w.length+1) => a i = 0)
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    change Q.card + (Finset.univ.filter (fun i : Fin (w.length+1) => a i ≠ 0)).card = w.length+1 at hc
    change Module.finrank ℝ H = min (Finset.univ.filter (fun i => a i ≠ 0)).card (d+1) at hr
    rw [hr] at hstrict
    dsimp only [K] at hstrict
    omega

/-- For each actually successful mixed pair, a genuine nonzero native chart polynomial exists. -/
theorem mixed_chart_success_certificate (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hM : false ∈ w) (hJ : true ∈ w) (hN : w.length+1 ≤ 2*(d+1))
    (C : Readout d w) (W : World d) (hW : Succeeds W w C) :
    ∃ j k : Fin (d+1), chartWedge d w C j k ≠ 0 ∧
      (∀ x r : ℝ, ∀ hx : 0 < x, ∀ hr : 0 < r, ∀ β : Coeff d, ∀ hn : β ≠ 0,
        ∀ δ : ℝ, Succeeds (chartWorld d x r hx hr β hn δ) w C →
          MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) = 0) ∧
      (∀ᵐ a : Fin (d+4) → ℝ ∂MeasureTheory.volume,
        MvPolynomial.eval a (chartWedge d w C j k) ≠ 0) := by
  apply chart_success_certificate
  intro hu
  obtain ⟨hb,he⟩ := universal_scalar_identity d hd w C hu
  by_cases hshort : w.length+1 ≤ d+1
  · exact short_word_no_universal_success d hd w hshort C hu W hW
  · have hn := successful_scalar_nonzero w C hb he W hW
    have hz := mixed_scalar_obstruction d hd w hM hJ hN C hb he
    exact hn (by rw [hz]; rfl)

end D5.S3.Observer.Linear.GainRay
