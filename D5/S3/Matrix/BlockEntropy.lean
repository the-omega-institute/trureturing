/- GID: D5/S3/Matrix/BlockEntropy
   generality: G
   mirror-B: none(waiver:covered-by-petz-qutrit-second-flag-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Energy-block compression and strict Klein inequality for finite complex matrices. -/

module

public import OmegaBuild.Commands
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Tactic.NoncommRing

/-!
Omega original.

Energy-block compression and strict Klein inequality for finite complex matrices.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
@[expose] public section

namespace Omega.Matrix.BlockEntropy

open _root_.Matrix _root_.MeasureTheory Set
open scoped _root_.Matrix ComplexOrder MatrixOrder CStarAlgebra Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The fixed-energy matrix blocks, with all entries across distinct energies erased. -/
def energyPinching (E : n → ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => if E i = E j then A i j else 0

def energyDiagonal (E : n → ℝ) : Matrix n n ℂ :=
  diagonal (fun i => (E i : ℂ))

theorem energyPinching_eq_self_iff (E : n → ℝ) (A : Matrix n n ℂ) :
    energyPinching E A = A ↔ Commute A (energyDiagonal E) := by
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    rw [energyDiagonal, mul_diagonal, diagonal_mul]
    by_cases hE : E i = E j
    · rw [hE, mul_comm]
    · have hz : A i j = 0 := by simpa [energyPinching, hE] using (congrFun (congrFun h i) j).symm
      simp [hz]
  · intro h
    ext i j
    by_cases hE : E i = E j
    · simp [energyPinching, hE]
    · have hh := congrFun (congrFun h.eq i) j
      simp only [energyDiagonal, mul_diagonal, diagonal_mul] at hh
      have hh := sub_eq_zero.mpr hh
      rw [← mul_comm (A i j) _, ← mul_sub] at hh
      have hne : ((E j : ℂ) - (E i : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hE)
      simp [energyPinching, hE, (mul_eq_zero.mp hh).resolve_right hne]

def energyProjection (E : n → ℝ) (e : ℝ) : Matrix n n ℂ :=
  diagonal fun i => if E i = e then 1 else 0

private theorem pinching_sum (E : n → ℝ) (A : Matrix n n ℂ) :
    energyPinching E A = ∑ e ∈ Finset.univ.image E,
      energyProjection E e * A * energyProjection E e := by
  ext i j
  simp only [Matrix.sum_apply, energyProjection, mul_diagonal, diagonal_mul]
  by_cases hE : E i = E j
  · rw [Finset.sum_eq_single_of_mem (E i) (by simp)]
    · simp [energyPinching, hE]
    · intro e _ he
      simp [Ne.symm he]
  · simp [energyPinching, hE]

omit [Fintype n] in
private theorem energyProjection_hermitian (E : n → ℝ) (e : ℝ) :
    (energyProjection E e).IsHermitian := by
  unfold energyProjection
  rw [Matrix.IsHermitian, diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : E i = e <;> simp [h]

omit [Fintype n] [DecidableEq n] in
theorem pinching_pos [Finite n] (E : n → ℝ) {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (energyPinching E A).PosSemidef := by
  classical
  let _ := Fintype.ofFinite n
  rw [pinching_sum]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply Finset.sum_nonneg
  intro e _
  simpa only [(energyProjection_hermitian E e).eq] using
    (hA.mul_mul_conjTranspose_same (energyProjection E e)).nonneg

private theorem energyProjection_sum (E : n → ℝ) :
    (∑ e ∈ Finset.univ.image E, energyProjection E e) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [energyProjection, Matrix.sum_apply, one_apply]
  · simp [energyProjection, Matrix.sum_apply, h, one_apply]

omit [DecidableEq n] in
theorem pinching_kernel (E : n → ℝ) {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (x : n → ℂ) (hx : energyPinching E A *ᵥ x = 0) : A *ᵥ x = 0 := by
  classical
  have hc (e : ℝ) : star x ⬝ᵥ ((energyProjection E e * A * energyProjection E e) *ᵥ x) =
      star (energyProjection E e *ᵥ x) ⬝ᵥ (A *ᵥ (energyProjection E e *ᵥ x)) := by
    calc
      _ = star x ⬝ᵥ (((energyProjection E e)ᴴ * A * energyProjection E e) *ᵥ x) := by
        rw [(energyProjection_hermitian E e).eq]
      _ = _ := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
  have hs := congrArg (fun y => star x ⬝ᵥ y) hx
  simp only [pinching_sum, sum_mulVec, dotProduct_sum, dotProduct_zero, hc] at hs
  have hz (e : ℝ) (he : e ∈ Finset.univ.image E) :
      A *ᵥ (energyProjection E e *ᵥ x) = 0 :=
    hA.dotProduct_mulVec_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => hA.dotProduct_mulVec_nonneg (energyProjection E t *ᵥ x))).mp hs e he)
  rw [← one_mulVec x, ← energyProjection_sum E, sum_mulVec, mulVec_sum]
  exact Finset.sum_eq_zero hz

theorem trace_pinching_mul (E : n → ℝ) (A L : Matrix n n ℂ)
    (hL : Commute L (energyDiagonal E)) :
    (energyPinching E A * L).trace = (A * L).trace := by
  have hf := (energyPinching_eq_self_iff E L).mpr hL
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : E i = E j
  · simp [energyPinching, h]
  · have hz : L j i = 0 := by
      simpa [energyPinching, Ne.symm h] using (congrFun (congrFun hf j) i).symm
    simp [hz]

private def overlap (W : Matrix n n ℂ) : Matrix n n ℝ := fun i j => ‖W i j‖ ^ 2

private theorem overlap_doublyStochastic {W : Matrix n n ℂ} (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    overlap W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrArg (fun A : Matrix n n ℂ => (A i i).re) (Unitary.mul_star_self_of_mem hW)
    simpa [overlap, Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
      Complex.mul_conj', ← Complex.ofReal_pow, Matrix.one_apply] using h
  · have h := congrArg (fun A : Matrix n n ℂ => (A j j).re) (Unitary.star_mul_self_of_mem hW)
    simpa [overlap, Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
      Complex.conj_mul', ← Complex.ofReal_pow, Matrix.one_apply] using h

/-- The strict scalar entropy gap, with the convention that zero times log zero is zero. -/
def kleinGap (r : ℝ) : ℝ := r * Real.log r - r + 1

theorem kleinGap_continuous : Continuous kleinGap :=
  (Real.continuous_mul_log.sub continuous_id).add continuous_const

theorem kleinGap_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ kleinGap r := by
  unfold kleinGap
  linarith [Real.self_sub_one_le_mul_log hr]

theorem kleinGap_eq_zero_iff {r : ℝ} (hr : 0 ≤ r) : kleinGap r = 0 ↔ r = 1 := by
  constructor
  · intro h
    by_contra hr'
    have hs := Real.self_sub_one_lt_mul_log hr hr'
    unfold kleinGap at h
    linarith
  · rintro rfl
    simp [kleinGap]

theorem measurable_matrix_cfc (f : ℝ → ℝ) (hf : Continuous f) :
    Measurable (cfc f : Matrix n n ℂ → Matrix n n ℂ) := by
  let s : Set (Matrix n n ℂ) := {A | IsSelfAdjoint A}
  have hs : IsClosed s := isClosed_eq continuous_star continuous_id
  have hc : ContinuousOn (cfc f : Matrix n n ℂ → Matrix n n ℂ) s := by
    refine ContinuousOn.cfc
      (s := fun A : Matrix n n ℂ => Metric.closedBall 0 ((‖A‖ + 1) * ‖(1 : Matrix n n ℂ)‖)) f
      (fun _ _ => isCompact_closedBall _ _) continuous_id.continuousOn ?_ (fun _ h => h)
      (fun _ _ => hf.continuousOn)
    intro A hA
    have hb : ∀ᶠ B : Matrix n n ℂ in nhdsWithin A s, ‖B‖ < ‖A‖ + 1 :=
      (continuous_norm.continuousWithinAt : ContinuousWithinAt (fun B : Matrix n n ℂ => ‖B‖)
        s A).eventually (gt_mem_nhds (lt_add_one ‖A‖))
    filter_upwards [hb] with B hB
    exact (spectrum.subset_closedBall_norm_mul B).trans
      (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_right hB.le (norm_nonneg _)))
  classical
  have hz : ∀ A ∉ s, cfc f A = (0 : Matrix n n ℂ) := fun _ h =>
    cfc_apply_of_not_predicate _ h
  have hpiece := hc.measurable_piecewise
    (continuousOn_const (c := (0 : Matrix n n ℂ))) hs.measurableSet
  convert hpiece using 1
  funext A
  by_cases hA : A ∈ s
  · simp [hA]
  · simp [hA, hz A hA]

theorem cfc_kleinGap_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (cfc kleinGap A).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg fun r hr => kleinGap_nonneg (spectrum_nonneg_of_nonneg
    (Matrix.nonneg_iff_posSemidef.mpr hA) hr)

theorem cfc_kleinGap_eq_zero {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    cfc kleinGap A = 0 ↔ A = 1 := by
  have ha : IsSelfAdjoint A := hA.isHermitian.isSelfAdjoint
  calc
    cfc kleinGap A = 0 ↔ (spectrum ℝ A).EqOn kleinGap 0 := by
      rw [← cfc_zero ℝ A]
      exact cfc_eq_cfc_iff_eqOn (a := A) (f := kleinGap) (g := 0)
        ha kleinGap_continuous.continuousOn (by fun_prop)
    _ ↔ (spectrum ℝ A).EqOn id 1 := by
      exact forall_congr' fun r => forall_congr' fun hr => kleinGap_eq_zero_iff
        (spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hA) hr)
    _ ↔ A = 1 := by
      rw [← cfc_eq_cfc_iff_eqOn (a := A) (f := id) (g := 1)
        ha continuous_id.continuousOn (by fun_prop)]
      change (cfc (fun r : ℝ => r) A = cfc 1 A) ↔ A = 1
      rw [cfc_id' ℝ A ha, cfc_one ℝ A ha]

private theorem scalarKlein (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * (Real.log a - Real.log b) - a + b ∧
      (a * (Real.log a - Real.log b) - a + b = 0 ↔ a = b) := by
  by_cases haz : a = 0
  · subst a
    simp [hb.le, hb.ne, hb.ne']
  · have hlog := Real.log_div haz hb.ne'
    have hmult : b * kleinGap (a / b) =
        a * (Real.log a - Real.log b) - a + b := by
      rw [kleinGap, hlog]
      field_simp
    rw [← hmult]
    have hd : 0 ≤ a / b := div_nonneg ha hb.le
    refine ⟨mul_nonneg hb.le (kleinGap_nonneg hd), ?_⟩
    rw [mul_eq_zero, or_iff_right hb.ne', kleinGap_eq_zero_iff hd, div_eq_one_iff_eq hb.ne']

private theorem spectral_log (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    CFC.log A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => (Real.log (hA.eigenvalues i) : ℂ)) *
        star (hA.eigenvectorUnitary : Matrix n n ℂ) := by
  rw [CFC.log, hA.cfc_eq]
  rfl

/-- Strict trace-log Klein inequality for equal-trace positive matrices with
input support contained in the reference support. -/
theorem trace_log_klein (A B : Matrix n n ℂ) (hA₀ : A.PosSemidef) (hB₀ : B.PosSemidef)
    (htrace : A.trace = B.trace) (hsupport : ∀ x, B *ᵥ x = 0 → A *ᵥ x = 0) :
    let d := (A * CFC.log A).trace.re - (A * CFC.log B).trace.re
    0 ≤ d ∧ (d = 0 ↔ A = B) := by
  let hA := hA₀.isHermitian
  let hB := hB₀.isHermitian
  let U : Matrix n n ℂ := hA.eigenvectorUnitary
  let V : Matrix n n ℂ := hB.eigenvectorUnitary
  let a := hA.eigenvalues
  let b := hB.eigenvalues
  let W := star U * V
  let w := overlap W
  have hU : U ∈ Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary.2
  have hV : V ∈ Matrix.unitaryGroup n ℂ := hB.eigenvectorUnitary.2
  have hU₁ := Unitary.mul_star_self_of_mem hU
  have hU₂ := Unitary.star_mul_self_of_mem hU
  have hV₁ := Unitary.mul_star_self_of_mem hV
  have hV₂ := Unitary.star_mul_self_of_mem hV
  have hw := overlap_doublyStochastic
    (Submonoid.mul_mem _ (Unitary.star_mem hU) hV)
  change w ∈ doublyStochastic ℝ n at hw
  let da := diagonal fun i => (a i : ℂ)
  let db := diagonal fun i => (b i : ℂ)
  let la := diagonal fun i => (Real.log (a i) : ℂ)
  let lb := diagonal fun i => (Real.log (b i) : ℂ)
  have hAd : A = U * da * star U := hA.spectral_theorem
  have hBd : B = V * db * star V := hB.spectral_theorem
  have hAlog : CFC.log A = U * la * star U := spectral_log A hA
  have hBlog : CFC.log B = V * lb * star V := spectral_log B hB
  have ha (i : n) : 0 ≤ a i := hA₀.eigenvalues_nonneg i
  have hb (i : n) : 0 ≤ b i := hB₀.eigenvalues_nonneg i
  have hsum : ∑ i, a i = ∑ i, b i := by
    have haTrace : A.trace = ∑ i, (a i : ℂ) := hA.trace_eq_sum_eigenvalues
    have hbTrace : B.trace = ∑ i, (b i : ℂ) := hB.trace_eq_sum_eigenvalues
    rw [haTrace, hbTrace, ← Complex.ofReal_sum, ← Complex.ofReal_sum] at htrace
    exact Complex.ofReal_inj.mp htrace
  have hleft : (A * CFC.log A).trace.re = ∑ i, a i * Real.log (a i) := by
    have hexpr : (U * da * star U) * (U * la * star U) =
        U * (da * (star U * U) * la) * star U := by noncomm_ring
    rw [hAlog, hAd, hexpr, hU₂, Matrix.mul_one, Matrix.trace_mul_cycle, hU₂, one_mul]
    simp [da, la, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  have hright : (A * CFC.log B).trace.re =
      ∑ i, ∑ j, w i j * (a i * Real.log (b j)) := by
    have hexpr : (U * da * star U) * (V * lb * star V) =
        U * (da * W * lb * star W) * star U := by
      simp only [W, star_mul, star_star]
      calc
        _ = U * (da * star U * V * lb * star V) := by noncomm_ring
        _ = U * (da * star U * V * lb * star V) * (U * star U) := by
          rw [hU₁, Matrix.mul_one]
        _ = _ := by noncomm_ring
    rw [hBlog, hAd, hexpr, Matrix.trace_mul_cycle, hU₂, one_mul]
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [da, lb, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply, Complex.star_def]
    rw [show (a i : ℂ) * W i j * (Real.log (b j) : ℂ) * (starRingEnd ℂ) (W i j) =
      (W i j * (starRingEnd ℂ) (W i j)) * ((a i : ℂ) * (Real.log (b j) : ℂ)) by ring]
    simp [w, overlap, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  have hcolA : da * W = star U * A * V := by
    conv_rhs => rw [hAd]
    simp [W, ← Matrix.mul_assoc, hU₂]
  have hcolB : W * db = star U * B * V := by
    conv_rhs => rw [hBd]
    simp [W, Matrix.mul_assoc, hV₂]
  have hz (i j : n) (hbj : b j = 0) : a i = 0 ∨ W i j = 0 := by
    have hvec : B *ᵥ (fun k => V k j) = 0 := by
      have h := hB.mulVec_eigenvectorBasis j
      simpa only [V, Matrix.IsHermitian.eigenvectorUnitary_apply,
        show hB.eigenvalues j = 0 from hbj, zero_smul] using h
    have hvecA := hsupport _ hvec
    have hentry : (star U * A * V) i j = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [show (A * V) k j = 0 from congrFun hvecA k, mul_zero]
    rw [← hcolA, Matrix.diagonal_mul, mul_eq_zero, Complex.ofReal_eq_zero] at hentry
    exact hentry
  let term := fun i j => w i j * (a i * (Real.log (a i) - Real.log (b j)) - a i + b j)
  have hterm (i j : n) : 0 ≤ term i j ∧ (term i j = 0 → W i j ≠ 0 → a i = b j) := by
    by_cases hj : b j = 0
    · rcases hz i j hj with hi | hij
      · simp [term, hj, hi]
      · simp [term, w, overlap, hij]
    · have hk := scalarKlein (a i) (b j) (ha i) (lt_of_le_of_ne (hb j) (Ne.symm hj))
      refine ⟨mul_nonneg (sq_nonneg _) hk.1, fun he hn => hk.2.mp ?_⟩
      exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hn))
  have hrow (f : n → ℝ) : (∑ i, ∑ j, w i j * f i) = ∑ i, f i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hw i, one_mul]
  have hcol (f : n → ℝ) : (∑ i, ∑ j, w i j * f j) = ∑ j, f j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, sum_col_of_mem_doublyStochastic hw j, one_mul]
  have hD : (A * CFC.log A).trace.re - (A * CFC.log B).trace.re =
      ∑ i, ∑ j, term i j := by
    rw [hleft, hright]
    simp only [term, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hrow, hrow, hcol, hsum]
    ring
  refine ⟨hD ▸ Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hterm i j).1)), ?_⟩
  constructor
  · intro h
    rw [hD] at h
    have heq : da * W = W * db := by
      ext i j
      simp only [da, db, Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases hij : W i j = 0
      · simp [hij]
      · have hi := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => Finset.sum_nonneg (fun j _ => (hterm i j).1))).mp h i (Finset.mem_univ i)
        have hj := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => (hterm i j).1)).mp hi j (Finset.mem_univ j)
        rw [(hterm i j).2 hj hij, mul_comm]
    rw [hcolA, hcolB] at heq
    have hAB := congrArg (fun M : Matrix n n ℂ => U * M * star V) heq
    have cancel (M : Matrix n n ℂ) :
        U * (star U * M * V) * star V = M := by
      calc
        _ = (U * star U) * M * (V * star V) := by noncomm_ring
        _ = _ := by rw [hU₁, hV₁, one_mul, Matrix.mul_one]
    simp only [cancel] at hAB
    exact hAB
  · rintro rfl
    simp


/-- Evaluate each equal-energy block at its own physical clock coordinate. -/
def shiftedEnergyDensity (E : n → ℝ) (scale : ℝ → ℝ → ℝ)
    (A : ℝ → Matrix n n ℂ) (y : ℝ) : Matrix n n ℂ :=
  fun i j => if E i = E j ∧ E i ≤ y then scale (E i) (y - E i) • A (y - E i) i j else 0

omit [Fintype n] [DecidableEq n] in
/-- Shifting and scaling the orthogonal energy blocks preserves positivity. -/
theorem shiftedEnergyDensity_pos [Finite n] (E : n → ℝ) (scale : ℝ → ℝ → ℝ)
    (A : ℝ → Matrix n n ℂ) (hscale : ∀ e x, 0 ≤ scale e x)
    (hA : ∀ x, (A x).PosSemidef) (y : ℝ) :
    (shiftedEnergyDensity E scale A y).PosSemidef := by
  classical
  let _ := Fintype.ofFinite n
  let F (e : ℝ) : Matrix n n ℂ := if e ≤ y then
    scale e (y - e) • ((energyProjection E e)ᴴ * A (y - e) * energyProjection E e) else 0
  have hEq : shiftedEnergyDensity E scale A y = ∑ e ∈ Finset.univ.image E, F e := by
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single_of_mem (E i) (by simp)]
    · by_cases hij : E i = E j
      · by_cases hiy : E i ≤ y <;> simp [F, energyProjection, mul_diagonal, diagonal_mul,
          shiftedEnergyDensity, ← hij, hiy]
      · by_cases hiy : E i ≤ y <;> simp [F, energyProjection, mul_diagonal, diagonal_mul,
          shiftedEnergyDensity, hij, Ne.symm hij, hiy]
    · intro k _ hk
      by_cases hky : k ≤ y <;> simp [F, energyProjection,
        mul_diagonal, diagonal_mul, Ne.symm hk, hky]
  rw [hEq, ← Matrix.nonneg_iff_posSemidef]
  apply Finset.sum_nonneg
  intro e _
  by_cases hy : e ≤ y
  · simpa only [F, ite_eq_left hy, Matrix.nonneg_iff_posSemidef] using
      ((hA (y - e)).conjTranspose_mul_mul_same (energyProjection E e)).smul (hscale e (y - e))
  · simp [F, hy]

/-- Each shifted block lies in the active part of the total-energy fiber. -/
theorem shiftedEnergyDensity_compressed (E : n → ℝ) (scale : ℝ → ℝ → ℝ)
    (A : ℝ → Matrix n n ℂ) (y : ℝ) :
    let P := diagonal fun i => if E i ≤ y then (1 : ℂ) else 0
    P * shiftedEnergyDensity E scale A y * P = shiftedEnergyDensity E scale A y := by
  dsimp only
  ext i j
  simp only [mul_diagonal, diagonal_mul, shiftedEnergyDensity]
  by_cases he : E i = E j
  · by_cases hy : E i ≤ y <;> simp [← he, hy]
  · simp [he]


omit [Fintype n] [DecidableEq n] in
/-- Matrix entries of translated Borel energy blocks are Borel functions. -/
theorem measurable_shiftedEnergyDensity (E : n → ℝ) (scale : ℝ → ℝ → ℝ)
    (A : ℝ → Matrix n n ℂ) (hs : ∀ e, Measurable (scale e))
    (hA : Measurable A) : Measurable (shiftedEnergyDensity E scale A) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hij : E i = E j
  · simp only [shiftedEnergyDensity, and_iff_right hij]
    have h : Measurable (fun y : ℝ => y - E i) := by fun_prop
    have hentry : Measurable (fun x => A x i j) := hA.eval_matrix
    exact ((hs (E i)).comp h |>.smul (hentry.comp h)).piecewise measurableSet_Ici measurable_const
  · simp [shiftedEnergyDensity, hij]

/-- The padded total-energy density intertwines each active energy block with its
physical-clock density and each inactive block with the identity. -/
theorem shiftedEnergyDensity_padded_intertwine (E : n → ℝ) (scale : ℝ → ℝ → ℝ)
    (A : ℝ → Matrix n n ℂ) (hoff : ∀ x i j, E i ≠ E j → A x i j = 0) (y : ℝ) (i : n) :
    (shiftedEnergyDensity E scale A y +
      (1 - diagonal (fun j => if E j ≤ y then (1 : ℂ) else 0))) * energyProjection E (E i) =
      energyProjection E (E i) *
        (if E i ≤ y then scale (E i) (y - E i) • A (y - E i) else 1) := by
  ext j k
  simp only [energyProjection, mul_diagonal, diagonal_mul, Matrix.add_apply]
  by_cases hjk : j = k
  · subst k
    by_cases hj : E j = E i <;> by_cases hy : E i ≤ y <;>
      simp [shiftedEnergyDensity, hj, hy]
  · by_cases hj : E j = E i <;> by_cases hk : E k = E i
    · by_cases hy : E i ≤ y <;> simp [shiftedEnergyDensity, hj, hk, hy,
        Matrix.one_apply_ne hjk, diagonal_apply_ne _ hjk]
    · have hne : E j ≠ E k := fun h => hk (h.symm.trans hj)
      by_cases hy : E i ≤ y <;> simp [shiftedEnergyDensity, hj, hk, hy,
        Matrix.one_apply_ne hjk, hoff _ j k hne]
    · simp [shiftedEnergyDensity, hj, hk, Matrix.one_apply_ne hjk, diagonal_apply_ne _ hjk]
    · simp [hj, hk]

def xlogx (r : ℝ) := r * Real.log r

theorem cfc_xlogx_smul (A : Matrix n n ℂ) (hA : A.IsHermitian) (s : ℝ) :
    cfc xlogx (s • A) = s • cfc xlogx A + (s * Real.log s) • A := by
  have hx : Continuous xlogx := Real.continuous_mul_log
  have hf : Continuous (fun r : ℝ => s • xlogx r) := hx.const_smul s
  have hg : Continuous (fun r : ℝ => (s * Real.log s) • r) := by
    change Continuous (fun r : ℝ => (s * Real.log s) * r)
    fun_prop
  rw [← cfc_comp_smul s xlogx A hx.continuousOn hA.isSelfAdjoint,
    ← cfc_smul s xlogx A hx.continuousOn,
    ← cfc_smul_id (R := ℝ) (s * Real.log s) A hA.isSelfAdjoint,
    ← cfc_add A _ _ hf.continuousOn hg.continuousOn]
  have hs : Continuous (fun r : ℝ => s • r) := by
    change Continuous (fun r : ℝ => s * r)
    fun_prop
  apply (cfc_eq_cfc_iff_eqOn hA.isSelfAdjoint
    (hx.comp hs).continuousOn (hf.add hg).continuousOn).mpr
  intro r _
  change xlogx (s * r) = s * xlogx r + (s * Real.log s) * r
  unfold xlogx
  by_cases hs : s = 0
  · simp [hs]
  by_cases hr : r = 0
  · simp [hr]
  rw [Real.log_mul hs hr]
  ring

theorem xlogx_eq_trace_log (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    cfc xlogx A = A * CFC.log A := by
  change cfc (fun r : ℝ => id r * Real.log r) A = _
  rw [CFC.log, cfc_mul id Real.log A continuous_id.continuousOn
    ((Set.toFinite (spectrum ℝ A)).continuousOn _)]
  change cfc (fun r : ℝ => r) A * cfc Real.log A = _
  rw [cfc_id' ℝ A hA.isSelfAdjoint]

theorem xlogx_weighted_diagonal (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {p q w : ℝ} (hq : 0 < q) (hw : 0 < w) (i : n) :
    q * w * (cfc xlogx ((p / q / w) • A) i i).re =
      p * ((cfc xlogx A i i).re + (Real.log (p / q) - Real.log w) * (A i i).re) := by
  rw [cfc_xlogx_smul A hA (p / q / w)]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  by_cases hp : p = 0
  · simp [hp]
  rw [Real.log_div (div_ne_zero hp hq.ne') hw.ne']
  field_simp

omit [DecidableEq n] in
theorem density_diagonal_abs_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace.re = 1) (i : n) : |(A i i).re| ≤ 1 := by
  have hpos (j : n) : 0 ≤ (A j j).re := (Complex.le_def.mp hA.diag_nonneg).1
  rw [abs_of_nonneg (hpos i), ← htr]
  simpa only [Matrix.trace, Matrix.diag, Complex.re_sum] using
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hpos j) (Finset.mem_univ i))

theorem density_log_diagonal_abs_le_one {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (htr : A.trace.re = 1) (i : n) :
    |(cfc xlogx A i i).re| ≤ 1 := by
  let f := xlogx
  have he : ∑ j, hA.isHermitian.eigenvalues j = 1 := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues] at htr
    change (∑ j, (hA.isHermitian.eigenvalues j : ℂ)).re = 1 at htr
    simpa only [Complex.re_sum, Complex.ofReal_re] using htr
  have hr (r : ℝ) (h : r ∈ spectrum ℝ A) : 0 ≤ r ∧ r ≤ 1 := by
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at h
    obtain ⟨j, rfl⟩ := h
    exact ⟨hA.eigenvalues_nonneg j, he ▸
      Finset.single_le_sum (fun k _ => hA.eigenvalues_nonneg k) (Finset.mem_univ j)⟩
  have hupper : cfc f A ≤ 0 := cfc_nonpos f A fun r h =>
    show xlogx r ≤ 0 from
      mul_nonpos_of_nonneg_of_nonpos (hr r h).1 (Real.log_nonpos (hr r h).1 (hr r h).2)
  have hlower : 0 ≤ cfc f A + 1 := by
    have h := cfc_nonneg (a := A) (f := fun r => f r + 1) fun r h =>
      show 0 ≤ f r + 1 by
        obtain ⟨hp, _⟩ := hr r h
        have hk := Real.self_sub_one_le_mul_log hp
        dsimp [f, xlogx]
        linarith
    rw [cfc_add_const 1 f A Real.continuous_mul_log.continuousOn hA.isHermitian.isSelfAdjoint, map_one] at h
    exact h
  have hu := (Complex.le_def.mp ((Matrix.nonneg_iff_posSemidef.mp (neg_nonneg.mpr hupper)).diag_nonneg
    (i := i))).1
  have hl := (Complex.le_def.mp ((Matrix.nonneg_iff_posSemidef.mp hlower).diag_nonneg (i := i))).1
  simp only [Matrix.neg_apply, Complex.neg_re, Matrix.add_apply, Matrix.one_apply_eq,
    Complex.add_re, Complex.one_re, Complex.zero_re] at hu hl
  change |(cfc f A i i).re| ≤ 1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Finite clock log moment controls each scaled trace-log entry under the clock weight. -/
theorem integrable_weighted_xlogx_diagonal {μ : Measure ℝ}
    (A : ℝ → Matrix n n ℂ) (hA : Measurable A)
    (hpos : ∀ x, (A x).PosSemidef) (htr : ∀ x, (A x).trace.re = 1)
    (p q : ℝ → ℝ) {w : ℝ} (hw : 0 < w) (hq : ∀ x, 0 < q x)
    (hp : Integrable p μ) (hl : Integrable (fun x => p x * Real.log (p x / q x)) μ) (i : n) :
    Integrable (fun x => q x *
      (cfc xlogx ((p x / q x / w) • A x) i i).re) μ := by
  let d := fun x => (A x i i).re
  let e := fun x => (cfc xlogx (A x) i i).re
  have hm (B : ℝ → Matrix n n ℂ) (hB : Measurable B) :
      Measurable fun x => (B x i i).re :=
    Complex.continuous_re.measurable.comp (hB.eval_matrix)
  have hd : AEStronglyMeasurable d μ := (hm A hA).aestronglyMeasurable
  have he : AEStronglyMeasurable e μ :=
    (hm _ ((measurable_matrix_cfc xlogx Real.continuous_mul_log).comp hA)).aestronglyMeasurable
  have hd₁ : ∀ᵐ x ∂μ, ‖d x‖ ≤ 1 := Filter.Eventually.of_forall fun x =>
    by simpa only [Real.norm_eq_abs] using density_diagonal_abs_le_one (hpos x) (htr x) i
  have he₁ : ∀ᵐ x ∂μ, ‖e x‖ ≤ 1 := Filter.Eventually.of_forall fun x =>
    by simpa only [e, Real.norm_eq_abs] using density_log_diagonal_abs_le_one (hpos x) (htr x) i
  have hpe : Integrable (fun x => p x * e x) μ := hp.mul_bdd he he₁
  have hpd : Integrable (fun x => (p x * Real.log (p x / q x)) * d x) μ := hl.mul_bdd hd hd₁
  have hpc : Integrable (fun x => (p x * Real.log w) * d x) μ := (hp.mul_const _).mul_bdd hd hd₁
  refine (((hpe.add hpd).sub hpc).div_const w).congr (Filter.Eventually.of_forall fun x => ?_)
  have hh := xlogx_weighted_diagonal (A x) (hpos x).isHermitian (p := p x) (hq x) hw i
  change (p x * e x + (p x * Real.log (p x / q x)) * d x -
    (p x * Real.log w) * d x) / w =
    q x * (cfc xlogx ((p x / q x / w) • A x) i i).re
  apply (div_eq_iff hw.ne').mpr
  dsimp [d, e]
  linear_combination -hh


/-- The sum of the Gibbs-weighted scaled diagonal entries splits into a clock
logarithm, the trace of xlogx, and the cross term against the diagonal log weights. -/
theorem weighted_xlogx_trace (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (htr : A.trace.re = 1) (w : n → ℝ) (hw : ∀ i, 0 < w i) {p q : ℝ} (hq : 0 < q) :
    (∑ i, q * w i * (cfc xlogx ((p / q / w i) • A) i i).re) =
      p * (Real.log (p / q) + (A * CFC.log A).trace.re -
        (A * diagonal (fun i => (Real.log (w i) : ℂ))).trace.re) := by
  calc
    _ = ∑ i, p * ((cfc xlogx A i i).re + (Real.log (p / q) - Real.log (w i)) * (A i i).re) :=
      Finset.sum_congr rfl fun i _ => xlogx_weighted_diagonal A hA hq (hw i) i
    _ = _ := ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hdiag : (∑ i, (A i i).re) = 1 := by rw [← Complex.re_sum]; exact htr
  have hlog : (∑ i, Real.log (w i) * (A i i).re) =
      (A * diagonal (fun i => (Real.log (w i) : ℂ))).trace.re := by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Matrix.mul_diagonal,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [xlogx_eq_trace_log A hA, ← Complex.re_sum, hdiag, mul_one, hlog]
  change (A * CFC.log A).trace.re + (Real.log (p / q) -
    (A * diagonal (fun i => (Real.log (w i) : ℂ))).trace.re) = _
  ring

end Omega.Matrix.BlockEntropy
