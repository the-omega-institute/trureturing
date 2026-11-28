/- GID: D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.claim; result=D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.result; claim=D5/S3/Quantum/Recovery/GibbsOverlap/PetzIntegerQutritOverlap.claim
   digest: An integer qutrit witness refutes the universal half-time polar overlap lower bound. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import OmegaBuild.Commands

/- Direct frozen dependency: `D5.S3.Quantum.Foundation.FiniteTraceDistance`.
   The matrix-exponential and arithmetic components use pinned Mathlib APIs. -/

/-! # The integer qutrit counterexample to the polar-optimized half-time overlap

`D5.S3.Quantum.Recovery.GibbsOverlap.PetzIntegerQutritOverlap.integer_certificate`
checks the floor table for the product of the two degree-100 Taylor polynomials.
`D5.S3.Quantum.Recovery.GibbsOverlap.PetzIntegerQutritOverlap.rational_certificate`
uses that table to bound each entry of the Taylor product in a rational interval.
-/

compile_only_with_mathlib

set_option autoImplicit false

open scoped BigOperators Matrix Matrix.Norms.Operator Nat NNReal
open NormedSpace

namespace D5.S3.Quantum.Recovery.GibbsOverlap.PetzIntegerQutritOverlap

abbrev Qutrit (R : Type) := Matrix (Fin 3) (Fin 3) R

def AInt : Qutrit ℤ := !![2, 6, -1; 6, 4, 1; -1, 1, 1]

def BInt : Qutrit ℤ := !![-9, -6, 1; -6, -3, -1; 1, -1, 8]

def YInt : Qutrit ℤ := !![-18, -6, 1; -6, -12, -1; 1, -1, -1]

/-- The state at step `n` consists of the power and the factorial-scaled sum. -/
def taylorState (X : Qutrit ℤ) : ℕ → Qutrit ℤ × Qutrit ℤ
  | 0 => (1, 1)
  | n + 1 =>
    let previous := taylorState X n
    let power := previous.1 * X
    (power, (n + 1) • previous.2 + power)

def numerator : Qutrit ℤ := (taylorState AInt 100).2 * (taylorState YInt 100).2

def denominator : ℤ := (100 ! : ℤ) ^ 2

def floorTable : Qutrit ℤ := !![-79877, 108160, -715517; -93751, 126952, -839601; 5, 4, 452]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem integer_certificate (i j : Fin 3) :
    (10000 * numerator i j) / denominator = floorTable i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

section Taylor

variable {E : Type*} [NormedRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E]

/-- The Taylor polynomial containing terms of degrees strictly below `N`. -/
noncomputable def taylor (X : E) (N : ℕ) : E :=
  ∑ n ∈ Finset.range N, (n !⁻¹ : ℝ) • X ^ n

omit [CompleteSpace E] in
private theorem norm_exp_term_le (X : E) {r : ℝ} (hX : ‖X‖ ≤ r) (n : ℕ) :
    ‖(n !⁻¹ : ℝ) • X ^ n‖ ≤ r ^ n / (n ! : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_pow_le X n).trans (pow_le_pow_left₀ (norm_nonneg _) hX _)) (by positivity)

/-- Geometric bound on the Taylor remainder, with first omitted degree `N`. -/
theorem norm_exp_sub_taylor_le (X : E) (N : ℕ) {r : ℝ}
    (hX : ‖X‖ ≤ r) (hr : r < N + 1) :
    ‖exp X - taylor X N‖ ≤ (r ^ N / (N ! : ℝ)) / (1 - r / (N + 1)) := by
  have hr₀ : 0 ≤ r := (norm_nonneg _).trans hX
  let q : ℝ := r / (N + 1)
  have hq₀ : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q < 1 := (div_lt_one (by positivity)).2 hr
  let a : ℕ → ℝ := fun k => r ^ (k + N) / ((k + N)! : ℝ)
  have hstep (k : ℕ) : a (k + 1) ≤ q * a k := by
    have hden : (N : ℝ) + 1 ≤ (k : ℝ) + N + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hratio : r / ((k : ℝ) + N + 1) ≤ q :=
      div_le_div_of_nonneg_left hr₀ (by positivity) hden
    calc
      a (k + 1) = (r / ((k : ℝ) + N + 1)) * a k := by
        dsimp [a]
        rw [show k + 1 + N = (k + N) + 1 by omega, pow_succ, Nat.factorial_succ]
        push_cast
        field_simp
      _ ≤ q * a k := mul_le_mul_of_nonneg_right hratio (by dsimp [a]; positivity)
  have hgeom (k : ℕ) : a k ≤ a 0 * q ^ k := by
    simpa only [mul_comm (q ^ k)] using le_geom hq₀ k (fun j _ => hstep j)
  let u : ℕ → E := fun n => (n !⁻¹ : ℝ) • X ^ n
  have hnorm : Summable (fun k => ‖u (k + N)‖) :=
    (summable_nat_add_iff N).2 (norm_expSeries_summable' (𝕂 := ℝ) X)
  have hsum := (expSeries_summable' (𝕂 := ℝ) X).sum_add_tsum_nat_add N
  change (∑ k ∈ Finset.range N, u k) + (∑' k, u (k + N)) = ∑' k, u k at hsum
  have htail : exp X - taylor X N = ∑' k, u (k + N) := by
    rw [exp_eq_tsum ℝ]
    change (∑' k, u k) - (∑ k ∈ Finset.range N, u k) = _
    rw [← hsum, add_sub_cancel_left]
  rw [htail]
  calc
    ‖∑' k, u (k + N)‖ ≤ ∑' k, ‖u (k + N)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k, a 0 * q ^ k :=
      hnorm.tsum_le_tsum (fun k => (norm_exp_term_le X hX (k + N)).trans (hgeom k))
        ((summable_geometric_of_lt_one hq₀ hq₁).mul_left _)
    _ = (r ^ N / (N ! : ℝ)) / (1 - r / (N + 1)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq₀ hq₁, div_eq_mul_inv]
      simp [a, q]

omit [CompleteSpace E] in
theorem norm_exp_le_real_exp (X : E) : ‖exp X‖ ≤ Real.exp ‖X‖ := by
  rw [exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  exact (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℝ) X)).trans
    ((norm_expSeries_summable' (𝕂 := ℝ) X).tsum_le_tsum
      (fun n => by simpa [smul_eq_mul, div_eq_inv_mul] using norm_exp_term_le X le_rfl n)
      (expSeries_summable' (𝕂 := ℝ) ‖X‖))

end Taylor

private theorem denominator_pos : 0 < denominator := by
  unfold denominator
  positivity

/-- The half-open rational interval for each entry of the Taylor product. -/
theorem rational_certificate (i j : Fin 3) :
    (floorTable i j : ℚ) / 10000 ≤ (numerator i j : ℚ) / (denominator : ℚ) ∧
    (numerator i j : ℚ) / (denominator : ℚ) < ((floorTable i j : ℚ) + 1) / 10000 := by
  have hd : (0 : ℚ) < (denominator : ℚ) := by exact_mod_cast denominator_pos
  have hlo := Int.ediv_mul_le (10000 * numerator i j) denominator_pos.ne'
  have hhi := Int.lt_ediv_add_one_mul_self (10000 * numerator i j) denominator_pos
  rw [integer_certificate i j] at hlo hhi
  constructor
  · apply (le_div_iff₀ hd).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 10000)).2
    rw [mul_comm _ (10000 : ℚ)]
    exact_mod_cast hlo
  · apply (div_lt_iff₀ hd).2
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (by norm_num : (0 : ℚ) < 10000)).2
    rw [mul_comm _ (10000 : ℚ)]
    exact_mod_cast hhi

noncomputable section

private def castMatrix : Qutrit ℤ →+* Qutrit ℂ :=
  (Int.castRingHom ℂ).mapMatrix

@[simp] private theorem castMatrix_apply (X : Qutrit ℤ) (i j : Fin 3) :
    castMatrix X i j = (X i j : ℂ) := rfl

def A : Qutrit ℂ := castMatrix AInt

def B : Qutrit ℂ := castMatrix BInt

def Y : Qutrit ℂ := castMatrix YInt

theorem A_isHermitian : A.IsHermitian := by
  change A.conjTranspose = A
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, AInt, Matrix.conjTranspose_apply, RCLike.star_def]

theorem B_isHermitian : B.IsHermitian := by
  change B.conjTranspose = B
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [B, BInt, Matrix.conjTranspose_apply, RCLike.star_def]

private theorem taylorState_power (X : Qutrit ℤ) (n : ℕ) :
    (taylorState X n).1 = X ^ n := by
  induction n with
  | zero => simp [taylorState]
  | succ n ih => simp only [taylorState, ih, pow_succ]

private theorem cast_taylorState_sum (X : Qutrit ℤ) (n : ℕ) :
    castMatrix (taylorState X n).2 = (n ! : ℝ) • taylor (castMatrix X) (n + 1) := by
  induction n with
  | zero => simp [taylorState, taylor]
  | succ n ih =>
    have hfactorial : ((n + 1)! : ℝ) ≠ 0 := by positivity
    change castMatrix ((n + 1) • (taylorState X n).2 + (taylorState X (n + 1)).1) =
      ((n + 1)! : ℝ) • taylor (castMatrix X) ((n + 1) + 1)
    rw [map_add, map_nsmul, ih, taylorState_power, map_pow, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul]
    conv_rhs => rw [taylor, Finset.sum_range_succ, smul_add, smul_smul, mul_inv_cancel₀ hfactorial,
      one_smul]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    rfl

private def P : Qutrit ℂ := taylor A 101 * taylor Y 101

private theorem P_apply (i j : Fin 3) :
    P i j = Complex.ofReal ((numerator i j : ℝ) / (denominator : ℝ)) := by
  have hscaled : castMatrix numerator = (denominator : ℝ) • P := by
    simp only [numerator, map_mul, cast_taylorState_sum]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
    change ((100 ! : ℝ) * (100 ! : ℝ)) • P = _
    simp only [denominator, pow_two, Int.cast_mul, Int.cast_natCast]
  have he := congrArg (fun M : Qutrit ℂ => M i j) hscaled
  simp only [castMatrix_apply, Matrix.smul_apply, Complex.real_smul] at he
  have hdc : (denominator : ℂ) ≠ 0 := by exact_mod_cast denominator_pos.ne'
  rw [Complex.ofReal_div, Complex.ofReal_intCast, Complex.ofReal_intCast, eq_div_iff hdc, mul_comm]
  exact he.symm

theorem row_sum_le {X : Qutrit ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i, ∑ j, ‖X i j‖ ≤ r) : ‖X‖ ≤ r := by
  let R : ℝ≥0 := ⟨r, hr⟩
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i => ∑ j, ‖X i j‖₊) : ℝ≥0) ≤ R
  refine Finset.sup_le fun i _ => ?_
  show ((∑ j, ‖X i j‖₊ : ℝ≥0) : ℝ) ≤ r
  simpa only [NNReal.coe_sum, coe_nnnorm] using h i

private theorem entry_norm_le (X : Qutrit ℂ) (i j : Fin 3) : ‖X i j‖ ≤ ‖X‖ := by
  rw [Matrix.linfty_opNorm_def]
  change ‖X i j‖₊ ≤ Finset.univ.sup (fun i => ∑ j, ‖X i j‖₊)
  exact (Finset.single_le_sum (fun b _ => (zero_le : 0 ≤ ‖X i b‖₊)) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ i))

theorem norm_A_le : ‖A‖ ≤ 11 := by
  refine row_sum_le (by norm_num) fun i => ?_
  fin_cases i <;> norm_num [A, AInt, Fin.sum_univ_three, Complex.norm_intCast]

private theorem norm_Y_le : ‖Y‖ ≤ 25 := by
  refine row_sum_le (by norm_num) fun i => ?_
  fin_cases i <;> norm_num [Y, YInt, Fin.sum_univ_three, Complex.norm_intCast]

private theorem tail_101 (X : Qutrit ℂ) (hX : ‖X‖ ≤ 25) :
    ‖exp X - taylor X 101‖ ≤ (1 : ℝ) / 10 ^ 18 := by
  refine (norm_exp_sub_taylor_le X 101 hX (by norm_num)).trans ?_
  norm_num [Nat.factorial]

private theorem norm_exp_le_three_pow (X : Qutrit ℂ) (n : ℕ) (hX : ‖X‖ ≤ n) :
    ‖exp X‖ ≤ (3 : ℝ) ^ n := by
  calc
    ‖exp X‖ ≤ Real.exp ‖X‖ := norm_exp_le_real_exp X
    _ ≤ Real.exp (n : ℝ) := Real.exp_le_exp.mpr hX
    _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
    _ ≤ 3 ^ n := pow_le_pow_left₀ (Real.exp_nonneg 1) Real.exp_one_lt_three.le _

private def K : Qutrit ℂ := exp A * exp Y

private theorem norm_product_error : ‖K - P‖ < (1 : ℝ) / 1000 := by
  let δ : ℝ := 1 / 10 ^ 18
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htA : ‖exp A - taylor A 101‖ ≤ δ := tail_101 A (norm_A_le.trans (by norm_num))
  have htY : ‖exp Y - taylor Y 101‖ ≤ δ := tail_101 Y norm_Y_le
  have heY : ‖exp Y‖ ≤ (3 : ℝ) ^ 25 := norm_exp_le_three_pow Y 25 (by simpa using norm_Y_le)
  have hpA : ‖taylor A 101‖ ≤ (3 : ℝ) ^ 11 + δ := by
    calc
      ‖taylor A 101‖ = ‖exp A - (exp A - taylor A 101)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖exp A‖ + ‖exp A - taylor A 101‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (norm_exp_le_three_pow A 11 (by simpa using norm_A_le)) htA
  have hsplit : K - P = (exp A - taylor A 101) * exp Y +
      taylor A 101 * (exp Y - taylor Y 101) := by
    simp only [K, P, sub_mul, mul_sub]
    abel
  rw [hsplit]
  calc
    ‖_‖ ≤ ‖(exp A - taylor A 101) * exp Y‖ +
        ‖taylor A 101 * (exp Y - taylor Y 101)‖ := norm_add_le _ _
    _ ≤ δ * (3 : ℝ) ^ 25 + ((3 : ℝ) ^ 11 + δ) * δ := by
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul htA heY (norm_nonneg _) hδ))
        ((norm_mul_le _ _).trans (mul_le_mul hpA htY (norm_nonneg _) (by positivity)))
    _ < 1 / 1000 := by norm_num [δ]

private def entryBounds : Qutrit ℝ :=
  !![8, 11, 72; 10, 13, 84; 1 / 100, 1 / 100, 1 / 20]

private theorem norm_K_apply_le (i j : Fin 3) : ‖K i j‖ ≤ entryBounds i j := by
  have hentry : ‖K i j - P i j‖ ≤ 1 / 1000 :=
    (entry_norm_le (K - P) i j).trans norm_product_error.le
  have hlo : (floorTable i j : ℝ) / 10000 ≤ (numerator i j : ℝ) / (denominator : ℝ) := by
    exact_mod_cast (rational_certificate i j).1
  have hhi : (numerator i j : ℝ) / (denominator : ℝ) < ((floorTable i j : ℝ) + 1) / 10000 := by
    exact_mod_cast (rational_certificate i j).2
  have hp : ‖P i j‖ ≤ entryBounds i j - 1 / 1000 := by
    rw [P_apply, Complex.norm_real, Real.norm_eq_abs, abs_le]
    fin_cases i <;> fin_cases j <;>
      norm_num [floorTable, entryBounds] at hlo hhi ⊢ <;>
      constructor <;> linarith only [hlo, hhi]
  have h := (norm_sub_le (K i j - P i j) (-P i j))
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
  linarith only [h, hentry, hp]

open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U)

private theorem traceNorm_le_sum_norm (X : Qutrit ℂ) :
    traceNorm X ≤ ∑ i, ∑ j, ‖X i j‖ := by
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
  have hunitary (i k : Fin 3) : ‖U.val i k‖ ≤ 1 := by
    have h := congrArg (fun M : Qutrit ℂ => M i i)
      (Matrix.mem_unitaryGroup_iff.mp U.prop)
    rw [Matrix.star_eq_conjTranspose] at h
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_sum,
      Matrix.one_apply_eq] at h
    have hsum : (∑ j, ‖U.val i j‖ ^ 2) = 1 := by exact_mod_cast h
    have hsq := (Finset.single_le_sum (f := fun j => ‖U.val i j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ k)).trans_eq hsum
    nlinarith [norm_nonneg (U.val i k)]
  rw [← hU, Matrix.trace, Complex.re_sum]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  calc
    (∑ i, ∑ j, (U.val i j * X j i).re) ≤ ∑ i, ∑ j, ‖X j i‖ := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      exact (Complex.re_le_norm _).trans (by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hunitary i j))
    _ = _ := Finset.sum_comm

private theorem traceNorm_smul_of_nonneg (X : Qutrit ℂ) {c : ℝ} (hc : 0 ≤ c) :
    traceNorm ((c : ℂ) • X) = c * traceNorm X := by
  have htrace (U : Matrix.unitaryGroup (Fin 3) ℂ) :
      (Matrix.trace (U.val * ((c : ℂ) • X))).re = c * (U.val * X).trace.re := by
    simp [Matrix.trace_smul, Complex.mul_re]
  apply le_antisymm
  · obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U ((c : ℂ) • X)).1
    rw [← hU, htrace]
    exact mul_le_mul_of_nonneg_left ((traceNorm_eq_max_re_tr_U X).2 ⟨U, rfl⟩) hc
  · obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
    have h := (traceNorm_eq_max_re_tr_U ((c : ℂ) • X)).2 ⟨U, rfl⟩
    rwa [htrace, hU] at h

private def s : Fin 3 → ℝ := ![-7, 1, 9]

private theorem A_add_B : A + B = Matrix.diagonal (fun i => (s i : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [A, B, AInt, BInt, s, Matrix.add_apply, Matrix.diagonal_apply]

private theorem Y_eq : Y = B + Complex.ofReal (-9) • (1 : Qutrit ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Y, B, YInt, BInt, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

private theorem exp_diagonal_real (v : Fin 3 → ℝ) :
    exp (Matrix.diagonal (fun i => (v i : ℂ))) =
      Matrix.diagonal (fun i => (Real.exp (v i) : ℂ)) := by
  rw [Matrix.exp_diagonal]
  congr 1
  funext i
  simp only [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem exp_add_scalar (X : Qutrit ℂ) (c : ℝ) :
    exp (X + (c : ℂ) • (1 : Qutrit ℂ)) = (Real.exp c : ℂ) • exp X := by
  have hcomm : Commute X ((c : ℂ) • (1 : Qutrit ℂ)) :=
    (Commute.one_right X).smul_right (c : ℂ)
  have hdiag (z : ℂ) : z • (1 : Qutrit ℂ) = Matrix.diagonal (fun _ => z) := by
    ext i j
    simp [Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, mul_ite]
  calc
    exp (X + (c : ℂ) • (1 : Qutrit ℂ)) = exp X * exp ((c : ℂ) • (1 : Qutrit ℂ)) :=
      exp_add_of_commute hcomm
    _ = _ := by
      rw [hdiag, exp_diagonal_real, ← hdiag, mul_smul_comm, mul_one]

private def weights (i : Fin 3) : ℝ := Real.exp (s i - 9)

def overlap : Qutrit ℂ := exp (A + B) * exp A * exp B

private theorem normalized_overlap :
    (Real.exp (-18) : ℂ) • overlap = Matrix.diagonal (fun i => (weights i : ℂ)) * K := by
  have hs : A + B + Complex.ofReal (-9) • (1 : Qutrit ℂ) =
      Matrix.diagonal (fun i => ((s i - 9 : ℝ) : ℂ)) := by
    rw [A_add_B]
    ext i j
    by_cases h : i = j <;>
      simp [h, Matrix.add_apply, Matrix.smul_apply, sub_eq_add_neg]
  have hD : Matrix.diagonal (fun i => (weights i : ℂ)) =
      (Real.exp (-9) : ℂ) • exp (A + B) := by
    rw [← exp_add_scalar, hs, exp_diagonal_real]
    rfl
  rw [hD, K, Y_eq, exp_add_scalar, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_smul]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  norm_num [overlap, Matrix.mul_assoc]

private theorem exp_neg_nat_le_inv_two_pow (n : ℕ) :
    Real.exp (-(n : ℝ)) ≤ 1 / (2 : ℝ) ^ n := by
  rw [Real.exp_neg, show Real.exp (n : ℝ) = Real.exp 1 ^ n by rw [← Real.exp_nat_mul, mul_one],
    one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le n)

theorem normalized_overlap_bound :
    traceNorm ((Real.exp (-18) : ℂ) • overlap) ≤ (801763 : ℝ) / 1638400 := by
  rw [normalized_overlap]
  refine (traceNorm_le_sum_norm _).trans ?_
  have hnorm (i : Fin 3) : ‖weights i‖ = weights i :=
    Real.norm_of_nonneg (Real.exp_nonneg _)
  simp only [Matrix.diagonal_mul, norm_mul, Complex.norm_real, hnorm]
  have hweighted : (∑ i, ∑ j, weights i * ‖K i j‖) ≤
      ∑ i, ∑ j, weights i * entryBounds i j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_K_apply_le i j) (Real.exp_nonneg _)
  refine hweighted.trans ?_
  have h16 : Real.exp (-16) ≤ 1 / (2 : ℝ) ^ 16 := by
    simpa using exp_neg_nat_le_inv_two_pow 16
  have h8 : Real.exp (-8) ≤ 1 / (2 : ℝ) ^ 8 := by
    simpa using exp_neg_nat_le_inv_two_pow 8
  norm_num [Fin.sum_univ_three, weights, s, entryBounds]
  linarith only [h16, h8]

theorem comparison_trace :
    (exp ((2 : ℂ) • (A + B))).trace.re =
      Real.exp (-14) + Real.exp 2 + Real.exp 18 := by
  have hd : (2 : ℂ) • (A + B) = Matrix.diagonal (fun i => ((2 * s i : ℝ) : ℂ)) := by
    rw [A_add_B, ← Matrix.diagonal_smul]
    congr 1
    funext i
    simp [smul_eq_mul]
  rw [hd, exp_diagonal_real, Matrix.trace_diagonal, Complex.re_sum]
  simp only [Complex.ofReal_re]
  norm_num [Fin.sum_univ_three, s]

/-- The strict reverse of the proposed polar-optimized half-time overlap inequality,
with `H = 2 • A` and `J = 2 • B`. -/
theorem polar_optimized_overlap_lt :
    traceNorm (exp (A + B) * exp A * exp B) <
      (exp ((2 : ℂ) • (A + B))).trace.re := by
  have hl := normalized_overlap_bound
  rw [traceNorm_smul_of_nonneg overlap (Real.exp_nonneg _)] at hl
  change Real.exp (-18) * traceNorm (exp (A + B) * exp A * exp B) ≤ _ at hl
  apply (mul_lt_mul_iff_right₀ (Real.exp_pos (-18))).mp
  rw [comparison_trace, mul_add, mul_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  norm_num
  linarith only [hl, Real.exp_nonneg (-32), Real.exp_nonneg (-16)]

/- The closed universal claim is stated with `Not` so its kernel proof exposes the
   literal counterexample supplied by `polar_optimized_overlap_lt`. -/
def claim : Prop :=
  ∀ H J : Qutrit ℂ,
    H.IsHermitian → J.IsHermitian →
      (exp (H + J)).trace.re ≤
        traceNorm (exp ((1 / 2 : ℂ) • (H + J)) *
          exp ((1 / 2 : ℂ) • H) * exp ((1 / 2 : ℂ) • J))

theorem result : Not claim := by
  intro h
  have hbound := h ((2 : ℂ) • A) ((2 : ℂ) • B)
    (show ((2 : ℂ) • A).IsHermitian from A_isHermitian.smul (by simp))
    (show ((2 : ℂ) • B).IsHermitian from B_isHermitian.smul (by simp))
  have hstrict := polar_optimized_overlap_lt
  apply (not_lt_of_ge hbound)
  simpa [claim, smul_add, smul_smul,
    add_assoc, add_left_comm, add_comm] using hstrict

end

end D5.S3.Quantum.Recovery.GibbsOverlap.PetzIntegerQutritOverlap
