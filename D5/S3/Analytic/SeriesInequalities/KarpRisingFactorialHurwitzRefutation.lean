/- GID: D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.claim; result=D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.result; claim=D5/S3/Analytic/SeriesInequalities/KarpRisingFactorialHurwitzRefutation.claim
   digest: Positive shifts need not preserve rising-factorial Toeplitz Hurwitz stability. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#22349; Refuted)
  Direct frozen dependencies: none (Mathlib-only import closure).
All private theorems below have proof_shape: bind-only, escape_witness: none,
and Direct frozen dependencies: none. Their consumers are:
  log_nonneg -> positive_root_of_negative
  input_pos -> stable_scaledQ
  expo_relation -> input_strict
  input_strict -> stable_scaledQ
  scaledAsc_expansion -> scaledAsc_zero, continuous_scaledAsc_eval,
    continuous_scaledAsc_deriv_eval
  scaledAsc_zero -> scaledQ_zero
  continuous_scaledAsc_eval -> continuous_scaledQ_eval, continuous_scaledQ_deriv_eval
  continuous_scaledAsc_deriv_eval -> continuous_scaledQ_deriv_eval
  continuous_scaledQ_eval -> result
  continuous_scaledQ_deriv_eval -> result
  scaledAsc_identity -> scaledQ_identity
  scaledQ_identity -> stable_scaledQ
  expo_ne_zero -> scaledQ_zero
  scaledQ_zero -> limit_negative
  limit_negative -> result
  stable_scaledQ -> result
  positive_root_of_negative -> result
The definitions Q and claim state equation (3)
and Conjecture 2 of arXiv:1203.1482v1, p. 2. Rising factorials use ascPochhammer.
The squared Nat.dist k 10 equals (k - 10)^2 + (10 - k)^2; scaled rising
factorials use Polynomial.scaleRoots followed by Polynomial.comp.
The public result is the designated refutation result (`basis=refutes`) and is
exempt from four-slot escape registration (CLAUDE.md §3.9).
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Literal conventions for Karp, arXiv:1203.1482v1, equation (3), Conjecture 2.
The rising factorial is Mathlib's ascPochhammer; no replacement is defined.
The finite input is read on indices 0,...,n. The source's explicit convention
for internal zeros is written in claim, including its restriction N > 0.
Q is an explicit finite sum, so there is no implicitly specified source object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.SeriesInequalities.KarpRisingFactorialHurwitzRefutation

open Polynomial
open scoped BigOperators

/-- Equation (3), with the real coefficients embedded into the complex numbers. -/
def Q (n : ℕ) (f : ℕ → ℝ) (α β : ℝ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((f k : ℂ) * (f (n - k) : ℂ) * (n.choose k : ℂ)) *
      (((ascPochhammer ℂ k).comp (X + C (α : ℂ))) *
          ((ascPochhammer ℂ (n - k)).comp (X + C (β : ℂ))) -
        ((ascPochhammer ℂ k).comp (X + C ((α + β : ℝ) : ℂ))) *
          ascPochhammer ℂ (n - k))

/-- Conjecture 2, including the nonnegative, nonzero input convention and the
source's definition of Hurwitz stability: every zero has negative real part. -/
def claim : Prop :=
  ∀ (n : ℕ) (α : ℝ) (β : ℝ) (f : ℕ → ℝ),
    3 ≤ n →
    0 < α →
    0 < β →
    (∀ k : ℕ, k ≤ n → 0 ≤ f k) →
    (∃ k : ℕ, k ≤ n ∧ f k ≠ 0) →
    (∀ N : ℕ, 0 < N → N ≤ n → f N = 0 →
      ∀ k : ℕ, N ≤ k → k ≤ n → f k = 0) →
    (∀ k : ℕ, 1 ≤ k → k < n → f (k - 1) * f (k + 1) < (f k) ^ 2) →
    ∀ z : ℂ, (Q n f α β).eval z = 0 → z.re < 0

end D5.S3.Analytic.SeriesInequalities.KarpRisingFactorialHurwitzRefutation

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000


namespace D5.S3.Analytic.SeriesInequalities.KarpRisingFactorialHurwitzRefutation
open Polynomial Filter Topology
open scoped BigOperators ComplexConjugate

private theorem log_nonneg (p : ℂ[X]) (z : ℂ) (hz : 0 < z.re)
    (hstable : ∀ w : ℂ, p.eval w = 0 → w.re ≤ 0) :
    0 ≤ (p.derivative.eval z / p.eval z).re := by
  have hpz : p.eval z ≠ 0 := by
    intro h
    exact (not_le_of_gt hz) (hstable z h)
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
  change 0 ≤ Complex.reAddGroupHom ((p.roots.map fun w => 1 / (z-w)).sum)
  rw [map_multiset_sum, Multiset.map_map]
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
  have hwneg := hstable w (Polynomial.isRoot_of_mem_roots hw)
  simp only [Function.comp_apply, one_div]
  change 0 ≤ ((z-w)⁻¹).re
  rw [Complex.inv_re]
  apply div_nonneg
  · simp only [Complex.sub_re]
    linarith
  · exact Complex.normSq_nonneg _

private def expo (k : ℕ) : ℕ := (Nat.dist k 10)^2
private def input (t : ℝ) (k : ℕ) : ℝ := t ^ expo k

private theorem input_pos (t : ℝ) (ht : 0 < t) (k : ℕ) : 0 < input t k := by
  exact pow_pos ht _

private theorem expo_relation (k : ℕ) (hlo : 1 ≤ k) (hhi : k < 20) :
    expo (k-1) + expo (k+1) = 2 * expo k + 2 := by
  interval_cases k <;> norm_num [expo, Nat.dist]

private theorem input_strict (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (k : ℕ) (hlo : 1 ≤ k) (hhi : k < 20) :
    input t (k-1) * input t (k+1) < (input t k)^2 := by
  unfold input
  rw [← pow_add, expo_relation k hlo hhi, pow_add, Nat.mul_comm 2 (expo k), pow_mul]
  have hsq : t^2 < (1 : ℝ) := pow_lt_one₀ ht.le ht1 (by norm_num)
  simpa using (mul_lt_mul_of_pos_left hsq (sq_pos_of_pos (pow_pos ht (expo k))))

private def scaledAsc (n : ℕ) (t c : ℝ) : ℂ[X] :=
  ((ascPochhammer ℂ n).scaleRoots (t : ℂ)).comp (X + C (c : ℂ))

private theorem scaledAsc_expansion (n : ℕ) (t c : ℝ) :
    scaledAsc n t c = ∏ j ∈ Finset.range n, (X + C ((c + j*t : ℝ) : ℂ)) := by
  unfold scaledAsc
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_scaleRoots_of_noZeroDivisors,
      show (n : ℂ[X]) = C (n : ℂ) by simp,
      X_add_C_scaleRoots, mul_comp, ih, Finset.prod_range_succ]
    congr 1
    simp only [add_comp, X_comp, C_comp]
    push_cast
    simp only [map_add]
    <;> ring

private theorem scaledAsc_zero (n : ℕ) (c : ℝ) :
    scaledAsc n 0 c = (X + C (c : ℂ))^n := by
  simp [scaledAsc_expansion]

private theorem continuous_scaledAsc_eval (n : ℕ) (c : ℝ) (z : ℂ) :
    Continuous (fun t : ℝ => (scaledAsc n t c).eval z) := by
  simp only [scaledAsc_expansion, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  fun_prop

private theorem continuous_scaledAsc_deriv_eval (n : ℕ) (c : ℝ) (z : ℂ) :
    Continuous (fun t : ℝ => (scaledAsc n t c).derivative.eval z) := by
  simp only [scaledAsc_expansion, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum,
    Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C,
    add_zero, Polynomial.eval_mul, Polynomial.eval_one, one_mul,
    Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  fun_prop

private def scaledQ (t : ℝ) : ℂ[X] :=
  ∑ k ∈ Finset.range 21,
    C ((input t k : ℂ) * (input t (20-k) : ℂ) * (Nat.choose 20 k : ℂ)) *
      (scaledAsc k t 1 * scaledAsc (20-k) t 1 -
        scaledAsc k t 2 * scaledAsc (20-k) t 0)

private theorem continuous_scaledQ_eval (z : ℂ) :
    Continuous (fun t : ℝ => (scaledQ t).eval z) := by
  simp only [scaledQ, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub]
  apply continuous_finsetSum
  intro k hk
  apply Continuous.mul
  · unfold input
    fun_prop
  · exact ((continuous_scaledAsc_eval k 1 z).mul
      (continuous_scaledAsc_eval (20-k) 1 z)).sub
        ((continuous_scaledAsc_eval k 2 z).mul (continuous_scaledAsc_eval (20-k) 0 z))

private theorem continuous_scaledQ_deriv_eval (z : ℂ) :
    Continuous (fun t : ℝ => (scaledQ t).derivative.eval z) := by
  simp only [scaledQ, Polynomial.derivative_sum, Polynomial.derivative_C_mul,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.eval_zero, zero_mul, zero_add, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_add]
  apply continuous_finsetSum
  intro k hk
  apply Continuous.mul
  · unfold input
    fun_prop
  · exact (((continuous_scaledAsc_deriv_eval k 1 z).mul
      (continuous_scaledAsc_eval (20-k) 1 z)).add
        ((continuous_scaledAsc_eval k 1 z).mul (continuous_scaledAsc_deriv_eval (20-k) 1 z))).sub
        (((continuous_scaledAsc_deriv_eval k 2 z).mul
      (continuous_scaledAsc_eval (20-k) 0 z)).add
        ((continuous_scaledAsc_eval k 2 z).mul (continuous_scaledAsc_deriv_eval (20-k) 0 z)))


private theorem scaledAsc_identity (n : ℕ) (t c : ℝ) (ht : t ≠ 0) (z : ℂ) :
    (scaledAsc n t c).eval z =
      (t : ℂ)^n * (ascPochhammer ℂ n).eval ((z + (c : ℂ))/(t : ℂ)) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  unfold scaledAsc
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  simpa only [ascPochhammer_natDegree, mul_div_cancel₀ _ htC] using
    (Polynomial.scaleRoots_eval_mul (ascPochhammer ℂ n)
      ((z + (c : ℂ)) / (t : ℂ)) (t : ℂ))

private theorem scaledQ_identity (t : ℝ) (ht : t ≠ 0) (z : ℂ) :
    (scaledQ t).eval z = (t : ℂ)^20 *
      (Q 20 (input t) (1/t) (1/t)).eval (z / (t : ℂ)) := by
  simp only [scaledQ, Q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk20 : k ≤ 20 := by exact Finset.mem_range_succ_iff.mp hk
  have hpow : (t : ℂ)^k * (t : ℂ)^(20-k) = (t : ℂ)^20 := by
    exact pow_mul_pow_sub (t : ℂ) hk20
  rw [scaledAsc_identity k t 1 ht z, scaledAsc_identity (20-k) t 1 ht z,
    scaledAsc_identity k t 2 ht z, scaledAsc_identity (20-k) t 0 ht z]
  push_cast
  simp only [Complex.ofReal_one, Complex.ofReal_zero, add_zero]
  have harg1 : (z+1)/(t : ℂ) = z/(t : ℂ)+1/(t : ℂ) := add_div _ _ _
  have harg2 : (z+2)/(t : ℂ) = z/(t : ℂ)+(1/(t : ℂ)+1/(t : ℂ)) := by ring
  rw [harg1, harg2]
  linear_combination
    ((input t k : ℂ) * (input t (20-k) : ℂ) * (Nat.choose 20 k : ℂ) *
      ((ascPochhammer ℂ k).eval (z/(t : ℂ)+1/(t : ℂ)) *
        (ascPochhammer ℂ (20-k)).eval (z/(t : ℂ)+1/(t : ℂ)) -
        (ascPochhammer ℂ k).eval (z/(t : ℂ)+(1/(t : ℂ)+1/(t : ℂ))) *
        (ascPochhammer ℂ (20-k)).eval (z/(t : ℂ)))) * hpow

private theorem expo_ne_zero (k : ℕ) (hk : k ≠ 10) : expo k ≠ 0 := by
  exact pow_ne_zero _ (Nat.dist_pos_of_ne hk).ne'

private theorem scaledQ_zero :
    scaledQ 0 = C (184756 : ℂ) * ((X+1)^20 - (X*(X+2))^10) := by
  have hchoose : Nat.choose 20 10 = 184756 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num : 10 ≤ 20)]
    norm_num [Nat.factorial]
  unfold scaledQ
  rw [Finset.sum_eq_single 10]
  · norm_num [input, expo, Nat.dist, scaledAsc_zero, hchoose, map_ofNat]
    ring
  · intro k hk hne
    simp [input, zero_pow (expo_ne_zero k hne)]
  · simp

private def testPoint : ℂ := 1/50 + (3/4)*Complex.I

private theorem limit_negative :
    (((scaledQ 0).derivative.eval testPoint) * conj ((scaledQ 0).eval testPoint)).re < 0 := by
  rw [scaledQ_zero]
  norm_num [Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_ofNat, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_one, testPoint, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    pow_succ]


private theorem stable_scaledQ (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hc : claim) : ∀ w : ℂ, (scaledQ t).eval w = 0 → w.re < 0 := by
  intro w hw
  have hzero : (Q 20 (input t) (1/t) (1/t)).eval (w / (t : ℂ)) = 0 := by
    have he := scaledQ_identity t ht.ne' w
    rw [hw] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ (by exact_mod_cast ht.ne'))
  have hneg := hc 20 (1/t) (1/t) (input t) (by norm_num)
    (one_div_pos.mpr ht) (one_div_pos.mpr ht)
    (fun k _ => (input_pos t ht k).le)
    ⟨0, by norm_num, (input_pos t ht 0).ne'⟩
    (by
      intro N _ _ hN
      exact False.elim ((input_pos t ht N).ne' hN))
    (fun k hk hk20 => input_strict t ht ht1 k hk hk20)
    (w / (t : ℂ)) hzero
  rw [Complex.div_ofReal_re] at hneg
  simpa only [div_lt_iff₀ ht, zero_mul] using hneg

private theorem positive_root_of_negative (p : ℂ[X]) (z : ℂ) (hz : 0 < z.re)
    (hnegative : (p.derivative.eval z * conj (p.eval z)).re < 0) :
    ∃ w : ℂ, p.eval w = 0 ∧ 0 < w.re := by
  by_contra h
  push Not at h
  have hp : p.eval z ≠ 0 := by
    intro hp
    exact (not_le_of_gt hz) (h z hp)
  have hn := Complex.normSq_pos.mpr hp
  have hh := mul_nonneg (log_nonneg p z hz h) hn.le
  have hid : (p.derivative.eval z * conj (p.eval z)).re =
      (p.derivative.eval z / p.eval z).re * Complex.normSq (p.eval z) := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.div_re]
    field_simp [hn.ne']
    <;> ring
  rw [← hid] at hh
  exact (not_lt_of_ge hh) hnegative

theorem result : ¬ claim := by
  intro hc
  let R : ℝ → ℝ := fun t =>
    (((scaledQ t).derivative.eval testPoint) * conj ((scaledQ t).eval testPoint)).re
  have hR : Continuous R := by
    exact Complex.continuous_re.comp
      ((continuous_scaledQ_deriv_eval testPoint).mul
        (Complex.continuous_conj.comp (continuous_scaledQ_eval testPoint)))
  have hev : ∀ᶠ t : ℝ in 𝓝 0, R t < 0 :=
    hR.continuousAt.eventually (gt_mem_nhds limit_negative)
  obtain ⟨ε, hε, heps⟩ := Metric.eventually_nhds_iff.mp hev
  let t : ℝ := min ε 1 / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htle : t ≤ ε/2 := by dsimp [t]; linarith [min_le_left ε 1]
  have ht1 : t < 1 := by dsimp [t]; linarith [min_le_right ε 1]
  have hneg : R t < 0 := heps (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using
      (show t < ε by linarith))
  have hz : 0 < testPoint.re := by norm_num [testPoint]
  obtain ⟨w, hw, hwpos⟩ := positive_root_of_negative (scaledQ t) testPoint hz hneg
  exact (not_lt_of_ge hwpos.le) (stable_scaledQ t ht ht1 hc w hw)

end D5.S3.Analytic.SeriesInequalities.KarpRisingFactorialHurwitzRefutation
