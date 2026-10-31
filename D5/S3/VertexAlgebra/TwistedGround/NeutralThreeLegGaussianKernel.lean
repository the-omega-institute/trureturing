/- GID: D5/S3/VertexAlgebra/TwistedGround/NeutralThreeLegGaussianKernel
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native pair and jet coefficients give a damped symmetric three-leg one-particle contraction. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianResolvent
import D5.S3.VertexAlgebra.LatticeHalfFockFockNormalField
import D5.S3.Quantum.Analysis.TraceClass.ColumnSynthesis
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators

noncomputable section
open scoped BigOperators ComplexConjugate ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel
open LatticeHalfFockFiniteCorrection LatticeHalfFockFockNormalField
open OriginalGaussianMatrix OriginalGaussianResolvent

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- The ordinary real falling-binomial product, including the empty product. -/
def binomialProduct (x : ℝ) (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n, (x - j)) / n.factorial

lemma jet_create_product (n k : ℕ) :
    jetScalar n (-(k : ℤ) - 1) = (binomialProduct (k - 1 / 2) n : ℂ) := by
  simp only [jetScalar, binomialProduct, map_div₀, map_prod, Complex.ofReal_sub,
    Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  ring

lemma jet_annihilate_product (n k : ℕ) :
    jetScalar n (k : ℤ) = (-1 : ℂ)^n *
      (binomialProduct (k + n + 1 / 2) n : ℂ) := by
  have hrev : (∏ j ∈ Finset.range n, ((k : ℂ) + 3 / 2 + j)) =
      ∏ j ∈ Finset.range n, ((k : ℂ) + n + 1 / 2 - j) := by
    rw [← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    push_cast [Nat.cast_sub (by omega : j + 1 ≤ n)]
    ring
  simp only [jetScalar, Int.cast_natCast]
  have hneg : (∏ j ∈ Finset.range n, (-(k : ℂ) - 3 / 2 - j)) =
      (-1 : ℂ)^n * ∏ j ∈ Finset.range n, ((k : ℂ) + 3 / 2 + j) := by
    simp_rw [show ∀ j : ℕ, -(k : ℂ) - 3 / 2 - j =
      (-1 : ℂ) * ((k : ℂ) + 3 / 2 + j) by intro j; ring]
    simp [Finset.prod_mul_distrib]
  rw [hneg, hrev]
  simp only [binomialProduct, map_div₀, map_prod, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

private lemma rising_product (n k : ℕ) :
    (∏ j ∈ Finset.range n, ((k : ℝ) + 2 + j)) =
      (n.factorial : ℝ) * ((k + n + 1).choose n : ℝ) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (k + 1) n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have hc := congrArg (fun a : ℕ => (a : ℝ)) h
  push_cast at hc
  convert hc using 1 <;> congr 1 <;> omega

/-- Both literal jet products obey the same binomial majorant, at every order. -/
theorem jet_binomial_bound (n k : ℕ) (m : ℤ)
    (hm : m = (k : ℤ) ∨ m = -(k : ℤ) - 1) :
    ‖jetScalar n m‖ ≤ ((k + n + 1).choose n : ℝ) := by
  have hfactor (j : ℕ) : ‖-(m : ℂ) - 3 / 2 - j‖ ≤ (k : ℝ) + 2 + j := by
    rcases hm with rfl | rfl
    · have he : -(k : ℂ) - 3 / 2 - j = (((-(k : ℝ) - 3 / 2 - j) : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by positivity)]
      linarith
    · have he : -((-(k : ℤ) - 1 : ℤ) : ℂ) - 3 / 2 - j =
          (((k : ℝ) - 1 / 2 - j : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      exact (abs_le.mpr ⟨by linarith [Nat.cast_nonneg k], by linarith [Nat.cast_nonneg j]⟩)
  rw [jetScalar, norm_div, norm_prod]
  have hf : ‖(n.factorial : ℂ)‖ = (n.factorial : ℝ) := by simp
  rw [hf, div_le_iff₀ (by positivity)]
  calc
    _ ≤ ∏ j ∈ Finset.range n, ((k : ℝ) + 2 + j) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hfactor j)
    _ = _ := by rw [rising_product]; ring

private lemma jet_power_bound (n k : ℕ) (m : ℤ)
    (hm : m = (k : ℤ) ∨ m = -(k : ℤ) - 1) :
    ‖jetScalar n m‖ ≤ (2 : ℝ)^(k + n + 1) :=
  (jet_binomial_bound n k m hm).trans (by exact_mod_cast Nat.choose_le_two_pow (k+n+1) n)

private lemma pair_half_bound (q : ℂ) (s t : ℕ) (hs : 0 < s) (ht : 0 < t) :
    ‖matrixEntry q s t‖ ≤ (1 / 2 : ℝ) * ‖q‖^(s+t) := by
  rw [matrixEntry_norm q s t hs ht]
  have hst : 0 < (s : ℝ) + t := by positivity
  have hroot : 2 * (Real.sqrt (s : ℝ) * Real.sqrt (t : ℝ)) ≤ (s : ℝ) + t := by
    nlinarith [sq_nonneg (Real.sqrt (s : ℝ) - Real.sqrt (t : ℝ)),
      Real.sq_sqrt (Nat.cast_nonneg s), Real.sq_sqrt (Nat.cast_nonneg t)]
  have hw : centralWeight s * centralWeight t ≤ 1 :=
    mul_le_one₀ (centralWeight_nonneg s) (weight_le_one s)
      (centralWeight_nonneg t) (weight_le_one t)
  apply (div_le_iff₀ hst).mpr
  calc
    _ = (Real.sqrt (s : ℝ) * Real.sqrt (t : ℝ)) *
      (centralWeight s * centralWeight t) * ‖q‖^(s+t) := by ring
    _ ≤ ((s : ℝ) + t) / 2 * 1 * ‖q‖^(s+t) := by gcongr; linarith
    _ = _ := by ring

private lemma jet_square_majorant (N n k : ℕ) (a root q : ℂ) (m : ℤ)
    (hm : m = (k : ℤ) ∨ m = -(k : ℤ)-1)
    (ha : ‖a‖ ≤ 1/16) (hq : ‖q‖ ≤ 1/16)
    (hroot : ‖root‖^2 = ‖q‖) :
    ‖a^(n+1) * root * q^k *
      (Real.sqrt (((k : ℝ)+1/2)/(n+1)) : ℂ) * jetScalar n m‖^2 ≤
      4 * ‖a‖^2 * ‖q‖ * (1/2 : ℝ)^n * (1/2 : ℝ)^k := by
  have hmu : ((k : ℝ)+1/2)/(n+1) ≤ (k : ℝ)+1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
    nlinarith [Nat.cast_nonneg n, Nat.cast_nonneg k]
  have hk : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
    have h : k+1 ≤ 2^k := k.lt_two_pow_self
    exact_mod_cast h
  have hj := jet_power_bound n k m hm
  have hsmallA : 4 * ‖a‖^2 ≤ (1/2 : ℝ) := by nlinarith [norm_nonneg a]
  have hsmallQ : 8 * ‖q‖^2 ≤ (1/2 : ℝ) := by nlinarith [norm_nonneg q]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [Real.sq_sqrt (by positivity), hroot]
  calc
    _ ≤ (‖a‖^(n+1))^2 * ‖q‖ * (‖q‖^k)^2 *
        ((2 : ℝ)^k) * ((2 : ℝ)^(k+n+1))^2 := by gcongr; exact hmu.trans hk
    _ = 4 * ‖a‖^2 * ‖q‖ * (4*‖a‖^2)^n * (8*‖q‖^2)^k := by
      simp only [pow_add, mul_pow, pow_mul, pow_succ]
      ring
    _ ≤ _ := by gcongr

def eta (N : ℕ) : ℝ := 1 / (16 * (N + 1))

/-- Strict damping conditions on the actual evaluation parameter and three legs. -/
structure Damping (N : ℕ) where
  T : ℂ
  T_ne : T ≠ 0
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  gamma_pos : 0 < gamma
  alpha_lt : alpha < min 1 (eta N * ‖T‖^2)
  beta_lt : beta < min 1 (eta N * ‖T‖^2)
  gamma_lt : gamma < min 1 (eta N / ‖T‖^2)

private lemma eta_bounds (N : ℕ) : 0 < eta N ∧ eta N ≤ 1 / 16 := by
  constructor
  · unfold eta; positivity
  · unfold eta
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (N+1))).mpr
    nlinarith [Nat.cast_nonneg N]

/-- The damping region is nonempty for every rank and every nonzero T. -/
theorem damping_nonempty (N : ℕ) (T : ℂ) (hT : T ≠ 0) :
    ∃ d : Damping N, d.T = T := by
  have hr : 0 < ‖T‖^2 := pow_pos (norm_pos_iff.mpr hT) _
  have he := eta_bounds N
  have hm : 0 < min 1 (‖T‖^2) := lt_min (by norm_num) hr
  have hm' : 0 < min 1 (1 / ‖T‖^2) := lt_min (by norm_num) (by positivity)
  refine ⟨{
    T := T, T_ne := hT
    alpha := eta N / 2 * min 1 (‖T‖^2)
    beta := eta N / 2 * min 1 (‖T‖^2)
    gamma := eta N / 2 * min 1 (1 / ‖T‖^2)
    alpha_pos := by positivity
    beta_pos := by positivity
    gamma_pos := by positivity
    alpha_lt := ?_
    beta_lt := ?_
    gamma_lt := ?_ }, rfl⟩
  · apply lt_min
    · nlinarith [min_le_left (1 : ℝ) (‖T‖^2)]
    · nlinarith [min_le_right (1 : ℝ) (‖T‖^2)]
  · apply lt_min
    · nlinarith [min_le_left (1 : ℝ) (‖T‖^2)]
    · nlinarith [min_le_right (1 : ℝ) (‖T‖^2)]
  · apply lt_min
    · nlinarith [min_le_left (1 : ℝ) (1 / ‖T‖^2)]
    · have := min_le_right (1 : ℝ) (1 / ‖T‖^2)
      rw [div_eq_mul_inv]
      nlinarith [mul_pos he.1 (inv_pos.mpr hr)]

namespace Damping
variable {N : ℕ} (d : Damping N)

def sourceRatio : ℂ := (d.alpha : ℂ) / d.T^2
def inputRatio : ℂ := (d.beta : ℂ) / d.T^2
def outputRatio : ℂ := (d.gamma : ℂ) * d.T^2
def inputRoot : ℂ := (Real.sqrt d.beta : ℂ) / d.T
def outputRoot : ℂ := (Real.sqrt d.gamma : ℂ) * d.T

private lemma ratio_bounds :
    ‖d.sourceRatio‖ ≤ eta N ∧ ‖d.inputRatio‖ ≤ eta N ∧
      ‖d.outputRatio‖ ≤ eta N := by
  have hT : 0 < ‖d.T‖^2 := pow_pos (norm_pos_iff.mpr d.T_ne) _
  simp only [sourceRatio, inputRatio, outputRatio, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.alpha_pos,
    abs_of_pos d.beta_pos, abs_of_pos d.gamma_pos]
  refine ⟨?_, ?_, ?_⟩
  · exact (div_lt_iff₀ hT).mpr (lt_min_iff.mp d.alpha_lt).2 |>.le
  · exact (div_lt_iff₀ hT).mpr (lt_min_iff.mp d.beta_lt).2 |>.le
  · exact ((lt_div_iff₀ hT).mp (lt_min_iff.mp d.gamma_lt).2).le

private lemma root_norms :
    ‖d.inputRoot‖^2 = ‖d.inputRatio‖ ∧
      ‖d.outputRoot‖^2 = ‖d.outputRatio‖ := by
  simp only [inputRoot, outputRoot, inputRatio, outputRatio, norm_div, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos d.beta_pos,
    abs_of_pos d.gamma_pos, div_pow, mul_pow,
    Real.sq_sqrt d.beta_pos.le, Real.sq_sqrt d.gamma_pos.le]
  exact ⟨rfl, rfl⟩

/-- Source n is the original positive source frequency n+1. -/
def SS (n m : ℕ) : ℂ := matrixEntry d.sourceRatio (n+1) (m+1)

/-- The native annihilation jet, with its doubled integer Hahn powers factored. -/
def SI (n k : ℕ) : ℂ := d.sourceRatio^(n+1) * d.inputRoot * d.inputRatio^k *
  (Real.sqrt (((k : ℝ) + 1/2) / (n+1)) : ℂ) * jetScalar n (k : ℤ)

/-- The native creation jet; the output block is holomorphic, without conjugation. -/
def SO (n k : ℕ) : ℂ := d.sourceRatio^(n+1) * d.outputRoot * d.outputRatio^k *
  (Real.sqrt (((k : ℝ) + 1/2) / (n+1)) : ℂ) * jetScalar n (-(k : ℤ)-1)

def IO (k l : ℕ) : ℂ :=
  if k = l then (Real.sqrt (d.beta*d.gamma) : ℂ) * ((d.beta*d.gamma : ℝ) : ℂ)^k else 0

/-- Three infinite mode legs; all colors, including the empty rank-zero carrier. -/
abbrev Index (N : ℕ) := Fin N × (Fin 3 × ℕ)
abbrev Space (N : ℕ) := lp (fun _ : Index N => ℂ) 2

def scalar (a b : Fin 3) (n m : ℕ) : ℂ :=
  ![![d.SS n m, d.SI n m, d.SO n m],
    ![d.SI m n, 0, d.IO n m],
    ![d.SO m n, d.IO m n, 0]] a b

def entry (i j : Index N) : ℂ :=
  if i.1 = j.1 then d.scalar i.2.1 j.2.1 i.2.2 j.2.2 else 0

private lemma ss_symm (n m : ℕ) : d.SS n m = d.SS m n := by
  unfold SS matrixEntry pairScalar
  congr 1
  · ring
  · omega

private lemma ss_square_bound (n m : ℕ) :
    ‖d.SS n m‖^2 ≤ (eta N)^4 / 4 * (1/2 : ℝ)^n * (1/2 : ℝ)^m := by
  have he := eta_bounds N
  have hq := (d.ratio_bounds).1
  have hsmall : ‖d.sourceRatio‖^2 ≤ (1/2 : ℝ) := by nlinarith [norm_nonneg d.sourceRatio]
  have h := pair_half_bound d.sourceRatio (n+1) (m+1) (by omega) (by omega)
  calc
    _ ≤ ((1/2 : ℝ) * ‖d.sourceRatio‖^((n+1)+(m+1)))^2 := by
      dsimp [SS]; gcongr
    _ = ‖d.sourceRatio‖^4 / 4 * (‖d.sourceRatio‖^2)^n *
        (‖d.sourceRatio‖^2)^m := by
      simp only [mul_pow, pow_add, pow_succ, pow_mul]; ring
    _ ≤ _ := by gcongr

private lemma si_square_bound (n k : ℕ) :
    ‖d.SI n k‖^2 ≤ 4 * (eta N)^3 * (1/2 : ℝ)^n * (1/2 : ℝ)^k := by
  have he := eta_bounds N
  have h := jet_square_majorant N n k d.sourceRatio d.inputRoot d.inputRatio (k : ℤ)
    (Or.inl rfl) ((d.ratio_bounds).1.trans he.2)
    ((d.ratio_bounds).2.1.trans he.2) d.root_norms.1
  apply h.trans
  have hpow : ‖d.sourceRatio‖^2 ≤ (eta N)^2 := by gcongr; exact d.ratio_bounds.1
  calc
    _ ≤ 4 * (eta N)^2 * eta N * (1/2 : ℝ)^n * (1/2 : ℝ)^k := by
      gcongr; exact d.ratio_bounds.2.1
    _ = _ := by ring

private lemma so_square_bound (n k : ℕ) :
    ‖d.SO n k‖^2 ≤ 4 * (eta N)^3 * (1/2 : ℝ)^n * (1/2 : ℝ)^k := by
  have he := eta_bounds N
  have h := jet_square_majorant N n k d.sourceRatio d.outputRoot d.outputRatio (-(k : ℤ)-1)
    (Or.inr rfl) ((d.ratio_bounds).1.trans he.2)
    ((d.ratio_bounds).2.2.trans he.2) d.root_norms.2
  apply h.trans
  have hpow : ‖d.sourceRatio‖^2 ≤ (eta N)^2 := by gcongr; exact d.ratio_bounds.1
  calc
    _ ≤ 4 * (eta N)^2 * eta N * (1/2 : ℝ)^n * (1/2 : ℝ)^k := by
      gcongr; exact d.ratio_bounds.2.2
    _ = _ := by ring

private lemma io_square_bound (n m : ℕ) :
    ‖d.IO n m‖^2 ≤ (eta N)^2 * (1/2 : ℝ)^n * (1/2 : ℝ)^m := by
  have he := eta_bounds N
  have hr : d.beta*d.gamma = ‖d.inputRatio‖ * ‖d.outputRatio‖ := by
    simp only [inputRatio, outputRatio, norm_mul, norm_div, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos d.beta_pos, abs_of_pos d.gamma_pos]
    field_simp [norm_ne_zero_iff.mpr d.T_ne]
  have ht : d.beta*d.gamma ≤ (eta N)^2 := by
    rw [hr]; nlinarith [d.ratio_bounds.2.1, d.ratio_bounds.2.2,
      norm_nonneg d.inputRatio, norm_nonneg d.outputRatio]
  have ht' : d.beta*d.gamma ≤ (1/2 : ℝ) := by nlinarith
  by_cases h : n = m
  · subst m
    simp only [IO, if_pos rfl, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (mul_pos d.beta_pos d.gamma_pos), mul_pow]
    rw [Real.sq_sqrt (mul_pos d.beta_pos d.gamma_pos).le]
    calc
      _ = (d.beta*d.gamma) * ((d.beta*d.gamma)^2)^n := by ring
      _ ≤ (eta N)^2 * ((1/2 : ℝ)^2)^n := by gcongr
      _ = _ := by rw [mul_assoc, ← mul_pow, ← pow_mul, ← pow_mul]
  · simp only [IO, if_neg h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity

def blockMajorant (a b : Fin 3) : ℝ :=
  ![![(eta N)^4/4, 4*(eta N)^3, 4*(eta N)^3],
    ![4*(eta N)^3, 0, (eta N)^2],
    ![4*(eta N)^3, (eta N)^2, 0]] a b

private lemma block_nonneg (a b : Fin 3) : 0 ≤ blockMajorant (N := N) a b := by
  fin_cases a <;> fin_cases b <;> simp [blockMajorant] <;> positivity

private lemma scalar_bound (a b : Fin 3) (n m : ℕ) :
    ‖d.scalar a b n m‖^2 ≤ blockMajorant (N := N) a b *
      (1/2 : ℝ)^n * (1/2 : ℝ)^m := by
  fin_cases a <;> fin_cases b <;> simp only [scalar, blockMajorant, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.cons_val_fin_one]
  · exact d.ss_square_bound n m
  · exact d.si_square_bound n m
  · exact d.so_square_bound n m
  · simpa [mul_assoc, mul_comm, mul_left_comm] using d.si_square_bound m n
  · simp
  · exact d.io_square_bound n m
  · simpa [mul_assoc, mul_comm, mul_left_comm] using d.so_square_bound m n
  · simpa [mul_assoc, mul_comm, mul_left_comm] using d.io_square_bound m n
  · simp

theorem entry_symmetric (i j : Index N) : d.entry i j = d.entry j i := by
  rcases i with ⟨c, a, n⟩
  rcases j with ⟨c', b, m⟩
  by_cases h : c = c'
  · subst c'
    simp only [entry, if_pos rfl]
    fin_cases a <;> fin_cases b <;> simp [scalar, ss_symm]
  · simp [entry, h, Ne.symm h]

private def envelope (p : Index N × Index N) : ℝ :=
  if p.1.1 = p.2.1 then blockMajorant (N := N) p.1.2.1 p.2.2.1 *
    (1/2 : ℝ)^p.1.2.2 * (1/2 : ℝ)^p.2.2.2 else 0

private lemma envelope_nonneg (p : Index N × Index N) : 0 ≤ envelope p := by
  dsimp [envelope]
  split_ifs <;> positivity [block_nonneg]

private lemma envelope_summable : Summable (envelope (N := N)) := by
  have hg : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hi : Summable (fun i : Index N => (1/2 : ℝ)^i.2.2) := by
    simpa using (summable_fintype (fun _ : Fin N => (1 : ℝ))).mul_of_nonneg
      ((summable_fintype (fun _ : Fin 3 => (1 : ℝ))).mul_of_nonneg hg
        (fun _ => by positivity) (fun _ => by positivity))
      (fun _ => by positivity) (fun _ => by positivity)
  let C : ℝ := (eta N)^4/4 + 4*(eta N)^3 + (eta N)^2
  have hc : ∀ a b, blockMajorant (N := N) a b ≤ C := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [blockMajorant, C] <;>
      nlinarith [eta_bounds N |>.1]
  apply Summable.of_nonneg_of_le envelope_nonneg _
    ((hi.mul_of_nonneg hi (fun _ => by positivity) (fun _ => by positivity)).mul_left C)
  intro p
  dsimp [envelope]
  split_ifs
  · calc
      _ ≤ C * (1/2 : ℝ)^p.1.2.2 * (1/2 : ℝ)^p.2.2.2 := by gcongr; apply hc
      _ = _ := by ring
  · dsimp [C]; positivity

private lemma envelope_mass :
    (∑' p : Index N × Index N, envelope p) =
      (N : ℝ) * ((eta N)^4 + 64*(eta N)^3 + 8*(eta N)^2) := by
  classical
  have hg : (∑' n : ℕ, (1/2 : ℝ)^n) = 2 := by
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hinner (i : Index N) :
      (∑' j : Index N, envelope (i,j)) =
        ∑ b : Fin 3, blockMajorant (N := N) i.2.1 b * (1/2 : ℝ)^i.2.2 * 2 := by
    rw [(envelope_summable.prod_factor i).tsum_prod]
    simp_rw [tsum_fintype]
    simp only [envelope]
    simp_rw [tsum_prod, tsum_fintype]
    simp_rw [tsum_ite_left]
    simp only [tsum_mul_left, hg]
    simp
  rw [envelope_summable.tsum_prod]
  simp_rw [hinner]
  rw [tsum_prod]
  simp_rw [tsum_fintype, tsum_prod, tsum_fintype, tsum_finsetSum]
  simp only [mul_assoc, tsum_mul_left, tsum_mul_right, hg]
  simp [blockMajorant, Fin.sum_univ_succ]
  ring

def massBound (N : ℕ) : ℝ := 13 * N * (eta N)^2

private lemma massBound_lt (N : ℕ) : massBound N < 1/4 := by
  unfold massBound eta
  have hp : 0 < (N : ℝ)+1 := by positivity
  apply (div_lt_iff₀ (by positivity : 0 < (16*((N : ℝ)+1))^2)).mp ?_
  field_simp
  nlinarith [sq_nonneg (N : ℝ)]

/-- All colors and all frequencies have finite matrix square mass; the two
orientations of every mixed block are both included in the estimate. -/
theorem matrix_square_mass :
    Summable (fun p : Index N × Index N => ‖d.entry p.1 p.2‖^2) ∧
      (∑' p : Index N × Index N, ‖d.entry p.1 p.2‖^2) ≤ massBound N := by
  have hle (p : Index N × Index N) : ‖d.entry p.1 p.2‖^2 ≤ envelope p := by
    dsimp [entry, envelope]
    split_ifs
    · exact d.scalar_bound _ _ _ _
    · simp
  have hs := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle envelope_summable
  refine ⟨hs, (hs.tsum_le_tsum hle envelope_summable).trans ?_⟩
  rw [envelope_mass]
  have he := eta_bounds N
  have he2 : (eta N)^2 ≤ 1 := by nlinarith
  have he3 : 64*(eta N)^3 ≤ 4*(eta N)^2 := by nlinarith [sq_nonneg (eta N)]
  unfold massBound
  gcongr
  nlinarith [sq_nonneg (eta N), mul_le_mul_of_nonneg_right he2 (sq_nonneg (eta N))]

private def column (j : Index N) : Space N :=
  ⟨fun i => d.entry i j, (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    (by simpa using ((d.matrix_square_mass.1.prod_symm.prod_factor j)))⟩

private lemma column_norm (j : Index N) :
    ‖d.column j‖^2 = ∑' i : Index N, ‖d.entry i j‖^2 := by
  simpa [column] using lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (d.column j)

private def coordinateBasis : HilbertBasis (Index N) ℂ (Space N) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

private def basisSet : Set (Space N) := Set.range (coordinateBasis (N := N))

private def basisEquiv : Index N ≃ basisSet (N := N) :=
  Equiv.ofInjective coordinateBasis coordinateBasis.orthonormal.linearIndependent.injective

private def setBasis : HilbertBasis (basisSet (N := N)) ℂ (Space N) :=
  HilbertBasis.mk coordinateBasis.orthonormal.toSubtypeRange (by
    apply top_le_iff.mpr
    simpa only [Subtype.range_coe] using coordinateBasis.dense_span)

private lemma setBasis_apply (j : Index N) :
    setBasis (basisEquiv j) = lp.single 2 j (1 : ℂ) := by
  change (HilbertBasis.mk _ _) (basisEquiv j) = _
  rw [HilbertBasis.coe_mk]
  rfl

private theorem synthesized :
    ∃ A : Space N →L[ℂ] Space N,
      (∀ i j, A (lp.single 2 j (1 : ℂ)) i = d.entry i j) ∧
      HilbertSchmidt.IsHilbertSchmidt A ∧ ‖A‖ ≤ Real.sqrt (massBound N) := by
  let e := basisEquiv (N := N)
  have hc : Summable (fun j : Index N => ‖d.column j‖^2) := by
    simpa only [d.column_norm] using d.matrix_square_mass.1.prod_symm.prod
  have hv : Summable (fun j : basisSet (N := N) => ‖d.column (e.symm j)‖^2) :=
    e.symm.summable_iff.mpr hc
  obtain ⟨A, hcol, hhs, hsum, hnorm⟩ :=
    HilbertSchmidt.exists_hilbertSchmidt_of_square_summable_columns
      (setBasis (N := N)) (fun j => d.column (e.symm j)) hv
  refine ⟨A, ?_, hhs, hnorm.trans ?_⟩
  · intro i j
    have h := hcol (e j)
    rw [e.symm_apply_apply, setBasis_apply] at h
    exact congrArg (fun x : Space N => x i) h
  · apply Real.sqrt_le_sqrt
    rw [← e.symm.tsum_eq]
    simp only [e.apply_symm_apply]
    simp_rw [d.column_norm]
    rw [← d.matrix_square_mass.1.prod_symm.tsum_prod,
      d.matrix_square_mass.1.tsum_comm]
    exact d.matrix_square_mass.2

/-- The actual complex-linear one-particle operator, obtained from its native columns. -/
def operator : Space N →L[ℂ] Space N := Classical.choose d.synthesized

/-- Exact native matrix entries, holomorphic transpose symmetry and strict
one-particle contraction. This does not identify a full field coefficient operator. -/
theorem operator_realization :
    (∀ i j, d.operator (lp.single 2 j (1 : ℂ)) i = d.entry i j) ∧
    (∀ i j, d.entry i j = d.entry j i) ∧
    HilbertSchmidt.IsHilbertSchmidt d.operator ∧
    ‖d.operator‖ ≤ Real.sqrt (massBound N) ∧ ‖d.operator‖ < 1/2 := by
  obtain ⟨hentry, hhs, hnorm⟩ := Classical.choose_spec d.synthesized
  refine ⟨hentry, d.entry_symmetric, hhs, hnorm, hnorm.trans_lt ?_⟩
  exact (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 1/2)).mpr (by
    convert massBound_lt N using 1 <;> norm_num)

#print axioms operator_realization

end Damping
end D5.S3.VertexAlgebra.TwistedGround.NeutralThreeLegGaussianKernel
