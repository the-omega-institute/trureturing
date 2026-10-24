/- GID: D5/S3/Analytic/KarpZhangNinh/Homogeneous
   generality: G
   mirror-B: D5/B/S3/Analytic/KarpZhangNinh/Homogeneous
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum, mathlib/module/Mathlib.Analysis.Calculus.Deriv.MeanValue]
   utility: none
   digest: Homogeneous trisection balancing and its positive coefficient expansion. -/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
admission_basis: escape-witness; witness: residue_filter.
The trisection sums are evaluated by a six-periodic recurrence. All variables
and degrees remain arbitrary; no numerical certificate is used.
-/
noncomputable section
set_option maxHeartbeats 400000
open Finset
namespace D5.S3.Analytic.KarpZhangNinh.Homogeneous

/- proof_shape: bind-only definition; escape_witness: none; consumer: residue_succ, residue_filter. -/
def residue (n r : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ) * if k % 3 = r then 1 else 0

/- proof_shape: bind-only; escape_witness: none; consumer: residue_filter. -/
private lemma residue_succ (n r : ℕ) (hr : r < 3) :
    residue (n+1) r = residue n r + residue n ((r+2)%3) := by
  unfold residue
  rw [show n + 1 + 1 = n + 2 by omega,
    Finset.sum_choose_succ_mul (fun k _ => if k % 3 = r then (1:ℤ) else 0) n]
  congr 1
  apply sum_congr rfl
  intro k hk
  have hm : (k+1)%3=r ↔ k%3=(r+2)%3 := by omega
  rw [hm]

/- proof_shape: bind-only definition; escape_witness: none; consumer: residue_filter. -/
def periodic (q : ℕ) : ℤ :=
  match q % 6 with
  | 0 => 2
  | 1 => 1
  | 2 => -1
  | 3 => -2
  | 4 => -1
  | _ => 1

/- proof_shape: content; escape_witness: residue_filter; consumer: weighted_filter. -/
theorem residue_filter (n : ℕ) :
    (3 * residue n 0 = 2^n + periodic n) ∧
    (3 * residue n 1 = 2^n + periodic (n+4)) ∧
    (3 * residue n 2 = 2^n + periodic (n+2)) := by
  induction n with
  | zero => norm_num [residue, periodic]
  | succ n ih =>
    rw [residue_succ n 0 (by omega), residue_succ n 1 (by omega),
      residue_succ n 2 (by omega)]
    norm_num only [Nat.reduceAdd, Nat.reduceMod]
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases h : n % 6 <;>
      simp only [periodic, Nat.add_mod, Nat.mod_mod, h] at * <;>
      norm_num at * <;> simp only [pow_succ] <;> omega

/- proof_shape: bind-only definition; escape_witness: none; consumer: weighted_succ, A, T. -/
def weighted (n r : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ) * k * if k % 3 = r then 1 else 0

/- proof_shape: bind-only; escape_witness: none; consumer: A_formula, T_formula. -/
private lemma weighted_succ (n r : ℕ) (hr : r < 3) :
    weighted (n+1) r = (n+1) * residue n ((r+2)%3) := by
  unfold weighted residue
  rw [show n + 1 + 1 = (n+1)+1 by omega, sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hc : ((n+1).choose (k+1) : ℤ) * (k+1) =
      (n+1) * (n.choose k : ℤ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hc]
  have hm : (k+1)%3=r ↔ k%3=(r+2)%3 := by omega
  rw [hm]
  ring

/- proof_shape: bind-only definition; escape_witness: none; consumer: second_succ, T. -/
def second (n r : ℕ) : ℤ :=
  ∑ k ∈ range (n+1), (n.choose k : ℤ) * k * ((k:ℤ)-1) *
    if k % 3 = r then 1 else 0

/- proof_shape: bind-only; escape_witness: none; consumer: T_formula. -/
private lemma second_succ (n r : ℕ) (hr : r < 3) :
    second (n+1) r = (n+1) * weighted n ((r+2)%3) := by
  unfold second weighted
  rw [sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, add_zero]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hc : ((n+1).choose (k+1) : ℤ) * (k+1) =
      (n+1) * (n.choose k : ℤ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq n k).symm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hc]
  have hm : (k+1)%3=r ↔ k%3=(r+2)%3 := by omega
  rw [hm]
  ring

/- proof_shape: bind-only definition; escape_witness: none; consumer: A_formula, A_nonneg, T_formula. -/
def A (n : ℕ) : ℤ := weighted n 0 - 2 * weighted (n-1) 0

/- proof_shape: bind-only definition; escape_witness: none; consumer: T_formula, T_nonneg, derivative_expansion. -/
def T (n N : ℕ) : ℤ :=
  ((N:ℤ)-1) * A n - (second n 0 - 2 * second (n-1) 0)

/- proof_shape: bind-only definition; escape_witness: none; consumer: A_formula, A_nonneg, T_formula. -/
def alpha (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => -3*n+4
  | 1 => -3*n+2
  | 2 => -2
  | 3 => 3*n-4
  | 4 => 3*n-2
  | _ => 2

/- proof_shape: bind-only definition; escape_witness: none; consumer: T_formula, T_nonneg. -/
def beta (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => -3*n+4
  | 1 => -4
  | 2 => 3*n-8
  | 3 => 3*n-4
  | 4 => 4
  | _ => -3*n+8

/- proof_shape: content; escape_witness: residue_filter; consumer: A_nonneg, T_nonneg. -/
theorem A_formula (n : ℕ) (hn : 1 ≤ n) :
    3 * A n = 2^(n-1) + alpha n := by
  rcases n with _|_|n
  · omega
  · norm_num [A, weighted, alpha, sum_range_succ]
  · simp only [A, Nat.add_one_sub_one, weighted_succ _ 0 (by omega)]
    have h₁ := (residue_filter (n+1)).2.2
    have h₂ := (residue_filter n).2.2
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases h : n % 6 <;>
      simp [alpha, periodic, Nat.add_mod, h, pow_succ] at * <;>
      linear_combination ((n:ℤ)+2)*h₁ - 2*((n:ℤ)+1)*h₂

/- proof_shape: content; escape_witness: residue_filter; consumer: T_nonneg. -/
theorem T_formula (n N : ℕ) (hn : 1 ≤ n) :
    3 * T n N = ((N:ℤ)-n)*2^(n-1) + ((N:ℤ)-1)*alpha n -
      ((n:ℤ)-1)*beta n := by
  rw [T, mul_sub, mul_left_comm 3, A_formula n hn]
  suffices h : 3 * (second n 0 - 2 * second (n-1) 0) =
      ((n:ℤ)-1)*(2^(n-1)+beta n) by rw [h]; ring
  rcases n with _|_|_|n
  · omega
  · norm_num [second, beta, sum_range_succ]
  · norm_num [second, beta, sum_range_succ]
  · simp only [Nat.add_one_sub_one, second_succ _ 0 (by omega),
      weighted_succ _ 2 (by omega)]
    norm_num only [Nat.reduceAdd, Nat.reduceMod]
    have h₁ := (residue_filter (n+1)).2.1
    have h₂ := (residue_filter n).2.1
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    interval_cases h : n % 6 <;>
      simp [beta, periodic, Nat.add_mod, h, pow_succ] at * <;>
      linear_combination ((n:ℤ)+3)*((n:ℤ)+2)*h₁ -
        2*((n:ℤ)+2)*((n:ℤ)+1)*h₂

/- proof_shape: content; escape_witness: power_linear; consumer: A_nonneg. -/
private lemma power_linear (n : ℕ) (hn : 5 ≤ n) : (3:ℤ)*n-2 ≤ 2^(n-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have he : n+1-1=(n-1)+1 := by omega
    rw [he, pow_succ]
    push_cast
    omega

/- proof_shape: content; escape_witness: power_quadratic_one; consumer: T_nonneg. -/
private lemma power_quadratic_one (n : ℕ) (hn : 7 ≤ n) :
    (3:ℤ)*n^2-3*n+2 ≤ 2^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ (2:ℤ) n]
    have hn' : (7:ℤ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith

/- proof_shape: content; escape_witness: power_quadratic_two; consumer: T_nonneg. -/
private lemma power_quadratic_two (n : ℕ) (hn : 8 ≤ n) :
    (3:ℤ)*n^2-9*n+8 ≤ 2^(n-1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have he : n+1-1=(n-1)+1 := by omega
    rw [he, pow_succ (2:ℤ) (n-1)]
    have hn' : (8:ℤ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith

/- proof_shape: content; escape_witness: power_linear; consumer: T_nonneg. -/
theorem A_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ A n := by
  have hf := A_formula n hn
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [A, weighted, sum_range_succ] at *
  · have hpow := power_linear n (by omega)
    have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
    have hl : -3*(n:ℤ)+2 ≤ alpha n := by
      interval_cases h : n % 6 <;> simp [alpha, h] <;> omega
    omega

/- proof_shape: content; escape_witness: power_quadratic_one, power_quadratic_two;
consumer: derivative_nonneg, derivative_pos. -/
theorem T_nonneg (n N : ℕ) (hn : 1 ≤ n) (hN : N % 3 = 0) (hnN : n < N) :
    0 ≤ T n N := by
  have hf := T_formula n N hn
  have ha : 0 ≤ 2^(n-1) + alpha n := by
    rw [← A_formula n hn]
    exact mul_nonneg (by norm_num) (A_nonneg n hn)
  have ha0 := ha
  have hm : n % 6 < 6 := Nat.mod_lt _ (by omega)
  have hn' : (1:ℤ) ≤ n := by exact_mod_cast hn
  have hgap : (1:ℤ) ≤ (N:ℤ)-n := by omega
  interval_cases h : n % 6
  · simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]
  · by_cases he : n=1
    · subst n; norm_num [alpha, beta] at hf; omega
    · have h7 : 7 ≤ n := by omega
      have hpow := power_quadratic_one n h7
      have hg : (2:ℤ) ≤ (N:ℤ)-n := by omega
      have hepow : (2:ℤ)^n=2*2^(n-1) := by
        conv_lhs => rw [show n=(n-1)+1 by omega, pow_succ]
        ring
      simp [alpha, beta, h] at hf ha
      rw [hepow] at hpow
      nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n-2) ha0]
  · by_cases he : n=2
    · subst n; norm_num [alpha, beta] at hf; omega
    · have h8 : 8 ≤ n := by omega
      have hpow := power_quadratic_two n h8
      simp [alpha, beta, h] at hf ha
      nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n-1) ha0]
  · simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]
  · have hn4 : (4:ℤ) ≤ n := by omega
    simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]
  · have hn5 : (5:ℤ) ≤ n := by omega
    simp [alpha, beta, h] at hf ha
    nlinarith [mul_nonneg (by omega : (0:ℤ) ≤ (N:ℤ)-n) ha0]

/- proof_shape: bind-only definition; escape_witness: none;
consumer: P, betaLift. -/
def coeff (N k : ℕ) : ℝ :=
  if k % 3 = 0 then (k:ℝ) * (N-k) * N.choose k else 0

/- proof_shape: bind-only definition; escape_witness: none;
consumer: derivative_expansion, strictMonoOn_slice, BetaLifting.lift_monoOn. -/
def P (N : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ range (N+1), coeff N k * x^k * y^(N-k)

/- proof_shape: bind-only; escape_witness: none; consumer: Result.Z_monotoneOn. -/
theorem coeff_symm (N k : ℕ) (hN : N % 3 = 0) (hk : k ≤ N) :
    coeff N (N-k) = coeff N k := by
  have hm : (N-k)%3=0 ↔ k%3=0 := by omega
  simp only [coeff, Nat.choose_symm hk, hm]
  rw [Nat.cast_sub hk]
  split_ifs <;> ring

/- proof_shape: bind-only definition; escape_witness: none;
consumer: shear, derivative_coeff, derivative_expansion. -/
def B (N t : ℕ) : ℝ :=
  (N.choose t : ℝ) * ((((N:ℤ)-1)*weighted (N-t) 0-second (N-t) 0 : ℤ):ℝ)

/- proof_shape: bind-only; escape_witness: none; consumer: shear. -/
private lemma choose_exchange (N k t : ℕ) (hk : k ≤ N) (ht : t ≤ N-k) :
    (N.choose k : ℝ) * (N-k).choose t =
      (N.choose t : ℝ) * (N-t).choose k := by
  have h := Nat.choose_mul (n:=N) (k:=N-k) (s:=t) ht
  rw [Nat.choose_symm hk] at h
  have he : N-k-t=N-t-k := by omega
  rw [he, Nat.choose_symm (by omega : k ≤ N-t)] at h
  exact_mod_cast h

/- proof_shape: bind-only; escape_witness: none; consumer: shear. -/
private lemma moment_sum (N n : ℕ) (hn : n ≤ N) :
    (∑ k ∈ range (n+1),
      (if k%3=0 then (k:ℝ)*(N-k) else 0)*(n.choose k : ℝ)) =
    ((((N:ℤ)-1)*weighted n 0-second n 0 : ℤ):ℝ) := by
  simp only [weighted, second, Int.cast_sub, Int.cast_mul, Int.cast_sum,
    Int.cast_ofNat, Int.cast_natCast, Int.cast_one, mul_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro k hk
  have hkN : k ≤ N := (Nat.le_of_lt_succ (mem_range.mp hk)).trans hn
  split_ifs <;> simp <;> ring

/- proof_shape: bind-only; escape_witness: none; consumer: derivative_expansion. -/
private theorem shear (N : ℕ) (x d : ℝ) :
    P N x (x+d) = ∑ t ∈ range (N+1), B N t*x^(N-t)*d^t := by
  unfold P
  calc
    _ = ∑ k ∈ range (N+1), ∑ t ∈ range (N+1),
        coeff N k * ((N-k).choose t : ℝ) * x^(N-t)*d^t := by
      apply sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.le_of_lt_succ (mem_range.mp hk)
      rw [add_comm x d, add_pow, mul_sum]
      calc
        _ = ∑ t ∈ range (N-k+1),
            coeff N k*((N-k).choose t : ℝ)*x^(N-t)*d^t := by
          apply sum_congr rfl
          intro t ht
          have htN : t ≤ N-k := Nat.le_of_lt_succ (mem_range.mp ht)
          have he : k+(N-k-t)=N-t := by omega
          rw [show coeff N k * x^k *
              (d^t*x^(N-k-t)*((N-k).choose t:ℝ)) =
              coeff N k*((N-k).choose t:ℝ)*(x^k*x^(N-k-t))*d^t by ring,
            ← pow_add, he]
        _ = _ := by
          apply sum_subset (range_mono (by omega))
          intro t ht hnot
          have ht' : N-k < t := by simp only [mem_range] at hnot; omega
          rw [Nat.choose_eq_zero_of_lt ht', Nat.cast_zero]
          ring
    _ = ∑ t ∈ range (N+1), ∑ k ∈ range (N+1),
        coeff N k*((N-k).choose t:ℝ)*x^(N-t)*d^t := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro t ht
      have htN : t ≤ N := Nat.le_of_lt_succ (mem_range.mp ht)
      rw [← sum_mul, ← sum_mul]
      congr 2
      calc
        _ = ∑ k ∈ range (N-t+1), coeff N k*((N-k).choose t:ℝ) := by
          symm
          apply sum_subset (range_mono (by omega))
          intro k hk hnot
          have hk' : N-t < k := by simp only [mem_range] at hnot; omega
          have hkN : k ≤ N := Nat.le_of_lt_succ (mem_range.mp hk)
          rw [Nat.choose_eq_zero_of_lt (by omega : N-k < t), Nat.cast_zero, mul_zero]
        _ = (N.choose t:ℝ) * ∑ k ∈ range (N-t+1),
            (if k%3=0 then (k:ℝ)*(N-k) else 0)*((N-t).choose k:ℝ) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k hk
          have hkN : k ≤ N := by simp only [mem_range] at hk; omega
          have htk : t ≤ N-k := by simp only [mem_range] at hk; omega
          unfold coeff
          have he := choose_exchange N k t hkN htk
          split_ifs
          · linear_combination (k:ℝ)*((N:ℝ)-k)*he
          · simp
        _ = B N t := by rw [moment_sum N (N-t) (by omega)]; rfl

/- proof_shape: bind-only; escape_witness: none; consumer: derivative_expansion. -/
private lemma derivative_coeff (N t : ℕ) (ht : t < N) :
    (N-t:ℕ)*B N t - 2*(t+1:ℕ)*B N (t+1) =
      (N-t:ℕ)*(N.choose t:ℝ)*(T (N-t) N:ℝ) := by
  have hc : (N.choose (t+1):ℝ)*((t+1:ℕ):ℝ) =
      (N.choose t:ℝ)*((N-t:ℕ):ℝ) := by
    exact_mod_cast (Nat.choose_succ_right_eq N t)
  have he : N-(t+1)=N-t-1 := by omega
  unfold B T A
  rw [he]
  push_cast at hc ⊢
  linear_combination -2 * (((N:ℝ)-1)*(weighted (N-t-1) 0:ℝ)-(second (N-t-1) 0:ℝ)) * hc

/- proof_shape: bind-only; escape_witness: none; consumer: derivative_expansion. -/
private lemma collect_derivative (N : ℕ) (x d : ℝ) :
    (∑ t ∈ range (N+1), B N t *
      (((N-t:ℕ):ℝ)*x^(N-t-1)*d^t - 2*(t:ℝ)*x^(N-t)*d^(t-1))) =
    ∑ t ∈ range N, (((N-t:ℕ):ℝ)*B N t - 2*((t+1:ℕ):ℝ)*B N (t+1))*
      x^(N-t-1)*d^t := by
  simp_rw [mul_sub]
  rw [sum_sub_distrib, sum_range_succ, sum_range_succ']
  simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, zero_add, add_zero,
    Nat.add_one_sub_one]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro t ht
  have he : N-(t+1)=N-t-1 := by omega
  rw [he]
  ring

/- proof_shape: bind-only definition; escape_witness: none;
consumer: hasDerivAt_slice, derivative_expansion. -/
def D (N : ℕ) (x d : ℝ) : ℝ :=
  ∑ t ∈ range N, ((N-t:ℕ):ℝ)*(N.choose t:ℝ)*(T (N-t) N:ℝ)*x^(N-t-1)*d^t

/- proof_shape: bind-only; escape_witness: none;
consumer: strictMonoOn_slice. -/
theorem hasDerivAt_slice (N : ℕ) (S x : ℝ) :
    HasDerivAt (fun s => P N s (S-s)) (D N x (S-2*x)) x := by
  have hfun : (fun s => P N s (S-s)) =
      (fun s => ∑ t ∈ range (N+1), B N t*s^(N-t)*(S-2*s)^t) := by
    funext s
    rw [show S-s=s+(S-2*s) by ring, shear]
  rw [hfun]
  have hder := HasDerivAt.fun_sum (u:=range (N+1)) (fun t _ =>
    (((hasDerivAt_id x).pow (N-t)).const_mul (B N t)).mul
      (((hasDerivAt_const x S).sub ((hasDerivAt_id x).const_mul 2)).pow t))
  convert hder using 1
  have hD : D N x (S-2*x) =
      ∑ t ∈ range (N+1), B N t *
        (((N-t:ℕ):ℝ)*x^(N-t-1)*(S-2*x)^t -
          2*(t:ℝ)*x^(N-t)*(S-2*x)^(t-1)) := by
    rw [collect_derivative]
    unfold D
    apply sum_congr rfl
    intro t ht
    rw [derivative_coeff N t (mem_range.mp ht)]
  rw [hD]
  simp only [id_eq, mul_one, zero_sub]
  apply sum_congr rfl
  intro t ht
  ring

/- proof_shape: bind-only; escape_witness: none;
consumer: derivative_expansion. -/
private lemma T_diagonal (N : ℕ) (hN : N%3=0) : T N N = 0 := by
  by_cases hzero : N=0
  · subst N; norm_num [T, A, weighted, second]
  · have hf := T_formula N N (by omega)
    have hm : N%6<6 := Nat.mod_lt _ (by omega)
    interval_cases h : N%6 <;> simp [alpha, beta, h] at hf <;> omega

/- proof_shape: bind-only definition; escape_witness: none;
consumer: derivative_expansion, K_pos. -/
def K (N : ℕ) (x d : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 (N-1), (n:ℝ)*(N.choose n:ℝ)*(T n N:ℝ)*x^(n-1)*d^(N-n-1)

/- proof_shape: bind-only; escape_witness: none;
consumer: strictMonoOn_slice. -/
theorem derivative_expansion (N : ℕ) (hN : N%3=0) (x d : ℝ) :
    D N x d = d*K N x d := by
  unfold D K
  calc
    _ = ∑ t ∈ Icc 1 (N-1),
        ((N-t:ℕ):ℝ)*(N.choose t:ℝ)*(T (N-t) N:ℝ)*x^(N-t-1)*d^t := by
      symm
      apply sum_subset
      · intro t ht; simp only [mem_Icc, mem_range] at *; omega
      · intro t ht hnot
        have hz : t=0 := by simp only [mem_Icc, mem_range] at *; omega
        subst t
        rw [Nat.sub_zero, T_diagonal N hN, Int.cast_zero]
        ring
    _ = ∑ n ∈ Icc 1 (N-1),
        (n:ℝ)*(N.choose n:ℝ)*(T n N:ℝ)*x^(n-1)*d^(N-n) := by
      refine sum_nbij' (fun t => N-t) (fun n => N-n) ?_ ?_ ?_ ?_ ?_
      · intro t ht; simp only [mem_Icc] at *; omega
      · intro n hn; simp only [mem_Icc] at *; omega
      · intro t ht; simp only [mem_Icc] at *; omega
      · intro n hn; simp only [mem_Icc] at *; omega
      · intro t ht
        have htN : t ≤ N := by simp only [mem_Icc] at ht; omega
        rw [Nat.sub_sub_self htN, Nat.choose_symm htN]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro n hn
      have he : N-n=(N-n-1)+1 := by simp only [mem_Icc] at hn; omega
      rw [show d^(N-n)=d^(N-n-1)*d by rw [he, pow_succ]]
      ring

/- proof_shape: content; escape_witness: T_nonneg; consumer: strictMonoOn_slice. -/
private theorem K_pos (N : ℕ) (hN : N%3=0) (h6 : 6 ≤ N) {x d : ℝ}
    (hx : 0 < x) (hd : 0 < d) : 0 < K N x d := by
  apply sum_pos'
  · intro n hn
    have hns := mem_Icc.mp hn
    have hT : (0:ℝ) ≤ (T n N:ℝ) := by
      exact_mod_cast T_nonneg n N hns.1 hN (by omega)
    positivity
  · refine ⟨3, by simp only [mem_Icc]; omega, ?_⟩
    have hT : T 3 N = 3*((N:ℤ)-3) := by norm_num [T, A, weighted, second, sum_range_succ]; ring
    have hTp : (0:ℝ) < (T 3 N:ℝ) := by rw [hT]; push_cast; exact_mod_cast (by omega : (0:ℤ) < 3*((N:ℤ)-3))
    have hc : (0:ℝ) < (N.choose 3:ℝ) := by exact_mod_cast Nat.choose_pos (by omega : 3≤N)
    positivity

/- proof_shape: content; escape_witness: K_pos;
consumer: Result.full_tail_nonneg. -/
theorem strictMonoOn_slice (m : ℕ) (hm : 2 ≤ m) :
    StrictMonoOn (fun t => P (3*m) t (1-t)) (Set.Ioc 0 (1/2:ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 (1/2:ℝ))
  · intro x hx
    exact (hasDerivAt_slice (3*m) 1 x).continuousAt.continuousWithinAt
  · intro x hx
    simp only [interior_Ioc, Set.mem_Ioo] at hx
    rw [(hasDerivAt_slice (3*m) 1 x).deriv, derivative_expansion (3*m) (by omega)]
    exact mul_pos (by linarith) (K_pos (3*m) (by omega) (by omega) hx.1 (by linarith))


end D5.S3.Analytic.KarpZhangNinh.Homogeneous
