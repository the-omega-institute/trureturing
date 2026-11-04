/- GID: D5/S1/Recurrence/Algebraic/HannaGaussianKernelParity
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/HannaGaussianKernelParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric Gaussian kernel coefficients determine integral parity. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none (all declarations below).
weight: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_pair, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.supported_matrix_integral, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_odd, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_symmetric, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_zero_left, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_zero_right, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.diagonal_parity, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.diagonal_parity, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
weight_zero_left: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_odd, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_symmetric, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_zero_right.
weight_zero_right: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_odd, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_symmetric.
weight_symmetric: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_symmetric;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_pair.
weight_odd: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.weight_odd;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.diagonal_parity, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.diagonal_parity.
kernel: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_constant, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_expansion, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_pair, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_step, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_zero_coeff, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.supported_matrix_integral, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.coefficient_matrix, D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.coefficient_matrix, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
kernel_constant: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient.
kernel_step: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient.
kernel_zero_coeff: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient.
kernel_coefficient: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_pair, D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.supported_matrix_integral.
phase_diagonal: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.supported_matrix_integral.
phase_pair: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_pair.
kernel_pair: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.supported_matrix_integral.
matrix_integral: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.supported_matrix_integral.
kernel_expansion: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.coefficient_matrix, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.coefficient_matrix.
expansion_coefficient: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.shifted_expansion_coefficient, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.coefficient_matrix.
shifted_expansion_coefficient: proof_shape: bind-only; escape_witness: none;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.coefficient_matrix.
supported_matrix_integral: proof_shape: content; escape_witness: D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity.kernel_coefficient;
  consumers: D5.S1.Recurrence.Algebraic.HannaGaussianShiftedSquareParity.result, D5.S1.Recurrence.Algebraic.HannaGaussianSquareParity.result.
The coefficient identity is established by nested natural-number induction.
The recursive integer array is used directly; no path-counting object is introduced.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22307
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand

namespace D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
open PowerSeries
open scoped BigOperators

def weight : ℕ → ℕ → ℤ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | m + 1, k + 1 => weight m (k+1) + weight (m+1) k + weight m k
termination_by m k => m+k

@[simp] private theorem weight_zero_left (k : ℕ) : weight 0 k = 1 := by simp [weight]
@[simp] private theorem weight_zero_right (m : ℕ) : weight m 0 = 1 := by cases m <;> simp [weight]

private theorem weight_symmetric (m k : ℕ) : weight m k = weight k m := by
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
    cases m with
    | zero => simp
    | succ m =>
      induction k with
      | zero => simp
      | succ k hk =>
        rw [weight, weight, ih m (by omega) (k+1), ih m (by omega) k, hk]
        ring

theorem weight_odd (m k : ℕ) : Odd (weight m k) := by
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
    cases m with
    | zero => simp
    | succ m =>
      induction k with
      | zero => simp
      | succ k hk =>
        rw [weight]
        obtain ⟨a, ha⟩ := ih m (by omega) (k+1)
        obtain ⟨b, hb⟩ := hk
        obtain ⟨c, hc⟩ := ih m (by omega) k
        exact ⟨a+b+c+1, by omega⟩

noncomputable def kernel (m : ℕ) : PowerSeries ℂ :=
  (X + C Complex.I)^m * ((1 + C Complex.I * X)^(m+1))⁻¹

@[simp] private theorem kernel_constant (m : ℕ) : constantCoeff (kernel m) = Complex.I^m := by
  simp [kernel]

private theorem kernel_step (m : ℕ) :
    (1 + C Complex.I * X) * kernel (m+1) = (X + C Complex.I) * kernel m := by
  let a : PowerSeries ℂ := X + C Complex.I
  let b : PowerSeries ℂ := 1 + C Complex.I * X
  have hb : constantCoeff b ≠ 0 := by simp [b]
  have hbi : b * b⁻¹ = 1 := PowerSeries.mul_inv_cancel b hb
  simp only [kernel, ← PowerSeries.inv_pow]
  change b * (a^(m+1) * (b⁻¹)^(m+1+1)) = a * (a^m * (b⁻¹)^(m+1))
  rw [pow_succ a m, pow_succ (b⁻¹) (m+1)]
  calc
    _ = (b*b⁻¹) * (a * (a^m * (b⁻¹)^(m+1))) := by ring
    _ = _ := by rw [hbi, one_mul]

private theorem kernel_zero_coeff (k : ℕ) : coeff k (kernel 0) = (-Complex.I)^k := by
  have h : rescale (-Complex.I) (mk 1 : PowerSeries ℂ) *
      (1 + C Complex.I * X) = 1 := by
    simpa only [map_mul, map_sub, map_one, rescale_X, map_neg,
      neg_mul, sub_neg_eq_add] using
      congrArg (rescale (-Complex.I)) (mk_one_mul_one_sub_eq_one ℂ)
  have he : rescale (-Complex.I) (mk 1 : PowerSeries ℂ) =
      (1 + C Complex.I * X)⁻¹ :=
    (PowerSeries.eq_inv_iff_mul_eq_one (by simp)).2 h
  simpa [kernel, ← he] using coeff_rescale (mk 1 : PowerSeries ℂ) (-Complex.I) k

private theorem kernel_coefficient (m k : ℕ) :
    coeff k (kernel m) = Complex.I^m * (-Complex.I)^k * (weight m k : ℂ) := by
  induction m generalizing k with
  | zero => simp [kernel_zero_coeff]
  | succ m ihm =>
    induction k with
    | zero => simp [coeff_zero_eq_constantCoeff]
    | succ k ihk =>
      have hc := congrArg (coeff (k+1)) (kernel_step m)
      simp only [add_mul, one_mul, mul_assoc, map_add, coeff_C_mul,
        coeff_succ_X_mul] at hc
      rw [ihk, ihm (k+1), ihm k] at hc
      have hphase : Complex.I^(m+1)*(-Complex.I)^(k+1) = Complex.I^m*(-Complex.I)^k := by
        rw [pow_succ, pow_succ]
        calc
          _ = (Complex.I * (-Complex.I)) * (Complex.I^m * (-Complex.I)^k) := by ring
          _ = _ := by simp
      have hl : Complex.I * (Complex.I^(m+1)*(-Complex.I)^k*(weight (m+1) k : ℂ)) =
          -(Complex.I^m*(-Complex.I)^k*(weight (m+1) k : ℂ)) := by
        rw [pow_succ]
        calc
          _ = (Complex.I * Complex.I) * (Complex.I^m*(-Complex.I)^k*(weight (m+1) k : ℂ)) := by ring
          _ = _ := by rw [Complex.I_mul_I]; ring
      have hr : Complex.I * (Complex.I^m*(-Complex.I)^(k+1)*(weight m (k+1) : ℂ)) =
          Complex.I^m*(-Complex.I)^k*(weight m (k+1) : ℂ) := by
        rw [pow_succ]
        calc
          _ = (Complex.I * (-Complex.I)) * (Complex.I^m*(-Complex.I)^k*(weight m (k+1) : ℂ)) := by ring
          _ = _ := by simp
      rw [hl, hr] at hc
      rw [weight, Int.cast_add, Int.cast_add, hphase]
      linear_combination hc

end D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
namespace D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
open PowerSeries
open scoped BigOperators


private theorem phase_diagonal (m : ℕ) : (Complex.I^m * (-Complex.I)^m) = 1 := by
  rw [← mul_pow]
  simp

private theorem phase_pair (m k : ℕ) : ∃ z : ℤ, (Complex.I^m * (-Complex.I)^k) + (Complex.I^k * (-Complex.I)^m) = (2*z : ℤ) := by
  have hn : (-Complex.I)^4 = 1 := by norm_num [neg_pow, Complex.I_pow_four]
  simp only [Complex.I_pow_eq_pow_mod m, Complex.I_pow_eq_pow_mod k,
    pow_eq_pow_mod k hn, pow_eq_pow_mod m hn]
  have hm := Nat.mod_lt m (by decide : 0 < 4)
  have hk := Nat.mod_lt k (by decide : 0 < 4)
  interval_cases h : m%4 <;> interval_cases h' : k%4 <;>
    first
    | (refine ⟨0, ?_⟩; norm_num [neg_pow, Complex.I_sq, Complex.I_pow_three]; done)
    | (refine ⟨1, ?_⟩; norm_num [neg_pow, Complex.I_sq, Complex.I_pow_three]; done)
    | (refine ⟨-1, ?_⟩; norm_num [neg_pow, Complex.I_sq, Complex.I_pow_three]; done)

private theorem kernel_pair (m k : ℕ) : ∃ z : ℤ,
    coeff k (kernel m) + coeff m (kernel k) = (2*z : ℤ) := by
  obtain ⟨z,hz⟩ := phase_pair m k
  refine ⟨z * weight m k, ?_⟩
  rw [kernel_coefficient, kernel_coefficient, weight_symmetric k m]
  change (Complex.I^m * (-Complex.I)^k) * (weight m k : ℂ) + (Complex.I^k * (-Complex.I)^m) * (weight m k : ℂ) = _
  rw [← add_mul, hz]
  push_cast
  ring

private theorem matrix_integral (s : Finset ℕ) (f : ℕ → ℕ → ℂ) (d : ℕ → ℤ)
    (hd : ∀ a ∈ s, f a a = (d a : ℂ))
    (hp : ∀ a ∈ s, ∀ b ∈ s, ∃ z : ℤ, f a b + f b a = (2*z : ℤ)) :
    ∃ z : ℤ, (∑ a ∈ s, ∑ b ∈ s, f a b) = (z : ℂ) ∧
      Even (z - ∑ a ∈ s, d a) := by
  classical
  revert hd hp
  induction s using Finset.induction_on with
  | empty => intro hd hp; exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    intro hd hp
    obtain ⟨z,hz,he⟩ := ih
      (fun b hb => hd b (Finset.mem_insert_of_mem hb))
      (fun b hb c hc => hp b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
    have hq : ∀ b ∈ s, ∃ z : ℤ, f a b + f b a = (2*z : ℤ) := by
      intro b hb
      exact hp a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb)
    let q (b : ℕ) : ℤ := if hb : b ∈ s then Classical.choose (hq b hb) else 0
    have hqb (b : ℕ) (hb : b ∈ s) : f a b + f b a = (2*q b : ℤ) := by
      simpa [q, hb] using Classical.choose_spec (hq b hb)
    let Q : ℤ := ∑ b ∈ s, q b
    have hQ : ∑ b ∈ s, (f a b + f b a) = (2 * Q : ℤ) := by
      simp only [Q, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b hb => by simpa only [Int.cast_mul, Int.cast_ofNat] using hqb b hb
    refine ⟨d a + 2*Q+z, ?_, ?_⟩
    · simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
      rw [hd a (Finset.mem_insert_self a s), hz]
      have := hQ
      simp only [Finset.sum_add_distrib] at this
      push_cast at this ⊢
      linear_combination this
    · rw [Finset.sum_insert ha]
      obtain ⟨t,ht⟩ := he
      exact ⟨Q+t, by omega⟩

end D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
namespace D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
open PowerSeries
open scoped BigOperators

theorem kernel_expansion (m p : ℕ) (hp : p ≠ 0) :
    expand p hp (kernel m) =
      (X^p + C Complex.I)^m * ((1 + C Complex.I * X^p)^(m+1))⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp [hp])).2
  have h : kernel m * ((1 + C Complex.I * X)^(m+1)) = (X + C Complex.I)^m := by
    unfold kernel
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  have he := congrArg (expand p hp) h
  simpa only [map_mul, map_pow, map_add, map_one, expand_X, expand_C] using he

theorem expansion_coefficient (p N : ℕ) (hp : p ≠ 0) (f : PowerSeries ℂ)
    (s : Finset ℕ) (hs : ∀ k, p*k=N → k∈s) :
    coeff N (expand p hp f) = ∑ k ∈ s, if p*k=N then coeff k f else 0 := by
  classical
  rw [coeff_expand]
  split_ifs with h
  · obtain ⟨k,hk⟩ := h
    have hm : k ∈ s := hs k hk.symm
    rw [hk, Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hp)]
    symm
    rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      rw [ite_eq_right]
      intro he
      exact hbk (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp) he)
    · intro hk'
      exact (hk' hm).elim
  · symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [ite_eq_right]
    intro he
    exact h ⟨k,he.symm⟩

theorem shifted_expansion_coefficient (d p N : ℕ) (hp : p ≠ 0)
    (hd : d ≤ N) (f : PowerSeries ℂ) (s : Finset ℕ)
    (hs : ∀ k, d+p*k=N → k∈s) :
    coeff N (X^d * expand p hp f) =
      ∑ k ∈ s, if d+p*k=N then coeff k f else 0 := by
  classical
  rw [coeff_X_pow_mul', ite_eq_left hd]
  rw [expansion_coefficient p (N-d) hp f s (by
    intro k hk
    apply hs k
    omega)]
  apply Finset.sum_congr rfl
  intro k hk
  have he : p*k=N-d ↔ d+p*k=N := by omega
  simp only [he]

theorem supported_matrix_integral (s : Finset ℕ) (P : ℕ → ℕ → Prop)
    [DecidableRel P] (hP : ∀ m k, P m k ↔ P k m) :
    ∃ z : ℤ,
      (∑ m ∈ s, ∑ k ∈ s, if P m k then coeff k (kernel m) else 0) = (z : ℂ) ∧
      Even (z - ∑ m ∈ s, if P m m then weight m m else 0) := by
  apply matrix_integral
  · intro m hm
    by_cases h : P m m
    · simp only [ite_eq_left h, kernel_coefficient]
      change (Complex.I^m * (-Complex.I)^m) * (weight m m : ℂ) = _
      rw [phase_diagonal, one_mul]
    · simp [h]
  · intro m hm k hk
    by_cases h : P m k
    · have h' := (hP m k).mp h
      simpa only [ite_eq_left h, ite_eq_left h'] using kernel_pair m k
    · have h' : ¬ P k m := fun hk => h ((hP m k).mpr hk)
      exact ⟨0, by simp [h,h']⟩

end D5.S1.Recurrence.Algebraic.HannaGaussianKernelParity
