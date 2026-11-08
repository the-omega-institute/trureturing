/- GID: D5/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod
   generality: I
   mirror-B: D5/B/S1/Recurrence/Periodic/ProvvediEvenFubiniLeastPrimePeriod
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive even-index Fubini numbers have the conjectured least period at every prime. -/

/-
For result:
proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#21866; Proved)
Direct frozen dependencies:
F0 = D5/S1/Recurrence/Periodic/SomerUniformSubsequenceRefutation.IsLeastPositivePeriodMod sha256:1ec2ffa0f4224d7f3c6c7df214bf5cae2fb21a718f35db90c997adf1bfe336b0
F1 = D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T_exponential_sum sha256:c748ff13d1112fddb7bb1d90ec975055f1e43b29ec4389cf51fbcb5f70b37ff3
F2 = D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T sha256:3fe8626b9a43fa9801a5c43fe562f2e0feacb5ccaa0ac1c9ca2238f00adeb453
F3 = D5/S1/Recurrence/Periodic/StirlingTransformTotientPeriod.T_window sha256:59f57bee9849051bd4a74547a09a93c572070cf5795411d62bb83760e7c757a6

Private helpers: name | proof_shape | direct frozen dependencies | consumers.
Each has escape_witness: none; dependencies expand same-module helpers.
choose_complement | bind-only | none | exponential_coefficient
exponential_coefficient | bind-only | none | fubini_exponential
fubini_exponential | bind-only | F1,F2 | paired_expansion
half_prime | bind-only | none | square_frequencies_card,paired_expansion,surviving_support,result
square_frequencies_injective | bind-only | none | square_frequencies_card,result
square_frequencies_card | bind-only | none | result
fiber_three_bound | bind-only | none | surviving_support
spectral_period_lower_bound | bind-only | none | result
weight_zero_iff | bind-only | none | surviving_support
paired_expansion | bind-only | F1,F2 | at_three,result
four_first_three_injective | bind-only | none | surviving_support
surviving_support | bind-only | none | result
at_two | bind-only | F2,F3 | result
at_three | bind-only | F1,F2 | result
square_count_two | bind-only | none | result

Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22423
Every private theorem is a consumed bind-only helper; none is an escape witness.
The sequence is the existing transform T at weight one and argument 2*n;
claim inlines this expression and adds no forwarding sequence definition.
The prime clause concerns positive indices; composite moduli, eventual periods
and the divisibility-by-288 conjecture are outside the statement.
-/

import D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Vandermonde
import D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation

open Finset

namespace D5.S1.Recurrence.Periodic.ProvvediEvenFubiniLeastPrimePeriod

/-- Provvedi's prime-modulus assertion in OEIS A249938, at positive indices. -/
def claim : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    D5.S1.Recurrence.Periodic.SomerUniformSubsequenceRefutation.IsLeastPositivePeriodMod
      p (fun n : ℕ =>
        D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod.T
          (fun _ : ℕ => 1) (2 * (n + 1)))
      (Nat.card {x : ZMod p // x ≠ 0 ∧ IsSquare x})

private theorem choose_complement (p j r : ℕ) [Fact p.Prime] (h : j + r < p) :
    (Nat.choose (p - 1 - j) r : ZMod p) =
      (-1 : ZMod p) ^ r * (Nat.choose (j + r) r : ZMod p) := by
  have hr : r < p := Nat.lt_of_add_left_lt h
  have hf : (r.factorial : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdiv
    exact (not_le_of_gt hr) ((Fact.out : p.Prime).dvd_factorial.mp hdiv)
  apply mul_left_cancel₀ hf
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose]
  have he : ((p - 1 - j).descFactorial r : ZMod p) =
      (-1 : ZMod p) ^ r * ((j + 1).ascFactorial r : ZMod p) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.ascFactorial_eq_prod_range]
    simp only [Nat.cast_prod]
    have hconst : (-1 : ZMod p)^r = ∏ _i ∈ range r, (-1 : ZMod p) :=
      pow_eq_prod_const (-1) r
    rw [hconst, ← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    have hi' : i < r := mem_range.mp hi
    have hb : j + 1 + i ≤ p := by omega
    have heq : p - 1 - j - i + (j + 1 + i) = p := by omega
    have hc := congrArg (fun n : ℕ => (n : ZMod p)) heq
    simp only [Nat.cast_add, ZMod.natCast_self] at hc
    push_cast
    linear_combination hc
  rw [he, Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  ring


open D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod

private theorem exponential_coefficient (p j : ℕ) [Fact p.Prime] (hj : j < p) :
    (∑ k ∈ range p, (-1 : ZMod p) ^ (k-j) * (Nat.choose k j : ZMod p)) =
      (2 : ZMod p) ^ (p - 1 - j) := by
  have hlow : (∑ k ∈ range j, (-1 : ZMod p) ^ (k-j) * (Nat.choose k j : ZMod p)) = 0 := by
    apply sum_eq_zero
    intro k hk
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hk)]
  rw [← sum_range_add_sum_Ico _ hj.le, hlow, zero_add, sum_Ico_eq_sum_range]
  have he : p-j = (p-1-j)+1 := by omega
  rw [he]
  calc
    _ = ∑ r ∈ range (p-1-j+1), (Nat.choose (p-1-j) r : ZMod p) := by
      apply sum_congr rfl
      intro r hr
      rw [show j+r-j = r by omega, Nat.choose_symm_add]
      simpa only [Nat.add_comm] using (choose_complement p j r (by
        have := mem_range.mp hr
        omega)).symm
    _ = (2 : ZMod p) ^ (p-1-j) := by
      have h := add_pow (1 : ZMod p) 1 (p-1-j)
      norm_num at h ⊢
      exact h.symm

private theorem fubini_exponential (p N : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (T (fun _ => 1) N : ZMod p) =
      ∑ j ∈ range p, ((2 : ZMod p)⁻¹)^j * (j : ZMod p)^N := by
  have hprime : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 :=
    (mt (ZMod.natCast_eq_zero_iff 2 p).mp
      (Nat.not_dvd_of_pos_of_lt (by decide) (by have := hprime.two_le; omega)))
  rw [T_exponential_sum _ p N hprime.pos]
  simp only [Int.cast_one, one_mul]
  have hexpand : (∑ k ∈ range p, ∑ j ∈ range (k+1),
      (-1 : ZMod p) ^ (k-j) * (Nat.choose k j : ZMod p) * (j : ZMod p)^N) =
      ∑ k ∈ range p, ∑ j ∈ range p,
      (-1 : ZMod p) ^ (k-j) * (Nat.choose k j : ZMod p) * (j : ZMod p)^N := by
    apply sum_congr rfl
    intro k hk
    apply sum_subset (range_mono (by have := mem_range.mp hk; omega))
    intro j hj hj'
    have hkj : k < j := by simp only [mem_range, not_lt] at hj'; omega
    simp [Nat.choose_eq_zero_of_lt hkj]
  rw [hexpand, sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← sum_mul, exponential_coefficient p j (mem_range.mp hj)]
  congr 1
  apply (mul_left_inj' (pow_ne_zero j h2)).mp
  rw [← pow_add, show p-1-j+j=p-1 by have := mem_range.mp hj; omega,
    ZMod.pow_card_sub_one_eq_one h2]
  simp [h2]



open Finset

private theorem half_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2 * ((p-1)/2) = p-1 := by
  exact Nat.two_mul_div_two_of_even ((Fact.out : p.Prime).even_sub_one hp)

private theorem square_frequencies_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (fun i : Fin ((p-1)/2) => ((i.val+1 : ℕ) : ZMod p)^2) := by
  intro i j he
  have hip : i.val+1 < p := by have := i.isLt; omega
  have hjp : j.val+1 < p := by have := j.isLt; omega
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
  · have hv := congrArg ZMod.val h
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp] at hv
    apply Fin.ext
    omega
  · have hz : (((i.val+1)+(j.val+1) : ℕ) : ZMod p) = 0 := by
      push_cast at h ⊢
      rw [h]
      ring
    have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hb : (i.val+1)+(j.val+1) < p := by
      have := i.isLt
      have := j.isLt
      omega
    exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) hb hdiv)

private theorem square_frequencies_card (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card {x : ZMod p // x ≠ 0 ∧ IsSquare x} = (p-1)/2 := by
  let m := (p-1)/2
  let f : Fin m → {x : ZMod p // x ≠ 0 ∧ IsSquare x} := fun i =>
    ⟨((i.val+1 : ℕ) : ZMod p)^2, pow_ne_zero _ ((mt (ZMod.natCast_eq_zero_iff _ p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by have := i.isLt; dsimp [m] at *; omega)))), ⟨(i.val+1 : ℕ), by simp [pow_two]⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j he
      exact square_frequencies_injective p (congrArg Subtype.val he)
    · intro x
      obtain ⟨y, hy⟩ := x.2.2
      have hy0 : y ≠ 0 := by intro h; simp [h] at hy; exact x.2.1 hy
      have hyval : 0 < y.val := ZMod.val_pos.mpr hy0
      have hyp : y.val < p := ZMod.val_lt y
      have hpodd := half_prime p hp
      by_cases hsmall : y.val ≤ m
      · refine ⟨⟨y.val-1, by omega⟩, ?_⟩
        apply Subtype.ext
        change (((y.val-1+1 : ℕ) : ZMod p)^2) = x.val
        rw [Nat.sub_add_cancel hyval, ZMod.natCast_zmod_val]
        exact (by simpa [pow_two] using hy.symm)
      · refine ⟨⟨p-y.val-1, by dsimp [m] at *; omega⟩, ?_⟩
        apply Subtype.ext
        change (((p-y.val-1+1 : ℕ) : ZMod p)^2) = x.val
        have hpy : 0 < p-y.val := Nat.zero_lt_sub_of_lt hyp
        rw [Nat.sub_add_cancel hpy, Nat.cast_sub hyp.le, ZMod.natCast_self,
          ZMod.natCast_zmod_val, zero_sub, neg_sq]
        exact (by simpa [pow_two] using hy.symm)
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (Nat.card_fin m)



open Finset

private theorem fiber_three_bound {K : Type*} [Field K] [DecidableEq K] (m : ℕ) (hm : 0 < m)
    (b c : K) (hc : c ≠ 0) (hperiod : b ^ m = 1)
    (hinj : Function.Injective (fun i : Fin 3 => b ^ (i : ℕ))) :
    3 * (univ.filter (fun i : Fin m => b ^ ((i : ℕ) + 1) = c)).card ≤ m := by
  classical
  let Z := {i : Fin m // b ^ ((i : ℕ) + 1) = c}
  let f : Z × Fin 3 → Fin m := fun z => ⟨(z.1.1.val + z.2.val) % m, Nat.mod_lt _ hm⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h := congrArg (fun i : Fin m => b ^ ((i : ℕ) + 1)) hxy
    change b ^ ((x.1.1.val + x.2.val) % m + 1) =
      b ^ ((y.1.1.val + y.2.val) % m + 1) at h
    simp only [pow_succ, ← pow_eq_pow_mod _ hperiod, pow_add] at h
    have h' : c * b ^ x.2.val = c * b ^ y.2.val := by
      have hx := x.1.2
      have hy := y.1.2
      simp only [pow_succ] at hx hy
      linear_combination h - b ^ x.2.val * hx + b ^ y.2.val * hy
    have hij : x.2 = y.2 := hinj (mul_left_cancel₀ hc h')
    apply Prod.ext
    · apply Subtype.ext
      apply Fin.ext
      have he := congrArg Fin.val hxy
      change (x.1.1.val + x.2.val) % m = (y.1.1.val + y.2.val) % m at he
      rw [hij] at he
      exact (Nat.ModEq.add_right_cancel' y.2.val he).eq_of_lt_of_lt
        x.1.1.isLt y.1.1.isLt
    · exact hij
  have hcard := Fintype.card_le_of_injective f hf
  have hZ : Fintype.card Z = (univ.filter (fun i : Fin m => b ^ ((i : ℕ) + 1) = c)).card :=
    Fintype.card_of_subtype _ (by intro i; simp)
  simpa [Fintype.card_prod, hZ, Nat.mul_comm] using hcard



open Finset

private theorem spectral_period_lower_bound {K : Type*} [Field K] [DecidableEq K]
    {m : ℕ} (hm : 0 < m) (lam w : Fin m → K)
    (hinj : Function.Injective lam) (hne : ∀ i, lam i ≠ 0)
    (hpow : ∀ i, lam i ^ m = 1)
    (hsupport : m < 2 * (univ.filter (fun i => w i ≠ 0)).card)
    (t : ℕ) (ht : 0 < t)
    (hperiod : ∀ n : ℕ,
      (∑ i, w i * lam i ^ (n + t + 1)) = ∑ i, w i * lam i ^ (n + 1)) :
    m ≤ t := by
  classical
  have hv : (fun i => w i * (lam i ^ t - 1) * lam i) = (0 : Fin m → K) := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro n
    have h := sub_eq_zero.mpr (hperiod n)
    rw [← sum_sub_distrib] at h
    convert h using 1
    apply sum_congr rfl
    intro i hi
    simp only [pow_add, pow_one]
    ring
  have hroot (i : Fin m) (hi : w i ≠ 0) : lam i ^ t = 1 := by
    have h := congrFun hv i
    simp only [Pi.zero_apply, mul_eq_zero, hne i, or_false, hi, false_or] at h
    exact sub_eq_zero.mp h
  let d := Nat.gcd m t
  have hd : 0 < d := Nat.gcd_pos_of_pos_left t hm
  have hdm : d ∣ m := Nat.gcd_dvd_left m t
  have hdt : d ≤ t := Nat.gcd_le_right m ht
  have hbound : (univ.filter (fun i => w i ≠ 0)).card ≤ d := by
    let s := (univ.filter (fun i => w i ≠ 0)).image lam
    have hs : s.val ⊆ (Polynomial.X ^ d - Polynomial.C (1 : K)).roots := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (show x ∈ s from hx)
      have ht' := hroot i (mem_filter.mp hi).2
      have hd' : lam i ^ d = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd
          (orderOf_dvd_of_pow_eq_one (hpow i)) (orderOf_dvd_of_pow_eq_one ht'))
      apply (Polynomial.mem_roots (Polynomial.X_pow_sub_C_ne_zero hd 1)).mpr
      simp [Polynomial.IsRoot, hd']
    have h := Polynomial.card_le_degree_of_subset_roots hs
    have hcard : s.card = (univ.filter (fun i => w i ≠ 0)).card :=
      card_image_of_injective _ hinj
    rw [hcard] at h
    rw [Polynomial.natDegree_X_pow_sub_C] at h
    exact h
  have hhalf : m < 2 * d := lt_of_lt_of_le hsupport (Nat.mul_le_mul_left 2 hbound)
  have hmd : m = d := by
    obtain ⟨k, hk⟩ := hdm
    have hk0 : k ≠ 0 := by intro h; simp [h] at hk; omega
    have hk1 : k = 1 := by
      by_contra hk1
      have hk2 : 2 ≤ k := by omega
      have hmul := Nat.mul_le_mul_left d hk2
      nlinarith
    simpa [hk1] using hk
  exact hmd.le.trans hdt



open Finset

private theorem weight_zero_iff {K : Type*} [Field K] (b : K) (hb : b ≠ 0) (r : ℕ) :
    b⁻¹ ^ (r+1) + b ^ r = 0 ↔ (b^2) ^ (r+1) = -b := by
  have hinv : b⁻¹ ^ (r+1) * b ^ (r+2) = b := by
    calc
      _ = b⁻¹ ^ (r+1) * (b ^ (r+1) * b) := by
        exact congrArg (fun x : K => b⁻¹ ^ (r+1) * x) (pow_succ b (r+1))
      _ = b := by
        rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hb, one_pow, one_mul]
  have hpwr : b ^ r * b ^ (r+2) = (b^2) ^ (r+1) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  have he : (b⁻¹ ^ (r+1) + b ^ r) * b ^ (r+2) = b + (b^2) ^ (r+1) := by
    rw [add_mul, hinv, hpwr]
  constructor
  · intro h
    rw [h, zero_mul] at he
    linear_combination -he
  · intro h
    rw [h, add_neg_cancel] at he
    exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ hb)


open D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod

private theorem paired_expansion (p n : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hn : 0 < n) :
    (T (fun _ => 1) (2*n) : ZMod p) =
      ∑ i : Fin ((p-1)/2),
        (((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val) *
          (((i.val+1 : ℕ) : ZMod p)^2)^n := by
  have hp2 : 2 < p := by have := (Fact.out : p.Prime).two_le; omega
  have h2 : (2 : ZMod p) ≠ 0 := (mt (ZMod.natCast_eq_zero_iff 2 p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) hp2))
  let m := (p-1)/2
  have hm : 2*m = p-1 := half_prime p hp
  have hpm : p = m+m+1 := by omega
  rw [fubini_exponential p (2*n) hp]
  rw [show range p = range (m+m+1) from congrArg range hpm, sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (by omega : 2*n ≠ 0), mul_zero, add_zero]
  rw [sum_range_add]
  rw [← sum_range_reflect (fun i => ((2 : ZMod p)⁻¹)^(m+i+1) *
      ((m+i+1 : ℕ) : ZMod p)^(2*n)) m]
  rw [← sum_add_distrib, ← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro k hk
  let i : ℕ := k.val
  have hi' : i < m := k.isLt
  change (2⁻¹ ^ (i+1) * ((i+1 : ℕ) : ZMod p)^(2*n) +
    2⁻¹ ^ (m+(m-1-i)+1) * ((m+(m-1-i)+1 : ℕ) : ZMod p)^(2*n)) =
    (2⁻¹ ^ (i+1) + 2^i) * (((i+1 : ℕ) : ZMod p)^2)^n
  have hexp : m+(m-1-i)+1 = p-(i+1) := by omega
  have hc : ((p-(i+1) : ℕ) : ZMod p) = -((i+1 : ℕ) : ZMod p) := by
    rw [Nat.cast_sub (by omega : i+1 ≤ p), ZMod.natCast_self, zero_sub]
  have hcoeff : ((2 : ZMod p)⁻¹)^(p-(i+1)) = (2 : ZMod p)^i := by
    apply (mul_left_inj' (pow_ne_zero i (inv_ne_zero h2))).mp
    rw [← pow_add, show p-(i+1)+i=p-1 by omega]
    rw [ZMod.pow_card_sub_one_eq_one (inv_ne_zero h2)]
    simp [h2]
  rw [hexp, hc, hcoeff]
  rw [show (2*n) = 2*n by rfl, pow_mul, pow_mul, neg_sq]
  ring



open Finset

private theorem four_first_three_injective (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    Function.Injective (fun i : Fin 3 => (4 : ZMod p)^i.val) := by
  have h2 : (2 : ZMod p) ≠ 0 := (mt (ZMod.natCast_eq_zero_iff 2 p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
  have h3 : (3 : ZMod p) ≠ 0 := (mt (ZMod.natCast_eq_zero_iff 3 p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
  have h5 : (5 : ZMod p) ≠ 0 := (mt (ZMod.natCast_eq_zero_iff 5 p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first | rfl |
      (exfalso; apply h3; norm_num at h ⊢; (first | linear_combination h | linear_combination -h)) |
      (exfalso; apply mul_ne_zero h3 h5; norm_num at h ⊢; (first | linear_combination h | linear_combination -h)) |
      (exfalso; apply mul_ne_zero (mul_ne_zero h3 h2) h2;
        norm_num at h ⊢; (first | linear_combination h | linear_combination -h))

private theorem surviving_support (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (p-1)/2 < 2 * (univ.filter (fun i : Fin ((p-1)/2) =>
      ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val ≠ 0)).card := by
  classical
  by_cases hp5 : p = 5
  · subst p
    have hi2 : (2 : ZMod 5)⁻¹ = 3 :=
      ZMod.inv_eq_of_mul_eq_one 5 2 3 (by decide +revert)
    have he : (univ.filter (fun i : Fin ((5-1)/2) =>
      ((2 : ZMod 5)⁻¹)^(i.val+1) + (2 : ZMod 5)^i.val ≠ 0)) = univ := by
      ext i
      simp only [mem_filter, mem_univ, true_and, iff_true]
      rw [hi2]
      fin_cases i
      · change (3 : ZMod 5) + 1 ≠ 0
        clear hi2
        decide +revert
      · change (3 : ZMod 5)^2 + 2 ≠ 0
        clear hi2
        decide +revert
    rw [he]
    norm_num
  · have hprime : p.Prime := Fact.out
    have hp7 : 7 ≤ p := by
      have hodd := hprime.eq_two_or_odd
      rcases hodd with h | h <;> omega
    let m := (p-1)/2
    have hm : 0 < m := by dsimp [m]; omega
    have h2 : (2 : ZMod p) ≠ 0 := (mt (ZMod.natCast_eq_zero_iff 2 p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)))
    have hfour : (4 : ZMod p) = (2 : ZMod p)^2 := by ring
    have hperiod : (4 : ZMod p)^m = 1 := by
      rw [hfour]
      rw [← pow_mul, half_prime p (by omega), ZMod.pow_card_sub_one_eq_one h2]
    have hbound := fiber_three_bound m hm (4 : ZMod p) (-2 : ZMod p)
      (neg_ne_zero.mpr h2) hperiod (four_first_three_injective p hp7)
    have hzero (i : Fin m) :
        ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val = 0 ↔
        (4 : ZMod p)^(i.val+1) = -2 := by
      rw [hfour]
      exact weight_zero_iff (2 : ZMod p) h2 i.val
    have he : (univ.filter (fun i : Fin m =>
        ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val = 0)) =
        univ.filter (fun i : Fin m => (4 : ZMod p)^(i.val+1) = -2) := by
      exact filter_inj'.mpr fun ⦃a⦄ _ => hzero a
    let Z := univ.filter (fun i : Fin m =>
      ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val = 0)
    let S := univ.filter (fun i : Fin m =>
      ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val ≠ 0)
    have hsplit : Z.card + S.card = m := by
      simpa only [Z, S, ne_eq, card_univ, Fintype.card_fin] using
        (card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
          (fun i : Fin m => ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val = 0))
    have hZ : 3 * Z.card ≤ m :=
      le_of_eq_of_le (congrArg (HMul.hMul 3) (congrArg card he)) hbound
    change m < 2 * S.card
    omega



open Finset
open D5.S1.Recurrence.Periodic.StirlingTransformTotientPeriod

private theorem at_two (n : ℕ) : ((T (fun _ : ℕ => 1) (2 * (n+1))) : ZMod 2) = 1 := by
  rw [T_window _ 2 _ (by decide)]
  have he : 2*(n+1) = (2*n+1)+1 := (Nat.succ_add (2*n) 1).symm
  simp [Finset.sum_range_succ, he, Nat.stirlingSecond_one_right]

private theorem at_three (n : ℕ) : ((T (fun _ : ℕ => 1) (2 * (n+1))) : ZMod 3) = 0 := by
  rw [paired_expansion 3 (n+1) (by decide) (by omega)]
  have hi2 : (2 : ZMod 3)⁻¹ = 2 :=
    ZMod.inv_eq_of_mul_eq_one 3 2 2 (by decide)
  norm_num [Fin.sum_univ_one, hi2]
  decide

private theorem square_count_two : Nat.card {x : ZMod 2 // x ≠ 0 ∧ IsSquare x} = 1 := by
  have he : {x : ZMod 2 | x ≠ 0 ∧ IsSquare x} = {1} := by
    exact (Set.toFinset_inj (s := {x : ZMod 2 | x ≠ 0 ∧ IsSquare x})
      (t := ({1} : Set (ZMod 2)))).mp rfl
  change Nat.card {x // x ∈ {x : ZMod 2 | x ≠ 0 ∧ IsSquare x}} = 1
  rw [he]
  simp

theorem result : claim := by
  intro p hprime
  haveI : Fact p.Prime := ⟨hprime⟩
  by_cases hp2 : p = 2
  · subst p
    rw [square_count_two]
    refine ⟨by decide, ?_, ?_⟩
    · intro n
      change ((T (fun _ : ℕ => 1) (2 * (n+1+1))) : ZMod 2) = (T (fun _ : ℕ => 1) (2 * (n+1)))
      rw [at_two, at_two]
    · intro t ht hp
      exact ht
  by_cases hp3 : p = 3
  · subst p
    rw [square_frequencies_card 3 (by decide)]
    change 0 < 1 ∧ _ ∧ _
    refine ⟨by decide, ?_, ?_⟩
    · intro n
      change ((T (fun _ : ℕ => 1) (2 * (n+1+1))) : ZMod 3) = (T (fun _ : ℕ => 1) (2 * (n+1)))
      rw [at_three, at_three]
    · intro t ht hp
      exact ht
  have hp5 : 5 ≤ p := hprime.five_le_of_ne_two_of_ne_three hp2 hp3
  rw [square_frequencies_card p hp2]
  let m := (p-1)/2
  let lam : Fin m → ZMod p := fun i => ((i.val+1 : ℕ) : ZMod p)^2
  let w : Fin m → ZMod p := fun i => ((2 : ZMod p)⁻¹)^(i.val+1) + (2 : ZMod p)^i.val
  have hm : 0 < m := by dsimp [m]; omega
  have hne (i : Fin m) : lam i ≠ 0 := by
    apply pow_ne_zero
    exact (mt (ZMod.natCast_eq_zero_iff _ p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by have := i.isLt; dsimp [m] at *; omega)))
  have hpow (i : Fin m) : lam i ^ m = 1 := by
    dsimp [lam]
    rw [← pow_mul, half_prime p hp2]
    exact ZMod.pow_card_sub_one_eq_one
      ((mt (ZMod.natCast_eq_zero_iff _ p).mp
      (Nat.not_dvd_of_pos_of_lt (by omega) (by have := i.isLt; dsimp [m] at *; omega))))
  have hexp (n : ℕ) : ((T (fun _ : ℕ => 1) (2 * (n+1))) : ZMod p) = ∑ i, w i * lam i ^ (n+1) := by
    exact paired_expansion p (n+1) hp2 (by omega)
  refine ⟨hm, ?_, ?_⟩
  · intro n
    change ((T (fun _ : ℕ => 1) (2 * (n+m+1))) : ZMod p) = (T (fun _ : ℕ => 1) (2 * (n+1)))
    rw [hexp, hexp]
    apply sum_congr rfl
    intro i hi
    rw [show n+m+1=(n+1)+m by omega, pow_add, hpow, mul_one]
  · intro t ht hperiod
    apply spectral_period_lower_bound hm lam w (square_frequencies_injective p) hne hpow
      (surviving_support p hp5) t ht
    intro n
    have h := hperiod n
    change ((T (fun _ : ℕ => 1) (2 * (n+t+1))) : ZMod p) = (T (fun _ : ℕ => 1) (2 * (n+1))) at h
    rw [hexp, hexp] at h
    exact h


end D5.S1.Recurrence.Periodic.ProvvediEvenFubiniLeastPrimePeriod
