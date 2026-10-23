/- GID: D5/S3/ArithUnits/JaffeSuccessorRatioRefutation
   generality: I
   mirror-B: D5/B/S3/ArithUnits/JaffeSuccessorRatioRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.fullClaim; result=D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.result; claim=D5/S3/ArithUnits/JaffeSuccessorRatioRefutation.fullClaim
   digest: Primitive nonnegative representations refute the unrestricted successor-ratio conjecture. -/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.EReal.Inv
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Tactic

/-! # Primitive representations and the unrestricted successor-ratio conjecture

The counting argument proves a finite tail before comparing greatest missing integers.
The source allows nonnegative integer coefficients and either ordering of its two inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithUnits.JaffeSuccessorRatioRefutation

open Finset
open scoped ArithmeticFunction.Moebius

/-- Primitive nonnegative coefficients, including both coordinate axes. -/
def Represented (a b n : ℤ) : Prop :=
  ∃ x y : ℤ, 0 ≤ x ∧ 0 ≤ y ∧ x.natAbs.Coprime y.natAbs ∧ a * x + b * y = n

/-- The entire integer complement of the represented set. -/
def missing (a b : ℤ) : Set ℤ := {n | ¬ Represented a b n}

/-- The greatest missing integer, or infinity if there is no greatest one. -/
noncomputable def sourceG (a b : ℤ) : EReal :=
  by
    classical
    exact if h : ∃ m, IsGreatest (missing a b) m then (((h.choose : ℤ) : ℝ) : EReal) else ⊤

/-- The integer successor defined by the source's coprimality condition. -/
noncomputable def successor (a b : ℤ) : ℤ :=
  sInf {c : ℤ | b < c ∧ a.natAbs.Coprime c.natAbs}

/-- The full source conjecture, with no ordering assumption on the two integers. -/
def fullClaim : Prop :=
  ∀ a b : ℤ, 3 ≤ a → 3 ≤ b → a.natAbs.Coprime b.natAbs →
    sourceG a (successor a b) / sourceG a b ≤ 5

private def solutions (A B n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun xy => A * xy.1 + B * xy.2 = n)

private def primitiveSolutions (A B n : ℕ) : Finset (ℕ × ℕ) :=
  (solutions A B n).filter (fun xy => xy.1.Coprime xy.2)

private theorem mem_solutions {A B n x y : ℕ} (hA : 0 < A) (hB : 0 < B) :
    (x, y) ∈ solutions A B n ↔ A * x + B * y = n := by
  simp only [solutions, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : x ≤ A * x := Nat.le_mul_of_pos_left x hA
    have hy : y ≤ B * y := Nat.le_mul_of_pos_left y hB
    omega

private theorem prime_power_estimate (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) :
    p ^ e * (e + 1) ^ 2 ≤
      (if p < 7 then 16 else 1) * (p ^ (e - 1) * (p - 1)) ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  clear he
  have pp : p = (p - 1) + 1 := by omega
  change p ^ (k + 1) * (k + 2) ^ 2 ≤
    (if p < 7 then 16 else 1) * (p ^ k * (p - 1)) ^ 2
  induction k with
  | zero =>
    by_cases hs : p < 7
    · simp only [ite_eq_left hs, pow_zero, one_mul]
      norm_num
      nlinarith
    · simp only [ite_eq_right hs, pow_zero, one_mul]
      norm_num
      have : 7 ≤ p := by omega
      nlinarith
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      by_cases hs : p < 7
      · simp only [ite_eq_left hs] at ih ⊢
        have h : 9 ≤ 16 * (p - 1) ^ 2 := by nlinarith
        simpa [mul_pow, mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left (p ^ 2) h
      · have hp7 : 7 ≤ p := by omega
        have h : 9 ≤ (p - 1) ^ 2 := by nlinarith
        simp only [ite_eq_right hs, one_mul]
        simpa [mul_pow, mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_le_mul_left (p ^ 2) h
    · have hs : (k + 3) ^ 2 ≤ p * (k + 2) ^ 2 := by
        have : 1 ≤ k := by omega
        have hh := Nat.mul_le_mul_right ((k + 2) ^ 2) hp
        nlinarith
      calc
        p ^ (k + 1 + 1) * (k + 1 + 2) ^ 2
            ≤ p ^ 2 * (p ^ (k + 1) * (k + 2) ^ 2) := by
              rw [pow_succ]
              nlinarith [Nat.mul_le_mul_left (p ^ (k + 1) * p) hs]
        _ ≤ p ^ 2 * ((if p < 7 then 16 else 1) * (p ^ k * (p - 1)) ^ 2) :=
          Nat.mul_le_mul_left _ ih
        _ = (if p < 7 then 16 else 1) * (p ^ (k + 1) * (p - 1)) ^ 2 := by
          rw [pow_succ]; ring

private theorem solutions_count_bounds {A B n : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A.Coprime B) :
    n / (A * B) ≤ (solutions A B n).card ∧
      (solutions A B n).card ≤ n / (A * B) + 1 := by
  obtain ⟨r, hr, hmod⟩ := Nat.exists_mul_mod_eq_of_coprime n hAB hB.ne'
  have hpos : 0 < A * B := Nat.mul_pos hA hB
  have residues : ∀ xy ∈ solutions A B n, xy.1 % B = r := by
    intro xy hxy
    have he := (mem_solutions hA hB).mp hxy
    have hm : Nat.ModEq B (A * xy.1) (A * r) := by
      change A * xy.1 % B = A * r % B
      have := congrArg (fun t => t % B) he
      simpa [Nat.add_mod, Nat.mul_mod] using this.trans hmod.symm
    have hh := Nat.ModEq.cancel_left_of_coprime hAB.symm hm
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using hh
  constructor
  · rw [← card_range (n / (A * B))]
    let f : ℕ → ℕ × ℕ := fun t =>
      (r + B * t, (n - A * (r + B * t)) / B)
    apply card_le_card_of_injOn f
    · intro t ht
      have ht' : t < n / (A * B) := mem_range.mp ht
      have hle : A * (r + B * t) ≤ n := by
        have hr' : r + 1 ≤ B := hr
        have hq := Nat.div_mul_le_self n (A * B)
        nlinarith
      have hd : B ∣ n - A * (r + B * t) := by
        apply (Nat.modEq_iff_dvd' hle).mp
        change A * (r + B * t) % B = n % B
        simpa [Nat.add_mod, Nat.mul_mod] using hmod
      apply (mem_solutions hA hB).mpr
      rw [Nat.mul_div_cancel' hd]
      omega
    · intro t ht u hu h
      have := congrArg Prod.fst h
      dsimp [f] at this
      nlinarith
  · rw [← card_range (n / (A * B) + 1)]
    apply card_le_card_of_injOn (fun xy : ℕ × ℕ => xy.1 / B)
    · intro xy hxy
      dsimp only
      have he := (mem_solutions hA hB).mp hxy
      apply mem_range.mpr
      have hle : xy.1 / B * (A * B) ≤ n := by
        have hh := Nat.div_mul_le_self xy.1 B
        nlinarith
      have := (Nat.le_div_iff_mul_le hpos).mpr hle
      omega
    · intro xy hxy zw hzw h
      dsimp only at h
      have hx := residues xy hxy
      have hz := residues zw hzw
      have hd := Nat.mod_add_div xy.1 B
      have hd' := Nat.mod_add_div zw.1 B
      have hf : xy.1 = zw.1 := by
        calc
          xy.1 = r + B * (xy.1 / B) := by omega
          _ = r + B * (zw.1 / B) := by rw [h]
          _ = zw.1 := by omega
      have he := (mem_solutions hA hB).mp hxy
      have he' := (mem_solutions hA hB).mp hzw
      have hs : xy.2 = zw.2 := by nlinarith
      exact Prod.ext hf hs

private theorem totient_divisor_estimate {n : ℕ} (hn : n ≠ 0) :
    n * n.divisors.card ^ 2 ≤ 16 ^ 7 * n.totient ^ 2 := by
  have hw : (∏ p ∈ n.primeFactors, (if p < 7 then 16 else 1)) ≤ 16 ^ 7 := by
    have hc : (n.primeFactors.filter (fun p => p < 7)).card ≤ 7 := by
      calc
        _ ≤ (range 7).card := card_le_card (by intro p hp; exact mem_range.mpr (mem_filter.mp hp).2)
        _ = 7 := card_range 7
    simpa [prod_ite] using Nat.pow_le_pow_right (by decide : 1 ≤ 16) hc
  have ht : n.totient = ∏ p ∈ n.primeFactors,
      p ^ (n.factorization p - 1) * (p - 1) := by
    rw [Nat.totient_eq_prod_factorization hn, Nat.prod_factorization_eq_prod_primeFactors]
  calc
    n * n.divisors.card ^ 2 =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p * (n.factorization p + 1) ^ 2 := by
          nth_rw 1 [Nat.prod_primeFactors_pow_factorization hn]
          rw [Nat.card_divisors hn, prod_mul_distrib, prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 7 then 16 else 1) * (p ^ (n.factorization p - 1) * (p - 1)) ^ 2 := by
          apply prod_le_prod
          intro p hp
          exact prime_power_estimate p (n.factorization p)
            (Nat.prime_of_mem_primeFactors hp).two_le
            (Finsupp.mem_support_iff.mp hp |> Nat.pos_of_ne_zero)
    _ = (∏ p ∈ n.primeFactors, (if p < 7 then 16 else 1)) * n.totient ^ 2 := by
          rw [prod_mul_distrib, prod_pow, ht]
    _ ≤ 16 ^ 7 * n.totient ^ 2 := Nat.mul_le_mul_right _ hw

private theorem gcd_fiber_count {A B n d : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hd : d ∈ n.divisors) :
    ((solutions A B n).filter (fun xy => xy.1.gcd xy.2 = d)).card =
      (primitiveSolutions A B (n / d)).card := by
  have hdvd := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  symm
  apply card_bij (fun xy _ => (d * xy.1, d * xy.2))
  · intro xy hxy
    obtain ⟨hxy, hcop⟩ := mem_filter.mp hxy
    have he := (mem_solutions hA hB).mp hxy
    apply mem_filter.mpr
    constructor
    · apply (mem_solutions hA hB).mpr
      calc
        A * (d * xy.1) + B * (d * xy.2) = d * (A * xy.1 + B * xy.2) := by ring
        _ = n := by rw [he, Nat.mul_div_cancel' hdvd]
    · rw [Nat.gcd_mul_left, show xy.1.gcd xy.2 = 1 from hcop, mul_one]
  · intro xy hxy zw hzw hh
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hdpos hx) (Nat.eq_of_mul_eq_mul_left hdpos hy)
  · intro xy hxy
    obtain ⟨hsol, hgcd⟩ := mem_filter.mp hxy
    obtain ⟨x, y, hcop, hx, hy⟩ := Nat.exists_coprime xy.1 xy.2
    rw [hgcd] at hx hy
    refine ⟨(x,y), ?_, ?_⟩
    · apply mem_filter.mpr
      refine ⟨(mem_solutions hA hB).mpr ?_, hcop⟩
      have he := (mem_solutions hA hB).mp hsol
      rw [hx, hy] at he
      have hmul : d * (A * x + B * y) = n := by nlinarith [he]
      exact Nat.eq_div_of_mul_eq_left hdpos.ne' (by simpa [mul_comm] using hmul)
    · exact Prod.ext (by dsimp; simpa [mul_comm] using hx.symm)
        (by dsimp; simpa [mul_comm] using hy.symm)

private theorem count_partition {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    ∀ n > 0, (∑ d ∈ n.divisors, ((primitiveSolutions A B d).card : ℝ)) =
      (solutions A B n).card := by
  intro n hn
  have hf : (solutions A B n).card =
      ∑ d ∈ n.divisors, ((solutions A B n).filter (fun xy => xy.1.gcd xy.2 = d)).card := by
    apply card_eq_sum_card_fiberwise
    intro xy hxy
    apply Nat.mem_divisors.mpr
    refine ⟨?_, hn.ne'⟩
    have he := (mem_solutions hA hB).mp hxy
    rw [← he]
    exact dvd_add (dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (Nat.gcd_dvd_right _ _) _)
  rw [hf]
  simp only [Nat.cast_sum]
  rw [← Nat.sum_div_divisors n (fun d => ((primitiveSolutions A B d).card : ℝ))]
  apply sum_congr rfl
  intro d hd
  rw [gcd_fiber_count hA hB hd]

private theorem ordinary_count_error {A B n : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A.Coprime B) :
    |(A * B : ℕ) * ((solutions A B n).card : ℝ) - n| ≤ (A * B : ℕ) := by
  obtain ⟨hlo, hhi⟩ := solutions_count_bounds (n := n) hA hB hAB
  have hp : 0 < A * B := Nat.mul_pos hA hB
  have hqlo := Nat.div_mul_le_self n (A * B)
  have hqhi : n < (n / (A * B) + 1) * (A * B) := by
    simpa [mul_comm] using Nat.lt_mul_div_succ n hp
  have h1 : (n / (A * B) : ℕ) ≤ ((solutions A B n).card : ℝ) := by exact_mod_cast hlo
  have h2 : ((solutions A B n).card : ℝ) ≤ (n / (A * B) : ℕ) + 1 := by exact_mod_cast hhi
  have h3 : (n / (A * B) : ℕ) * (A * B : ℕ) ≤ (n : ℝ) := by exact_mod_cast hqlo
  have h4 : (n : ℝ) < ((n / (A * B) : ℕ) + 1 : ℝ) * (A * B : ℕ) := by
    exact_mod_cast hqhi
  have h5 : (0 : ℝ) ≤ (A * B : ℕ) := by positivity
  rw [abs_le]
  constructor <;> nlinarith

private theorem primitive_count_lower {A B n : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A.Coprime B) (hn : 0 < n) :
    (n.totient : ℝ) ≤ (A * B : ℕ) * ((primitiveSolutions A B n).card : ℝ) +
      (A * B : ℕ) * n.divisors.card := by
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ)).mp (count_partition hA hB) n hn
  have htbase : ∀ (m : ℕ), 0 < m → (∑ d ∈ m.divisors, (d.totient : ℝ)) = (m : ℝ) := by
    intro m _hm
    exact_mod_cast Nat.sum_totient m
  have ht := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ)).mp htbase n hn
  rw [Nat.sum_divisorsAntidiagonal
    (fun d m => (μ d : ℝ) * ((solutions A B m).card : ℝ))] at hm
  rw [Nat.sum_divisorsAntidiagonal (fun d m => (μ d : ℝ) * (m : ℝ))] at ht
  have hid : (A * B : ℕ) * ((primitiveSolutions A B n).card : ℝ) - n.totient =
      ∑ d ∈ n.divisors, (μ d : ℝ) *
        ((A * B : ℕ) * ((solutions A B (n / d)).card : ℝ) - (n / d : ℕ)) := by
    rw [← hm, ← ht, mul_sum]
    simp_rw [mul_sub]
    rw [sum_sub_distrib]
    congr 1
    apply sum_congr rfl
    intro d hd
    ring
  have herr : |(A * B : ℕ) * ((primitiveSolutions A B n).card : ℝ) - n.totient| ≤
      (A * B : ℕ) * n.divisors.card := by
    rw [hid]
    calc
      _ ≤ ∑ d ∈ n.divisors, |(μ d : ℝ) *
          ((A * B : ℕ) * ((solutions A B (n / d)).card : ℝ) - (n / d : ℕ))| :=
            abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ n.divisors, ((A * B : ℕ) : ℝ) := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul]
        have hmu : |(μ d : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
        calc
          _ ≤ 1 * |(A * B : ℕ) * ((solutions A B (n / d)).card : ℝ) - (n / d : ℕ)| :=
            mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
          _ ≤ (A * B : ℕ) := by simpa using ordinary_count_error (n := n / d) hA hB hAB
      _ = (A * B : ℕ) * n.divisors.card := by simp [mul_comm]
  have hh := (abs_le.mp herr).1
  linarith

private theorem primitive_tail {A B n : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hAB : A.Coprime B)
    (hn : 16 ^ 7 * (A * B) ^ 2 < n) :
    ∃ x y : ℕ, x.Coprime y ∧ A * x + B * y = n := by
  have hnpos : 0 < n := by omega
  have hP : 0 < (primitiveSolutions A B n).card := by
    by_contra hzero
    have hz : (primitiveSolutions A B n).card = 0 := by omega
    have hlo := primitive_count_lower hA hB hAB hnpos
    rw [hz, Nat.cast_zero, mul_zero, zero_add] at hlo
    have hphi : n.totient ≤ A * B * n.divisors.card := by exact_mod_cast hlo
    have hs := totient_divisor_estimate hnpos.ne'
    have hprod : n * n.divisors.card ^ 2 ≤
        (16 ^ 7 * (A * B) ^ 2) * n.divisors.card ^ 2 := by
      calc
        _ ≤ 16 ^ 7 * n.totient ^ 2 := hs
        _ ≤ 16 ^ 7 * (A * B * n.divisors.card) ^ 2 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hphi 2)
        _ = _ := by ring
    have hcard : 0 < n.divisors.card := card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hnpos.ne'⟩
    have hle := Nat.le_of_mul_le_mul_right hprod (pow_pos hcard 2)
    omega
  obtain ⟨xy, hxy⟩ := card_pos.mp hP
  obtain ⟨hsol, hcop⟩ := mem_filter.mp hxy
  exact ⟨xy.1, xy.2, hcop, (mem_solutions hA hB).mp hsol⟩

private theorem represented_nat (a b n : ℤ) :
    Represented a b n ↔ ∃ x y : ℕ, x.Coprime y ∧ a * x + b * y = n := by
  constructor
  · rintro ⟨x, y, hx, hy, hcop, he⟩
    lift x to ℕ using hx with u
    lift y to ℕ using hy with v
    exact ⟨u, v, by simpa using hcop, he⟩
  · rintro ⟨x, y, hcop, he⟩
    exact ⟨x, y, by positivity, by positivity, by simpa using hcop, he⟩

private theorem actual_maximum {A B : ℕ} (hA : 3 ≤ A) (hB : 3 ≤ B)
    (hAB : A.Coprime B) :
    ∃ m : ℤ, IsGreatest (missing A B) m ∧ 1 ≤ m := by
  have hone : (1 : ℤ) ∈ missing A B := by
    intro h
    obtain ⟨x, y, _hcop, he⟩ := (represented_nat A B 1).mp h
    have ha : (3 : ℤ) ≤ A := by exact_mod_cast hA
    have hb : (3 : ℤ) ≤ B := by exact_mod_cast hB
    have hx : (0 : ℤ) ≤ x := by positivity
    have hy : (0 : ℤ) ≤ y := by positivity
    have hsum : (3 : ℤ) * ((x : ℤ) + y) ≤ 1 := by nlinarith
    have hzero : (x : ℤ) = 0 ∧ (y : ℤ) = 0 := by omega
    simp [hzero.1, hzero.2] at he
  have hbdd : ∃ t : ℤ, ∀ z : ℤ, z ∈ missing A B → z ≤ t := by
    refine ⟨(16 ^ 7 * (A * B) ^ 2 : ℕ), ?_⟩
    intro z hz
    by_contra hle
    have hz0 : 0 ≤ z := by
      have : (0 : ℤ) ≤ (16 ^ 7 * (A * B) ^ 2 : ℕ) := by positivity
      omega
    lift z to ℕ using hz0 with n
    have hn : 16 ^ 7 * (A * B) ^ 2 < n := by exact_mod_cast (lt_of_not_ge hle)
    obtain ⟨x, y, hcop, he⟩ := primitive_tail (by omega) (by omega) hAB hn
    apply hz
    apply (represented_nat A B n).mpr
    exact ⟨x, y, hcop, by exact_mod_cast he⟩
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨1, hone⟩
  exact ⟨m, ⟨hm, hmax⟩, hmax 1 hone⟩

private theorem sourceG_eq {a b m : ℤ} (hm : IsGreatest (missing a b) m) :
    sourceG a b = ((m : ℝ) : EReal) := by
  have hex : ∃ m, IsGreatest (missing a b) m := ⟨m, hm⟩
  rw [sourceG, dite_eq_left hex, hex.choose_spec.unique hm]

private theorem scale_missing {A B u : ℕ} {n : ℤ} (hu : 0 < u)
    (hAu : A.Coprime u) (hn : n ∈ missing A B) :
    (u : ℤ) * n ∈ missing A (u * B) := by
  intro h
  obtain ⟨x, y, hcop, he⟩ := (represented_nat A (u * B) ((u : ℤ) * n)).mp h
  have hdiv : (u : ℤ) ∣ (A : ℤ) * x := by
    refine ⟨n - (B : ℤ) * y, ?_⟩
    nlinarith [he]
  have hd : u ∣ A * x := by exact_mod_cast hdiv
  obtain ⟨t, ht⟩ := hAu.symm.dvd_of_dvd_mul_left hd
  apply hn
  apply (represented_nat A B n).mpr
  refine ⟨t, y, ?_, ?_⟩
  · rw [ht] at hcop
    exact hcop.coprime_mul_left
  · rw [ht] at he
    push_cast at he
    have hup : (0 : ℤ) < u := by exact_mod_cast hu
    nlinarith [he]

private theorem successor_isLeast {a b : ℤ} (ha : 3 ≤ a) (hb : 3 ≤ b) :
    IsLeast {c : ℤ | b < c ∧ a.natAbs.Coprime c.natAbs} (successor a b) := by
  have hbd : BddBelow {c : ℤ | b < c ∧ a.natAbs.Coprime c.natAbs} :=
    ⟨b, fun c hc => hc.1.le⟩
  have hne : ({c : ℤ | b < c ∧ a.natAbs.Coprime c.natAbs} : Set ℤ).Nonempty := by
    lift a to ℕ using (by omega : 0 ≤ a) with A
    lift b to ℕ using (by omega : 0 ≤ b) with B
    refine ⟨((A * (B + 1) + 1 : ℕ) : ℤ), ?_, ?_⟩
    · have ha' : 3 ≤ A := by exact_mod_cast ha
      have hb' : 3 ≤ B := by exact_mod_cast hb
      exact_mod_cast (show B < A * (B + 1) + 1 by nlinarith)
    · norm_cast
      simp [Nat.coprime_mul_left_add_right]
  exact ⟨Int.csInf_mem hne hbd, fun c hc => csInf_le hbd hc⟩

private def witnessA : ℕ := 87841397512641630

private theorem witness_successor : successor witnessA 7 = 49 := by
  have ha : (3 : ℤ) ≤ witnessA := by norm_num [witnessA]
  have hgood : witnessA.Coprime 49 := by decide
  have hbad : ∀ k : Fin 49, 7 < k.val → ¬ witnessA.Coprime k.val := by decide
  have hleast : IsLeast {c : ℤ | 7 < c ∧ (witnessA : ℤ).natAbs.Coprime c.natAbs} 49 := by
    constructor
    · exact ⟨by norm_num, by simpa using hgood⟩
    · intro c hc
      change 7 < c ∧ witnessA.Coprime c.natAbs at hc
      by_contra h
      have hc0 : 0 ≤ c := by omega
      lift c to ℕ using hc0 with k
      have hk : k < 49 := by exact_mod_cast (lt_of_not_ge h)
      have hk7 : 7 < k := by exact_mod_cast hc.1
      exact hbad ⟨k, hk⟩ hk7 (by simpa using hc.2)
  exact (successor_isLeast ha (by norm_num)).unique hleast

/-- The unrestricted source conjecture is false. -/
theorem result : ¬ fullClaim := by
  intro hclaim
  have hA : 3 ≤ witnessA := by norm_num [witnessA]
  have h7 : witnessA.Coprime 7 := by decide
  have h49 : witnessA.Coprime 49 := by decide
  obtain ⟨m, hm, hmpos⟩ := actual_maximum hA (by decide : 3 ≤ 7) h7
  obtain ⟨M, hM, _hMpos⟩ := actual_maximum hA (by decide : 3 ≤ 49) h49
  have hscaled : (7 : ℤ) * m ∈ missing witnessA 49 := by
    simpa using scale_missing (B := 7) (u := 7) (by decide) h7 hm.1
  have hbound : 7 * m ≤ M := hM.2 hscaled
  have hg := hclaim witnessA 7 (by exact_mod_cast hA) (by norm_num) (by simpa using h7)
  norm_num only [Nat.cast_ofNat] at hm hM
  rw [witness_successor, sourceG_eq hm, sourceG_eq hM] at hg
  have hreal : (M : ℝ) / (m : ℝ) ≤ 5 := by
    exact EReal.coe_le_coe_iff.mp hg
  have hmp : (0 : ℝ) < m := by exact_mod_cast (show (0 : ℤ) < m by omega)
  have hbound' : 7 * (m : ℝ) ≤ M := by exact_mod_cast hbound
  have hviolation : (7 : ℝ) ≤ (M : ℝ) / (m : ℝ) := (le_div_iff₀ hmp).mpr hbound'
  linarith

end D5.S3.ArithUnits.JaffeSuccessorRatioRefutation
