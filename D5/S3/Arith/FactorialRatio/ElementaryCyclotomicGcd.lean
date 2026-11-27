/- GID: D5/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/ElementaryCyclotomicGcd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: The accumulated LCM identity and divisibility bound for cyclotomic carries. -/

module

public import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The integer prime-power carry product and its exact accumulated lcm deficit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd

open Finset
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd (div_mod_add)
open scoped BigOperators

@[expose] public def C (i : ℕ) : ℕ := (2 * i).centralBinom

@[expose] public def cutoff (N j : ℕ) : ℕ := 4 * (N - j) + 1

/-- Positive exponents of powers of \(p\) up to \(X\), for prime \(p\). -/
public abbrev levels (p X : ℕ) : Finset ℕ := Ico 1 (Nat.log p X + 1)

private def doubleCarry (r n : ℕ) : ℕ := (2 * n / r) % 2

@[expose] public def carry (r j : ℕ) : ℕ := (4 * j / r) % 2

@[expose] public def firstDegree (r : ℕ) : ℕ := (r + 2) / 4

@[expose] public def Exceptional (r j : ℕ) : Prop :=
  if r % 4 = 1 then r ∣ j else r ∣ 4 * j + 1

public instance exceptionalDecidable (r j : ℕ) : Decidable (Exceptional r j) := by
  unfold Exceptional
  split <;> infer_instance

@[expose] public def exceptionCount (N r : ℕ) : ℕ :=
  if r % 2 = 1 then ((range (N + 1 - firstDegree r)).filter (Exceptional r)).card else 0

@[expose] public def QStar (N j : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE (cutoff N j), ∏ t ∈ levels p (cutoff N j), p ^ carry (p ^ t) j

@[expose] public def HStar (N : ℕ) : ℕ := ∏ j ∈ range (N + 1), QStar N j

@[expose] public def EStar (N : ℕ) : ℕ :=
  2 ^ N * ∏ p ∈ Nat.primesLE (4 * N + 1),
    p ^ (∑ t ∈ levels p (4 * N + 1), exceptionCount N (p ^ t))

@[expose] public def rowProduct (N : ℕ) : ℕ := ∏ i ∈ range (N + 1), C i

@[expose] public def lcmProduct (N : ℕ) : ℕ := ∏ i ∈ range (N + 1), Nat.lcmUpto (4 * i + 1)

private theorem C_ne_zero (i : ℕ) : C i ≠ 0 := (Nat.centralBinom_pos _).ne'

private theorem firstDegree_le_iff {r k : ℕ} : firstDegree r ≤ k ↔ r ≤ 4 * k + 1 := by
  unfold firstDegree
  omega

private theorem carry_eq_doubleCarry (r j : ℕ) : carry r j = doubleCarry r (2 * j) := by
  simp only [carry, doubleCarry, ← mul_assoc, show (2 : ℕ) * 2 = 4 by decide]

private theorem doubleCarry_eq_ite {r : ℕ} (hr : 0 < r) (n : ℕ) :
    doubleCarry r n = if r ≤ n % r + n % r then 1 else 0 := by
  unfold doubleCarry
  rw [two_mul, (div_mod_add n n hr).1]
  obtain h | h := lt_or_ge (n % r + n % r) r
  · rw [Nat.div_eq_of_lt h, ite_eq_right (Nat.not_le.mpr h)]
    omega
  · have hlt : n % r + n % r < r * 2 := by
      have := Nat.mod_lt n hr
      omega
    have hdiv : (n % r + n % r) / r = 1 :=
      Nat.div_eq_of_lt_le (by simpa using h) (by simpa [Nat.mul_comm] using hlt)
    rw [hdiv, ite_eq_left h]
    omega

private theorem even_quotient {r j : ℕ} (hr : r % 2 = 1)
    (hrem : ((4 * j) % r) % 2 = 0) : (4 * j / r) % 2 = 0 := by
  have h := congrArg (fun x : ℕ => x % 2) (Nat.mod_add_div (4 * j) r)
  rw [Nat.add_mod ((4 * j) % r) (r * (4 * j / r)) 2,
    Nat.mul_mod r (4 * j / r) 2, hr, hrem] at h
  simp only [Nat.zero_add, Nat.one_mul, Nat.mod_mod] at h
  omega

/-- The paired carries at any odd integer level, including composite levels. -/
private theorem carry_shift_odd {r : ℕ} (hr : 3 ≤ r) (hodd : r % 2 = 1) (j : ℕ) :
    carry r (j + firstDegree r) + carry r j = if Exceptional r j then 0 else 1 := by
  have hpos : 0 < r := by omega
  have hrem := Nat.mod_lt (4 * j) hpos
  have hdecomp := Nat.mod_add_div (4 * j) r
  have hres : r % 4 = 1 ∨ r % 4 = 3 := by omega
  rcases hres with hres | hres
  · have he : 4 * firstDegree r + 1 = r := by unfold firstDegree; omega
    have hcop : r.Coprime 4 := by
      have h2 := (Nat.odd_iff.mpr hodd).coprime_two_right
      simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using h2.pow_right 2
    have hx : Exceptional r j ↔ (4 * j) % r = 0 := by
      simp only [Exceptional, hres, ite_true, ← Nat.dvd_iff_mod_eq_zero]
      exact hcop.dvd_mul_left.symm
    by_cases hz : (4 * j) % r = 0
    · have hd : 4 * (j + firstDegree r) / r = 4 * j / r := by
        apply Nat.div_eq_of_lt_le <;>
          simp only [Nat.add_mul, Nat.one_mul, mul_comm (4 * j / r) r] <;> omega
      have hq := even_quotient (j := j) hodd (by rw [hz])
      rw [ite_eq_left (hx.mpr hz)]
      simp [carry, hd, hq]
    · have hd : 4 * (j + firstDegree r) / r = 4 * j / r + 1 := by
        apply Nat.div_eq_of_lt_le <;>
          simp only [Nat.add_mul, Nat.one_mul, mul_comm (4 * j / r) r] <;> omega
      rw [ite_eq_right (fun h => hz (hx.mp h))]
      simp only [carry, hd]
      omega
  · have he : 4 * firstDegree r = r + 1 := by unfold firstDegree; omega
    have h1 : 1 < r := by omega
    have hmod : (4 * j + 1) % r = ((4 * j) % r + 1) % r := by
      rw [Nat.add_mod (4 * j) 1 r, Nat.mod_eq_of_lt h1]
    have hx : Exceptional r j ↔ (4 * j) % r + 1 = r := by
      rw [Exceptional, ite_eq_right (by omega : r % 4 ≠ 1), Nat.dvd_iff_mod_eq_zero, hmod]
      by_cases hh : (4 * j) % r + 1 = r
      · simp [hh]
      · rw [Nat.mod_eq_of_lt (show (4 * j) % r + 1 < r by omega)]
        omega
    have hd : 4 * (j + firstDegree r) / r = (4 * j + 1) / r + 1 := by
      rw [show 4 * (j + firstDegree r) = (4 * j + 1) + r * 1 by omega,
        Nat.add_mul_div_left _ _ hpos]
    have hnext : (4 * j + 1) / r =
        4 * j / r + (if r ≤ (4 * j) % r + 1 then 1 else 0) := by
      rw [Nat.add_div hpos, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1, add_zero]
    by_cases ht : (4 * j) % r + 1 = r
    · have hq := even_quotient (j := j) hodd (by omega)
      rw [ite_eq_left (hx.mpr ht)]
      simp only [carry, hd, hnext, ite_eq_left (show r ≤ (4 * j) % r + 1 by omega)]
      omega
    · rw [ite_eq_right (fun h => ht (hx.mp h))]
      simp only [carry, hd, hnext, ite_eq_right (show ¬ r ≤ (4 * j) % r + 1 by omega), add_zero]
      omega

private theorem carry_two (j : ℕ) : carry 2 j = 0 := by
  unfold carry
  omega

/-- Every positive multiple of four has a paired contribution of one. -/
private theorem carry_shift_four_dvd {r : ℕ} (hr : 0 < r) (h4 : 4 ∣ r) (j : ℕ) :
    carry r (j + firstDegree r) + carry r j = 1 := by
  obtain ⟨a, ha⟩ := h4
  have he : 4 * firstDegree r = r := by unfold firstDegree; omega
  have hd : 4 * (j + firstDegree r) / r = 4 * j / r + 1 := by
    rw [show 4 * (j + firstDegree r) = 4 * j + r * 1 by omega,
      Nat.add_mul_div_left _ _ hr]
  simp only [carry, hd]
  omega

private theorem mem_levels_iff {p X t : ℕ} (hp : p.Prime) :
    t ∈ levels p X ↔ 1 ≤ t ∧ p ^ t ≤ X := by
  simp only [mem_Ico, Nat.lt_succ_iff]
  by_cases hX : X = 0
  · subst X
    simp only [Nat.log_zero_right, Nat.le_zero]
    have hp0 := pow_ne_zero t hp.ne_zero
    omega
  · rw [Nat.le_log_iff_pow_le hp.one_lt hX]

private theorem card_filter_eq_sum {α : Type*} (s : Finset α) (P : α → Prop)
    [DecidablePred P] : (s.filter P).card = ∑ x ∈ s, if P x then 1 else 0 := by
  rw [← sum_filter, ← card_eq_sum_ones]

private theorem doubleCarry_sum {p X n : ℕ} (hp : p.Prime) (hn : 2 * n ≤ X) :
    n.centralBinom.factorization p = ∑ t ∈ levels p X, doubleCarry (p ^ t) n := by
  have hlog : Nat.log p (2 * n) < Nat.log p X + 1 :=
    Nat.lt_succ_of_le (Nat.log_mono_right hn)
  unfold Nat.centralBinom
  rw [Nat.factorization_choose hp (by omega : n ≤ 2 * n) hlog,
      show 2 * n - n = n by omega, card_filter_eq_sum]
  exact sum_congr rfl fun t _ => (doubleCarry_eq_ite (pow_pos hp.pos t) n).symm

private theorem C_factorization {p X i : ℕ} (hp : p.Prime) (hi : 4 * i ≤ X) :
    (C i).factorization p = ∑ t ∈ levels p X, carry (p ^ t) i := by
  simpa only [C, carry_eq_doubleCarry] using doubleCarry_sum hp (by omega : 2 * (2 * i) ≤ X)

private theorem factorization_eq_sum_dvd {p X n : ℕ} (hp : p.Prime) (hn : 0 < n) (hnX : n ≤ X) :
    n.factorization p = ∑ t ∈ levels p X, if p ^ t ∣ n then 1 else 0 := by
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hn
      (hnX.trans_lt (Nat.lt_pow_succ_log_self hp.one_lt X)), card_filter_eq_sum]

/-- Reindex the levels below a smaller cutoff inside a larger one. -/
private theorem sum_levels_cutoff {p x X : ℕ} (hp : p.Prime) (hx : x ≤ X) (f : ℕ → ℕ) :
    (∑ t ∈ levels p X, if p ^ t ≤ x then f t else 0) = ∑ t ∈ levels p x, f t := by
  rw [← sum_filter]
  congr 1
  ext t
  simp only [mem_filter, mem_levels_iff hp]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hx⟩, h.2⟩⟩

private theorem prime_product_ne_zero (X : ℕ) (f : ℕ → ℕ) :
    (∏ p ∈ Nat.primesLE X, p ^ f p) ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hp => pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero

private theorem factorization_prime_product {X p : ℕ} (f : ℕ → ℕ) :
    (∏ q ∈ Nat.primesLE X, q ^ f q).factorization p =
      if p ∈ Nat.primesLE X then f p else 0 := by
  rw [Nat.factorization_prod_apply
    (fun q hq => pow_ne_zero (f q) (Nat.prime_of_mem_primesLE hq).ne_zero)]
  calc
    (∑ q ∈ Nat.primesLE X, (q ^ f q).factorization p) =
        ∑ q ∈ Nat.primesLE X, if q = p then f q else 0 := by
      refine sum_congr rfl fun q hq => ?_
      rw [(Nat.prime_of_mem_primesLE hq).factorization_pow, Finsupp.single_apply]
    _ = _ := sum_ite_eq' _ _ _

private theorem sum_levels_eq_zero_of_lt {p X : ℕ} (hlt : X < p) (f : ℕ → ℕ) :
    (∑ t ∈ levels p X, f t) = 0 := by
  simp [Nat.log_of_lt hlt]

private theorem QStar_grouped (N j : ℕ) :
    QStar N j = ∏ p ∈ Nat.primesLE (cutoff N j),
      p ^ (∑ t ∈ levels p (cutoff N j), carry (p ^ t) j) := by
  unfold QStar
  exact prod_congr rfl (fun p _ => prod_pow_eq_pow_sum _ _ _)

private theorem QStar_ne_zero (N j : ℕ) : QStar N j ≠ 0 := by
  rw [QStar_grouped]
  exact prime_product_ne_zero _ _

private theorem HStar_ne_zero (N : ℕ) : HStar N ≠ 0 :=
  prod_ne_zero_iff.mpr fun j _ => QStar_ne_zero N j

private theorem EStar_ne_zero (N : ℕ) : EStar N ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) (prime_product_ne_zero _ _)

private theorem rowProduct_ne_zero (N : ℕ) : rowProduct N ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => C_ne_zero i

private theorem lcmProduct_ne_zero (N : ℕ) : lcmProduct N ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ _ => Nat.lcmUpto_ne_zero _

private theorem QStar_factorization {N j p X : ℕ} (hp : p.Prime) (hX : cutoff N j ≤ X) :
    (QStar N j).factorization p =
      ∑ t ∈ levels p X, if p ^ t ≤ cutoff N j then carry (p ^ t) j else 0 := by
  rw [sum_levels_cutoff hp hX, QStar_grouped, factorization_prime_product]
  by_cases h : p ≤ cutoff N j
  · rw [ite_eq_left (Nat.mem_primesLE.mpr ⟨h, hp⟩)]
  · rw [ite_eq_right (fun hm => h (Nat.mem_primesLE.mp hm).1),
        sum_levels_eq_zero_of_lt (lt_of_not_ge h)]

private theorem EStar_factorization (N : ℕ) {p : ℕ} (hp : p.Prime) :
    (EStar N).factorization p =
      (if p = 2 then N else 0) + ∑ t ∈ levels p (4 * N + 1), exceptionCount N (p ^ t) := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  unfold EStar
  rw [Nat.factorization_mul (pow_ne_zero _ h2.ne_zero) (prime_product_ne_zero _ _),
    Finsupp.add_apply, h2.factorization_pow, Finsupp.single_apply, factorization_prime_product]
  have he : (if p ∈ Nat.primesLE (4 * N + 1) then
      ∑ t ∈ levels p (4 * N + 1), exceptionCount N (p ^ t) else 0) =
      ∑ t ∈ levels p (4 * N + 1), exceptionCount N (p ^ t) := by
    by_cases h : p ≤ 4 * N + 1
    · rw [ite_eq_left (Nat.mem_primesLE.mpr ⟨h, hp⟩)]
    · rw [ite_eq_right (fun hm => h (Nat.mem_primesLE.mp hm).1),
          sum_levels_eq_zero_of_lt (lt_of_not_ge h)]
  simp only [he, (eq_comm : (2 : ℕ) = p ↔ p = 2)]

private theorem sum_shift (m e : ℕ) (f : ℕ → ℕ) (hz : ∀ i < e, f i = 0) :
    (∑ i ∈ range m, f i) = ∑ j ∈ range (m - e), f (j + e) := by
  by_cases he : e ≤ m
  · have h := sum_range_add f e (m - e)
    rw [Nat.add_sub_of_le he, sum_eq_zero (fun i hi => hz i (mem_range.mp hi)), zero_add] at h
    exact h.trans (sum_congr rfl fun j _ => congrArg f (add_comm e j))
  · rw [Nat.sub_eq_zero_of_le (le_of_not_ge he), sum_range_zero]
    exact sum_eq_zero fun i hi => hz i (by have := mem_range.mp hi; omega)

private theorem sum_cutoff (N r : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ range (N + 1), if r ≤ cutoff N j then f j else 0) =
      ∑ j ∈ range (N + 1 - firstDegree r), f j := by
  rw [← sum_filter]
  congr 1
  ext j
  simp only [mem_filter, mem_range, cutoff, ← firstDegree_le_iff]
  omega

private theorem sum_lcm_level (N r : ℕ) :
    (∑ i ∈ range (N + 1), if r ≤ 4 * i + 1 then 1 else 0) = N + 1 - firstDegree r := by
  rw [sum_shift (N + 1) (firstDegree r) (fun i => if r ≤ 4 * i + 1 then 1 else 0)
    (fun i hi => ite_eq_right (by rw [← firstDegree_le_iff]; omega))]
  have h (j : ℕ) : r ≤ 4 * (j + firstDegree r) + 1 :=
    firstDegree_le_iff.mp (by omega)
  simp only [h, ite_true, ← card_eq_sum_ones, card_range]

private theorem sum_carry_below (N r : ℕ) :
    (∑ i ∈ range (N + 1), carry r i) =
      ∑ j ∈ range (N + 1 - firstDegree r), carry r (j + firstDegree r) := by
  apply sum_shift
  intro i hi
  have hr : 4 * i < r := by
    have h := @firstDegree_le_iff r i
    omega
  simp [carry, Nat.div_eq_of_lt hr]

private theorem level_balance (N r : ℕ) (hr : 2 ≤ r) (h : r = 2 ∨ r % 2 = 1 ∨ 4 ∣ r) :
    (∑ i ∈ range (N + 1), carry r i) +
      (∑ j ∈ range (N + 1), if r ≤ cutoff N j then carry r j else 0) +
      exceptionCount N r + (if r = 2 then N else 0) =
      ∑ i ∈ range (N + 1), if r ≤ 4 * i + 1 then 1 else 0 := by
  rw [sum_lcm_level N r]
  rcases h with rfl | hodd | h4
  · simp [carry_two, exceptionCount, firstDegree]
  all_goals
    rw [sum_carry_below, sum_cutoff, ← sum_add_distrib]
  · rw [exceptionCount, ite_eq_left hodd, ite_eq_right (by omega : r ≠ 2), add_zero,
        card_filter_eq_sum, ← sum_add_distrib]
    calc
      _ = ∑ _j ∈ range (N + 1 - firstDegree r), (1 : ℕ) := by
        refine sum_congr rfl fun j _ => ?_
        rw [carry_shift_odd (by omega) hodd]
        by_cases h : Exceptional r j <;> simp [h]
      _ = _ := by simp
  · obtain ⟨a, ha⟩ := h4
    have he : r % 2 ≠ 1 := by omega
    have hne : r ≠ 2 := by omega
    rw [exceptionCount, ite_eq_right he, ite_eq_right hne, add_zero, add_zero]
    simp [carry_shift_four_dvd (by omega : 0 < r) (show 4 ∣ r from ⟨a, ha⟩)]

private theorem prime_power_cases {p t : ℕ} (hp : p.Prime) (ht : 1 ≤ t) :
    2 ≤ p ^ t ∧ (p ^ t = 2 ∨ p ^ t % 2 = 1 ∨ 4 ∣ p ^ t) := by
  have hle : p ≤ p ^ t := by
    simpa only [pow_one] using (Nat.pow_le_pow_iff_right hp.one_lt).mpr ht
  refine ⟨hp.two_le.trans hle, ?_⟩
  rcases hp.eq_two_or_odd with rfl | hpodd
  · by_cases hh : t = 1
    · exact Or.inl (by simp [hh])
    · exact Or.inr (Or.inr (by
        simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using
          (Nat.pow_dvd_pow (2 : ℕ) (show 2 ≤ t by omega))))
  · exact Or.inr (Or.inl (Nat.odd_iff.mp ((Nat.odd_iff.mpr hpodd).pow)))

private theorem lcm_level_sum {p X x : ℕ} (hp : p.Prime) (hx : x ≤ X) :
    (Nat.lcmUpto x).factorization p = ∑ t ∈ levels p X, if p ^ t ≤ x then 1 else 0 := by
  rw [Nat.factorization_lcmUpto _ hp, sum_levels_cutoff hp hx]
  simp [levels]

private theorem sum_two_level (N p : ℕ) (hp : p.Prime) :
    (∑ t ∈ levels p (4 * N + 1), if p ^ t = 2 then N else 0) =
      if p = 2 then N else 0 := by
  have he (t : ℕ) (ht : t ∈ levels p (4 * N + 1)) : p ^ t = 2 ↔ p = 2 ∧ t = 1 := by
    have ht' := (mem_levels_iff hp).mp ht
    have hle : p ≤ p ^ t := by
      simpa only [pow_one] using (Nat.pow_le_pow_iff_right hp.one_lt).mpr ht'.1
    constructor
    · intro h
      have h2 : p = 2 := by have := hp.two_le; omega
      subst p
      have ht1 : t ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (by
        simpa only [pow_one] using h.le)
      exact ⟨rfl, le_antisymm ht1 ht'.1⟩
    · rintro ⟨rfl, rfl⟩
      simp
  by_cases h : p = 2
  · subst p
    by_cases hN : N = 0
    · simp [hN]
    · have h1 : 1 ∈ levels 2 (4 * N + 1) :=
        (mem_levels_iff Nat.prime_two).mpr ⟨le_rfl, by simp only [pow_one]; omega⟩
      rw [ite_eq_left rfl, sum_eq_single_of_mem 1 h1]
      · simp
      · intro t ht ht1
        exact ite_eq_right (fun h => ht1 ((he t ht).mp h).2)
  · rw [ite_eq_right h]
    exact sum_eq_zero fun t ht => ite_eq_right (fun ht2 => h ((he t ht).mp ht2).1)

/-- The accumulated lcm is the binomial product times the carry product and the explicit deficit. -/
public theorem lcmProduct_eq (N : ℕ) : lcmProduct N = rowProduct N * HStar N * EStar N := by
  apply Nat.eq_of_factorization_eq (lcmProduct_ne_zero N)
    (mul_ne_zero (mul_ne_zero (rowProduct_ne_zero N) (HStar_ne_zero N)) (EStar_ne_zero N))
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (mul_ne_zero (rowProduct_ne_zero N) (HStar_ne_zero N))
      (EStar_ne_zero N), Nat.factorization_mul (rowProduct_ne_zero N) (HStar_ne_zero N),
      Finsupp.add_apply, Finsupp.add_apply, EStar_factorization N hp,
      lcmProduct, rowProduct, HStar,
      Nat.factorization_prod_apply (fun i _ => Nat.lcmUpto_ne_zero (4 * i + 1)),
      Nat.factorization_prod_apply (fun i _ => C_ne_zero i),
      Nat.factorization_prod_apply (fun j _ => QStar_ne_zero N j)]
    let T := levels p (4 * N + 1)
    have hL : (∑ i ∈ range (N + 1), (Nat.lcmUpto (4 * i + 1)).factorization p) =
        ∑ t ∈ T, ∑ i ∈ range (N + 1), if p ^ t ≤ 4 * i + 1 then 1 else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun i hi => lcm_level_sum hp (by have := mem_range.mp hi; omega)
    have hC : (∑ i ∈ range (N + 1), (C i).factorization p) =
        ∑ t ∈ T, ∑ i ∈ range (N + 1), carry (p ^ t) i := by
      rw [sum_comm]
      exact sum_congr rfl fun i hi => C_factorization hp (by have := mem_range.mp hi; omega)
    have hQ : (∑ j ∈ range (N + 1), (QStar N j).factorization p) =
        ∑ t ∈ T, ∑ j ∈ range (N + 1), if p ^ t ≤ cutoff N j then carry (p ^ t) j else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun j _ => QStar_factorization hp (by unfold cutoff; omega)
    rw [hL, hC, hQ, ← sum_two_level N p hp]
    rw [show T = levels p (4 * N + 1) by rfl]
    calc
      _ = ∑ t ∈ levels p (4 * N + 1),
          ((∑ i ∈ range (N + 1), carry (p ^ t) i) +
           (∑ j ∈ range (N + 1), if p ^ t ≤ cutoff N j then carry (p ^ t) j else 0) +
           exceptionCount N (p ^ t) + (if p ^ t = 2 then N else 0)) := by
        refine sum_congr rfl fun t ht => ?_
        have h := prime_power_cases hp ((mem_levels_iff hp).mp ht).1
        exact (level_balance N (p ^ t) h.1 h.2).symm
      _ = _ := by
        simp only [sum_add_distrib]
        ac_rfl
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem exceptionCount_sum (N r : ℕ) :
    exceptionCount N r =
      ∑ j ∈ range (N + 1),
        if r % 2 = 1 ∧ j < N + 1 - firstDegree r ∧ Exceptional r j then 1 else 0 := by
  by_cases hr : r % 2 = 1
  · rw [exceptionCount, ite_eq_left hr, card_filter_eq_sum]
    simp only [hr, true_and, ← sum_filter]
    congr 1
    ext j
    simp only [mem_filter, mem_range]
    exact ⟨fun ⟨hj, he⟩ => ⟨hj.trans_le (Nat.sub_le _ _), hj, he⟩,
      fun ⟨_, hj, he⟩ => ⟨hj, he⟩⟩
  · simp [exceptionCount, hr]

/-- A finite integer bound on the error. The lcm on the right pays the index zero. -/
public theorem EStar_dvd (N : ℕ) :
    EStar N ∣ 2 ^ N * Nat.lcmUpto (4 * N + 1) *
      ∏ j ∈ range N, (j + 1) * (4 * (j + 1) + 1) := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  have hne (j : ℕ) : (j + 1) * (4 * (j + 1) + 1) ≠ 0 := by positivity
  apply (Nat.factorization_prime_le_iff_dvd (EStar_ne_zero N) (mul_ne_zero
    (mul_ne_zero (pow_ne_zero _ h2.ne_zero) (Nat.lcmUpto_ne_zero _))
    (prod_ne_zero_iff.mpr fun j _ => hne j))).mp
  intro p hp
  rw [EStar_factorization N hp, Nat.factorization_mul
    (mul_ne_zero (pow_ne_zero _ h2.ne_zero) (Nat.lcmUpto_ne_zero _))
    (prod_ne_zero_iff.mpr fun j _ => hne j),
    Nat.factorization_mul (pow_ne_zero _ h2.ne_zero) (Nat.lcmUpto_ne_zero _),
    Finsupp.add_apply, Finsupp.add_apply, h2.factorization_pow, Finsupp.single_apply]
  simp only [(eq_comm : (2 : ℕ) = p ↔ p = 2), add_assoc, Nat.add_le_add_iff_left]
  simp only [exceptionCount_sum]
  rw [sum_comm, sum_range_succ']
  have hzero :
      (∑ t ∈ levels p (4 * N + 1),
        if p ^ t % 2 = 1 ∧ 0 < N + 1 - firstDegree (p ^ t) ∧ Exceptional (p ^ t) 0
        then 1 else 0) ≤ (Nat.lcmUpto (4 * N + 1)).factorization p := by
    rw [Nat.factorization_lcmUpto _ hp]
    calc
      _ ≤ ∑ _t ∈ levels p (4 * N + 1), (1 : ℕ) := by
        exact sum_le_sum (fun _ _ => by split <;> omega)
      _ = _ := by simp [levels]
  have hpos (j : ℕ) (hj : j ∈ range N) :
      (∑ t ∈ levels p (4 * N + 1),
        if p ^ t % 2 = 1 ∧ j + 1 < N + 1 - firstDegree (p ^ t) ∧ Exceptional (p ^ t) (j + 1)
        then 1 else 0) ≤ ((j + 1) * (4 * (j + 1) + 1)).factorization p := by
    have hj' := mem_range.mp hj
    rw [Nat.factorization_mul (by positivity : j + 1 ≠ 0)
      (by positivity : 4 * (j + 1) + 1 ≠ 0), Finsupp.add_apply,
      factorization_eq_sum_dvd hp (by omega : 0 < j + 1) (by omega : j + 1 ≤ 4 * N + 1),
      factorization_eq_sum_dvd hp (by omega : 0 < 4 * (j + 1) + 1)
        (by omega : 4 * (j + 1) + 1 ≤ 4 * N + 1), ← sum_add_distrib]
    refine sum_le_sum fun t _ => ?_
    by_cases he : p ^ t % 2 = 1 ∧ j + 1 < N + 1 - firstDegree (p ^ t) ∧
        Exceptional (p ^ t) (j + 1)
    · rw [ite_eq_left he]
      have hd := he.2.2
      unfold Exceptional at hd
      split at hd
      · simp [hd]
      · simp [hd]
    · rw [ite_eq_right he]
      exact Nat.zero_le _
  rw [Nat.factorization_prod_apply (fun j _ => hne j)]
  exact (add_le_add (sum_le_sum hpos) hzero).trans_eq (add_comm _ _)

private theorem log_mul_nat {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log ((a * b : ℕ) : ℝ) = Real.log a + Real.log b := by
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]

private theorem log_prod_nat {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    Real.log ((∏ i ∈ s, f i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (f i) := by
  rw [Nat.cast_prod, Real.log_prod (fun i hi => by exact_mod_cast hf i hi)]

/-- The exact comparison before estimating the central-binomial and exceptional terms. -/
private theorem log_HStar_exact (N : ℕ) :
    Real.log (HStar N) = (∑ i ∈ range (N + 1), Chebyshev.psi ((4 * i + 1 : ℕ) : ℝ)) -
      Real.log (rowProduct N) - Real.log (EStar N) := by
  have h := congrArg (fun n : ℕ => Real.log (n : ℝ)) (lcmProduct_eq N)
  change Real.log (lcmProduct N) = Real.log ((rowProduct N * HStar N * EStar N : ℕ) : ℝ) at h
  rw [log_mul_nat (mul_ne_zero (rowProduct_ne_zero N) (HStar_ne_zero N)) (EStar_ne_zero N),
    log_mul_nat (rowProduct_ne_zero N) (HStar_ne_zero N), lcmProduct,
    log_prod_nat _ _ (fun i _ => Nat.lcmUpto_ne_zero (4 * i + 1))] at h
  simp_rw [← Chebyshev.psi_eq_log_lcmUpto] at h
  linarith

private theorem log_EStar_bounds (N : ℕ) :
    0 ≤ Real.log (EStar N) ∧
    Real.log (EStar N) ≤ (N : ℝ) * Real.log 2 + Chebyshev.psi ((4 * N + 1 : ℕ) : ℝ) +
      (∑ j ∈ range N, Real.log (((j + 1) * (4 * (j + 1) + 1) : ℕ) : ℝ)) := by
  let f (j : ℕ) := (j + 1) * (4 * (j + 1) + 1)
  have hf (j : ℕ) : f j ≠ 0 := by dsimp [f]; positivity
  have h2 : (2 : ℕ) ^ N ≠ 0 := pow_ne_zero _ (by decide)
  have hpos : 0 < EStar N := Nat.pos_of_ne_zero (EStar_ne_zero N)
  refine ⟨Real.log_nonneg (by exact_mod_cast hpos), ?_⟩
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero
    (mul_ne_zero h2 (Nat.lcmUpto_ne_zero (4 * N + 1)))
    (prod_ne_zero_iff.mpr (fun j _ => hf j)))) (EStar_dvd N)
  have hlog : Real.log (EStar N) ≤
      Real.log (((2 : ℕ) ^ N * Nat.lcmUpto (4 * N + 1) * ∏ j ∈ range N, f j : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hle)
  rw [log_mul_nat (mul_ne_zero h2 (Nat.lcmUpto_ne_zero (4 * N + 1)))
    (prod_ne_zero_iff.mpr (fun j _ => hf j)),
    log_mul_nat h2 (Nat.lcmUpto_ne_zero (4 * N + 1)), Nat.cast_pow, Real.log_pow,
    ← Chebyshev.psi_eq_log_lcmUpto, log_prod_nat _ _ (fun j _ => hf j)] at hlog
  simpa only [f, Nat.cast_ofNat] using hlog

private theorem log_C_bounds (i : ℕ) :
    (4 * (i : ℝ)) * Real.log 2 - Real.log ((4 * i + 1 : ℕ) : ℝ) ≤ Real.log (C i) ∧
    Real.log (C i) ≤ (4 * (i : ℝ)) * Real.log 2 := by
  have hlo : (4 : ℕ) ^ (2 * i) ≤ (4 * i + 1) * C i := by
    simpa only [C, ← mul_assoc, show (2 : ℕ) * 2 = 4 by decide] using
      Nat.four_pow_le_two_mul_add_one_mul_centralBinom (2 * i)
  have hhi : C i ≤ (4 : ℕ) ^ (2 * i) := Nat.centralBinom_le_four_pow _
  have hpos : 0 < C i := Nat.pos_of_ne_zero (C_ne_zero i)
  have hl : Real.log ((4 : ℝ) ^ (2 * i)) ≤ Real.log (((4 * i + 1) * C i : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hlo)
  have hu : Real.log (C i) ≤ Real.log ((4 : ℝ) ^ (2 * i)) :=
    Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hhi)
  have hpow : Real.log ((4 : ℝ) ^ (2 * i)) = (4 * (i : ℝ)) * Real.log 2 := by
    rw [Real.log_pow, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [log_mul_nat (by positivity) (C_ne_zero i), hpow] at hl
  rw [hpow] at hu
  exact ⟨by linarith, hu⟩

private theorem sum_log_C_main (N : ℕ) :
    (∑ i ∈ range (N + 1), (4 * (i : ℝ)) * Real.log 2) =
      2 * Real.log 2 * (N : ℝ) * ((N : ℝ) + 1) := by
  have h := sum_range_id_mul_two (N + 1)
  rw [Nat.add_sub_cancel] at h
  have hr : (∑ i ∈ range (N + 1), (i : ℝ)) * 2 = ((N : ℝ) + 1) * N := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) h
    push_cast at hc
    exact hc
  calc
    _ = 4 * (∑ i ∈ range (N + 1), (i : ℝ)) * Real.log 2 := by
      rw [mul_sum, sum_mul]
    _ = 2 * ((∑ i ∈ range (N + 1), (i : ℝ)) * 2) * Real.log 2 := by ring
    _ = _ := by rw [hr]; ring

/-- The error in the sampled Chebyshev comparison, with the two one-sided bounds. -/
private theorem log_HStar_comparison (N : ℕ) :
    let main := (∑ i ∈ range (N + 1), Chebyshev.psi ((4 * i + 1 : ℕ) : ℝ)) -
      2 * Real.log 2 * (N : ℝ) * ((N : ℝ) + 1)
    main - ((N : ℝ) * Real.log 2 + Chebyshev.psi ((4 * N + 1 : ℕ) : ℝ) +
      (∑ j ∈ range N, Real.log (((j + 1) * (4 * (j + 1) + 1) : ℕ) : ℝ))) ≤
        Real.log (HStar N) ∧
      Real.log (HStar N) ≤ main + ∑ i ∈ range (N + 1), Real.log ((4 * i + 1 : ℕ) : ℝ) := by
  dsimp only
  have hlo := sum_le_sum (s := range (N + 1)) (fun i _ => (log_C_bounds i).1)
  have hhi := sum_le_sum (s := range (N + 1)) (fun i _ => (log_C_bounds i).2)
  have hrow : Real.log (rowProduct N) = ∑ i ∈ range (N + 1), Real.log (C i) :=
    log_prod_nat _ _ (fun i _ => C_ne_zero i)
  rw [sum_sub_distrib, sum_log_C_main, ← hrow] at hlo
  rw [sum_log_C_main, ← hrow] at hhi
  have herr := log_EStar_bounds N
  rw [log_HStar_exact]
  exact ⟨by linarith [herr.2], by linarith [herr.1]⟩

private theorem log_cutoff_le {N i : ℕ} (hi : i ≤ N) :
    Real.log ((4 * i + 1 : ℕ) : ℝ) ≤ 2 * Real.log ((N : ℝ) + 2) := by
  have h : (4 * (i : ℝ) + 1) ≤ ((N : ℝ) + 2) ^ 2 := by
    have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
    nlinarith [sq_nonneg (N : ℝ)]
  have hlog := Real.log_le_log (by positivity : 0 < 4 * (i : ℝ) + 1) h
  rw [Real.log_pow] at hlog
  simpa using hlog

private theorem log_exception_term_le {N j : ℕ} (hj : j < N) :
    Real.log (((j + 1) * (4 * (j + 1) + 1) : ℕ) : ℝ) ≤
      3 * Real.log ((N : ℝ) + 2) := by
  rw [log_mul_nat (by positivity) (by positivity)]
  have hj' : j + 1 ≤ N := by omega
  have h : Real.log ((j + 1 : ℕ) : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    norm_cast
    omega
  linarith [log_cutoff_le hj']

private theorem psi_cutoff_le {N : ℕ} (hN : 1 ≤ N) :
    Chebyshev.psi ((4 * N + 1 : ℕ) : ℝ) ≤ 10 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by
  let m := 4 * N + 1
  have hcount : Nat.primeCounting m ≤ m := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    calc
      _ ≤ (Icc 1 m).card := by
        apply card_le_card
        intro p hp
        obtain ⟨hpm, hprime⟩ := Nat.mem_primesLE.mp hp
        exact mem_Icc.mpr ⟨hprime.one_lt.le, hpm⟩
      _ = m := by simp
  have hm : (m : ℝ) ≤ 5 * N := by
    have hmNat : m ≤ 5 * N := by dsimp [m]; omega
    exact_mod_cast hmNat
  have hlogm : 0 ≤ Real.log (m : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (by dsimp [m]; omega : 1 ≤ m)
  calc
    _ ≤ (Nat.primeCounting m : ℝ) * Real.log (m : ℝ) :=
      Chebyshev.psi_le_primeCounting_mul_log m
    _ ≤ (m : ℝ) * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hlogm
    _ ≤ (5 * (N : ℝ)) * (2 * Real.log ((N : ℝ) + 2)) :=
      mul_le_mul hm (log_cutoff_le (le_refl N)) hlogm (by positivity)
    _ = _ := by ring

/-- An explicit (O(Nlog(N+2))) error in the sampled Chebyshev comparison. -/
public theorem log_HStar_sub_sampled_chebyshev_le (N : ℕ) :
    |Real.log (HStar N) -
      ((∑ i ∈ range (N + 1), Chebyshev.psi ((4 * i + 1 : ℕ) : ℝ)) -
        2 * Real.log 2 * (N : ℝ) * ((N : ℝ) + 1))| ≤
      14 * (N : ℝ) * Real.log ((N : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h : HStar 0 = 1 := by decide
    norm_num [h, Chebyshev.psi_eq_zero_of_le_one]
  · have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    have hlog : 0 ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
      apply Real.log_le_log (by norm_num)
      have h : 0 ≤ (N : ℝ) := by positivity
      linarith
    have hE : (∑ j ∈ range N, Real.log (((j + 1) * (4 * (j + 1) + 1) : ℕ) : ℝ)) ≤
        (N : ℝ) * (3 * Real.log ((N : ℝ) + 2)) := by
      calc
        _ ≤ ∑ _j ∈ range N, 3 * Real.log ((N : ℝ) + 2) :=
          sum_le_sum fun j hj => log_exception_term_le (mem_range.mp hj)
        _ = _ := by simp
    have hC : (∑ i ∈ range (N + 1), Real.log ((4 * i + 1 : ℕ) : ℝ)) ≤
        ((N : ℝ) + 1) * (2 * Real.log ((N : ℝ) + 2)) := by
      calc
        _ ≤ ∑ _i ∈ range (N + 1), 2 * Real.log ((N : ℝ) + 2) :=
          sum_le_sum fun _ hi => log_cutoff_le (Nat.le_of_lt_succ (mem_range.mp hi))
        _ = _ := by simp
    have hb := log_HStar_comparison N
    dsimp only at hb
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hmain := psi_cutoff_le hN
    have h2 := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ (N : ℝ))
    have hmul := mul_le_mul_of_nonneg_right hNr hlog
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]

end D5.S3.Arith.FactorialRatio.ElementaryCyclotomicGcd
