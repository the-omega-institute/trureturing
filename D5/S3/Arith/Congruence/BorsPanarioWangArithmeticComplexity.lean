/- GID: D5/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BorsPanarioWangArithmeticComplexity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Positive lower limit for the arithmetic complexity of singleton partitions. -/

/-
admission_basis: open-problem-resolution (#19381; Proved)
escape_witness: none
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19486
Direct frozen dependencies: none (all imported mathematical owners are pinned Mathlib).
The public result has no hypotheses and proves claim, with the extended-real lower limit.
The congruence, separation and minimum definitions retain the source expressions.
The prime-power counting argument gives an eventual ratio of at least 1/64.
Per-declaration proof_shape and consumers (direct frozen dependencies: none throughout):
MCongruence: proof_shape: bind-only (source record); consumers: MCongruence.Holds, SpansTrivial.
MCongruence.Holds: proof_shape: bind-only (source predicate); consumers: SpansTrivial, holds_card.
SpansTrivial: proof_shape: bind-only (source predicate); consumers: acTrivial, per_prime_count.
acTrivial: proof_shape: bind-only (source minimum); consumers: claim, ac_prime_power_bound.
claim: proof_shape: bind-only (question's affirmative proposition); consumer: result.
missing_full_power: proof_shape: bind-only; escape_witness: none; consumers: per_prime_count.
holds_iff_nat_modEq: proof_shape: bind-only; escape_witness: none; consumers: holds_card, holds_of_same_fibre.
holds_card: proof_shape: bind-only; escape_witness: none; consumers: per_prime_count.
holds_of_same_fibre: proof_shape: bind-only; escape_witness: none; consumers: per_prime_count.
per_prime_count: proof_shape: content; escape_witness: none; consumers: per_prime_charge.
sum_le_prod_two_le: proof_shape: content; escape_witness: none; consumers: charge_le.
prime_power_two_le: proof_shape: bind-only; escape_witness: none; consumers: charge_le, small_log_bound, log_prime_power_sum.
prime_power_pairwise: proof_shape: bind-only; escape_witness: none; consumers: charge_le, small_log_bound.
charge_le: proof_shape: content; escape_witness: none; consumers: counting_lemma.
per_prime_charge: proof_shape: content; escape_witness: none; consumers: counting_lemma.
counting_lemma: proof_shape: content; escape_witness: none; consumers: prime_power_sum_le.
totient_half: proof_shape: bind-only; escape_witness: none; consumers: prime_power_sum_le.
prime_power_sum_le: proof_shape: content; escape_witness: none; consumers: ac_prime_power_bound.
small_log_bound: proof_shape: bind-only; escape_witness: none; consumers: logarithm_bound.
log_prime_power_sum: proof_shape: bind-only; escape_witness: none; consumers: logarithm_bound.
logarithm_bound: proof_shape: bind-only; escape_witness: none; consumers: ratio_bound_of_log.
spanning_nonempty: proof_shape: content; escape_witness: none; consumers: ac_prime_power_bound.
ac_prime_power_bound: proof_shape: content; escape_witness: none; consumers: ratio_bound_of_log.
ratio_bound_of_log: proof_shape: content; escape_witness: none; consumers: eventual_ratio_bound.
eventual_ratio_bound: proof_shape: content; escape_witness: none; consumers: result.
result: proof_shape: content; escape_witness: none; consumers: settling result.
-/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.Chebyshev

open scoped Classical

/-! Binding conventions for A. Bors, D. Panario and Q. Wang, "Functional graphs of generalized cyclotomic mappings
of finite fields", arXiv:2304.00181v1 (Memoirs of the European Mathematical Society 23): m-congruences, the arithmetic
partition they span (Definition 1.5), its arithmetic complexity AC, the trivial partition T_m of Z/mZ into
singletons, and Question 6.3.1, "Is it true that lim inf_{m→∞} AC(T_m)/(log² m/log log m) > 0?". -/

namespace D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity

/-- An m-congruence `x ≡ b (mod a)`: integers `a, b` with `a ≥ 1` and `a ∣ m`. -/
structure MCongruence (m : ℕ) where
  a : ℕ
  b : ℤ
  one_le : 1 ≤ a
  dvd : a ∣ m

/-- The congruence `x ≡ b (mod a)` at the standard representative `x ∈ {0, 1, …, m − 1}`. -/
def MCongruence.Holds {m : ℕ} (c : MCongruence m) (x : ℕ) : Prop :=
  (x : ℤ) ≡ c.b [ZMOD (c.a : ℤ)]

/-- The arithmetic partition `P(x ≡ b_j (mod a_j) : j = 1, …, K)` is the trivial partition `T_m` (every block a
singleton): two residues that satisfy exactly the same congruences of the system are equal. -/
def SpansTrivial {m K : ℕ} (c : Fin K → MCongruence m) : Prop :=
  ∀ x y : ℕ, x < m → y < m → (∀ j, (c j).Holds x ↔ (c j).Holds y) → x = y

/-- `AC(T_m)`: the smallest `K` such that `T_m` is spanned by `K` m-congruences (Definition 1.5(3)). -/
noncomputable def acTrivial (m : ℕ) : ℕ :=
  sInf {K : ℕ | ∃ c : Fin K → MCongruence m, SpansTrivial c}

/-- Question 6.3.1: `lim inf_{m→∞} AC(T_m)/(log² m/log log m) > 0`, the lower limit taken in the extended reals. -/
def claim : Prop :=
  0 < Filter.liminf
    (fun m : ℕ => (((acTrivial m : ℝ) / (Real.log m ^ 2 / Real.log (Real.log m)) : ℝ) : EReal)) Filter.atTop

end D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity

namespace D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity
open Finset

private theorem missing_full_power {m p r : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hr : r ∣ m) (hmiss : ¬ p ^ m.factorization p ∣ r) : r ∣ m / p := by
  have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero hm hr
  have hle := (Nat.factorization_le_iff_dvd hr0 hm).2 hr
  have hlt : r.factorization p < m.factorization p :=
    lt_of_not_ge ((hp.pow_dvd_iff_le_factorization hr0).not.mp hmiss)
  have hpd : p ∣ m := hp.dvd_iff_one_le_factorization hm |>.2 (by omega)
  have hdiv0 : m / p ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpd) hp.pos)
  apply (Nat.factorization_le_iff_dvd hr0 hdiv0).1
  intro l
  rw [Nat.factorization_div hpd, Finsupp.tsub_apply, hp.factorization]
  by_cases hl : l = p
  · subst l
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_eq_of_ne hl, Nat.sub_zero]
    exact hle l

private theorem holds_iff_nat_modEq {m : ℕ} (c : MCongruence m) (x : ℕ) :
    c.Holds x ↔ x ≡ (c.b : ZMod c.a).val [MOD c.a] := by
  have : NeZero c.a := ⟨Nat.ne_of_gt c.one_le⟩
  rw [MCongruence.Holds, ← ZMod.intCast_eq_intCast_iff, Int.cast_natCast,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]

private theorem holds_card {m : ℕ} (c : MCongruence m) :
    ((range m).filter c.Holds).card = m / c.a := by
  classical
  have ha : 0 < c.a := c.one_le
  simp_rw [holds_iff_nat_modEq]
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ ha,
    Nat.mod_eq_zero_of_dvd c.dvd]
  simp

private theorem holds_of_same_fibre {m n : ℕ} (c : MCongruence m) (hd : c.a ∣ n)
    {x y : ℕ} (hxy : x % n = y % n) : c.Holds x ↔ c.Holds y := by
  have h : x ≡ y [MOD c.a] := (show x ≡ y [MOD n] from hxy).of_dvd hd
  rw [holds_iff_nat_modEq, holds_iff_nat_modEq]
  exact ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

private theorem per_prime_count {m K p : ℕ} (hm : m ≠ 0) (hp : p.Prime) (hpm : p ∣ m)
    (c : Fin K → MCongruence m) (hc : SpansTrivial c) :
    m ≤ m / p + ∑ j ∈ (univ.filter fun j => p ^ m.factorization p ∣ (c j).a), m / (c j).a := by
  classical
  let s : Finset (Fin K) := univ.filter fun j => p ^ m.factorization p ∣ (c j).a
  let U : Finset ℕ := s.biUnion fun j => (range m).filter (c j).Holds
  have hn : 0 < m / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpm) hp.pos
  have hbad : ((range m) \ U).card ≤ m / p := by
    have : ((range m) \ U).card ≤ (range (m / p)).card := by
      apply card_le_card_of_injOn (fun x => x % (m / p))
      · intro x hx
        exact mem_range.mpr (Nat.mod_lt _ hn)
      · intro x hx y hy hxy
        have hx0 := mem_range.mp (mem_sdiff.mp hx).1
        have hy0 := mem_range.mp (mem_sdiff.mp hy).1
        apply hc x y hx0 hy0
        intro j
        by_cases hj : j ∈ s
        · have hxj : ¬ (c j).Holds x := by
            intro hh
            exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨mem_range.mpr hx0, hh⟩⟩)
          have hyj : ¬ (c j).Holds y := by
            intro hh
            exact (mem_sdiff.mp hy).2 (mem_biUnion.mpr ⟨j, hj, mem_filter.mpr ⟨mem_range.mpr hy0, hh⟩⟩)
          exact iff_of_false hxj hyj
        · have hmiss : ¬ p ^ m.factorization p ∣ (c j).a := by simpa [s] using hj
          exact holds_of_same_fibre (c j) (missing_full_power hm hp (c j).dvd hmiss) hxy
    simpa using this
  have hU : U.card ≤ ∑ j ∈ s, m / (c j).a := by
    calc
      U.card ≤ ∑ j ∈ s, ((range m).filter (c j).Holds).card := card_biUnion_le
      _ = _ := sum_congr rfl fun j _ => holds_card (c j)
  have hcard := card_le_card_sdiff_add_card (s := range m) (t := U)
  rw [card_range] at hcard
  exact hcard.trans (Nat.add_le_add hbad hU)

end D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity

namespace D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity
open Finset

private theorem sum_le_prod_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : ∑ i ∈ s, f i ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hfa : 2 ≤ f a := h a (mem_insert_self _ _)
    have hs : ∀ i ∈ s, 2 ≤ f i := fun i hi => h i (mem_insert_of_mem hi)
    have ih' := ih hs
    by_cases hempty : s = ∅
    · simp [hempty]
    · obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hsum : 2 ≤ ∑ i ∈ s, f i :=
        (hs b hb).trans (single_le_sum (fun i _ => Nat.zero_le (f i)) hb)
      nlinarith

private theorem prime_power_two_le {m p : ℕ} (hp : p ∈ m.primeFactors) :
    2 ≤ p ^ m.factorization p := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpos : 1 ≤ m.factorization p := hprime.factorization_pos_of_dvd
    ((Nat.mem_primeFactors.mp hp).2.2) (Nat.dvd_of_mem_primeFactors hp)
  exact hprime.two_le.trans (by simpa using Nat.pow_le_pow_right hprime.pos hpos)

private theorem prime_power_pairwise (m : ℕ) (s : Finset ℕ) (hs : s ⊆ m.primeFactors) :
    (s : Set ℕ).Pairwise (fun p r => Nat.Coprime (p ^ m.factorization p) (r ^ m.factorization r)) := by
  intro p hp r hr hne
  exact (Nat.pairwise_coprime_pow_primeFactors_factorization (n := m))
    (show (⟨p, hs hp⟩ : m.primeFactors) ≠ ⟨r, hs hr⟩ from
      fun h => hne (congrArg Subtype.val h))

private theorem charge_le {m r : ℕ} (hr : 0 < r) :
    ∑ p ∈ m.primeFactors.filter (fun p => p ^ m.factorization p ∣ r),
      ((p ^ m.factorization p : ℕ) : ℝ) / r ≤ 1 := by
  classical
  let s := m.primeFactors.filter (fun p => p ^ m.factorization p ∣ r)
  have hpair := prime_power_pairwise m s (filter_subset _ _)
  have hdiv : (∏ p ∈ s, p ^ m.factorization p) ∣ r := by
    rw [← Finset.lcm_eq_prod hpair]
    exact lcm_dvd fun p hp => (mem_filter.mp hp).2
  have hsum : ∑ p ∈ s, p ^ m.factorization p ≤ r :=
    (sum_le_prod_two_le s _ fun p hp => prime_power_two_le (mem_filter.mp hp).1).trans
      (Nat.le_of_dvd hr hdiv)
  rw [← sum_div]
  apply (div_le_one (by exact_mod_cast hr)).2
  exact_mod_cast hsum

end D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity

namespace D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity
open Finset

private theorem per_prime_charge {m K p : ℕ} (hm : m ≠ 0) (hp : p ∈ m.primeFactors)
    (c : Fin K → MCongruence m) (hc : SpansTrivial c) :
    (Nat.totient (p ^ m.factorization p) : ℝ) ≤
      ∑ j ∈ (univ.filter fun j => p ^ m.factorization p ∣ (c j).a),
        ((p ^ m.factorization p : ℕ) : ℝ) / (c j).a := by
  classical
  let s := univ.filter fun j => p ^ m.factorization p ∣ (c j).a
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  have hnat := per_prime_count hm hprime hpd c hc
  have hh : (m : ℝ) ≤ ((m / p : ℕ) : ℝ) + ∑ j ∈ s, ((m / (c j).a : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_div_charZero hpd] at hh
  have hsum : (∑ j ∈ s, ((m / (c j).a : ℕ) : ℝ)) =
      ∑ j ∈ s, (m : ℝ) / (c j).a := by
    exact sum_congr rfl fun j _ => Nat.cast_div_charZero (c j).dvd
  rw [hsum] at hh
  have hpφ : (p : ℝ) * Nat.totient (p ^ m.factorization p) =
      ((p ^ m.factorization p : ℕ) : ℝ) * ((p : ℝ) - 1) := by
    have he : 0 < m.factorization p := hprime.factorization_pos_of_dvd hm hpd
    obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
    rw [he, Nat.totient_prime_pow_succ hprime, Nat.cast_mul,
      Nat.cast_sub hprime.one_le, Nat.cast_one, pow_succ, Nat.cast_mul]
    ring
  have hmul := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ ((p ^ m.factorization p : ℕ) : ℝ) / m by positivity)
  have hcancel : (((p ^ m.factorization p : ℕ) : ℝ) / m) * (m : ℝ) =
      ((p ^ m.factorization p : ℕ) : ℝ) := div_mul_cancel₀ _ hmR.ne'
  have hcancelp : (((p ^ m.factorization p : ℕ) : ℝ) / m) * ((m : ℝ) / p) =
      ((p ^ m.factorization p : ℕ) : ℝ) / p := div_mul_div_cancel₀ hmR.ne'
  have hcancelr : (((p ^ m.factorization p : ℕ) : ℝ) / m) *
      (∑ j ∈ s, (m : ℝ) / (c j).a) =
      ∑ j ∈ s, ((p ^ m.factorization p : ℕ) : ℝ) / (c j).a := by
    simp_rw [mul_sum, ← mul_div_assoc, hcancel]
  rw [mul_add, hcancel, hcancelp, hcancelr] at hmul
  have hφ : (Nat.totient (p ^ m.factorization p) : ℝ) =
      ((p ^ m.factorization p : ℕ) : ℝ) - ((p ^ m.factorization p : ℕ) : ℝ) / p := by
    apply (mul_right_cancel₀ hpR.ne')
    field_simp [hmR.ne', hpR.ne']
    nlinarith [hpφ]
  rw [hφ]
  linarith

private theorem counting_lemma {m K : ℕ} (hm : m ≠ 0)
    (c : Fin K → MCongruence m) (hc : SpansTrivial c) :
    ∑ p ∈ m.primeFactors, Nat.totient (p ^ m.factorization p) ≤ K := by
  classical
  have hfirst : (∑ p ∈ m.primeFactors, (Nat.totient (p ^ m.factorization p) : ℝ)) ≤
      ∑ p ∈ m.primeFactors, ∑ j ∈ (univ.filter fun j => p ^ m.factorization p ∣ (c j).a),
        ((p ^ m.factorization p : ℕ) : ℝ) / (c j).a :=
    sum_le_sum fun p hp => per_prime_charge hm hp c hc
  have hswap : (∑ p ∈ m.primeFactors,
      ∑ j ∈ (univ.filter fun j => p ^ m.factorization p ∣ (c j).a),
        ((p ^ m.factorization p : ℕ) : ℝ) / (c j).a) =
      ∑ j : Fin K, ∑ p ∈ m.primeFactors.filter (fun p => p ^ m.factorization p ∣ (c j).a),
        ((p ^ m.factorization p : ℕ) : ℝ) / (c j).a := by
    simp_rw [sum_filter]
    rw [sum_comm]
  rw [hswap] at hfirst
  have hlast : (∑ j : Fin K,
      ∑ p ∈ m.primeFactors.filter (fun p => p ^ m.factorization p ∣ (c j).a),
        ((p ^ m.factorization p : ℕ) : ℝ) / (c j).a) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin K, (1 : ℝ) := by
        apply sum_le_sum
        intro j hj
        exact charge_le (c j).one_le
      _ = _ := by simp
  exact_mod_cast hfirst.trans hlast

private theorem totient_half {m p : ℕ} (hp : p ∈ m.primeFactors) :
    p ^ m.factorization p ≤ 2 * Nat.totient (p ^ m.factorization p) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have he : 0 < m.factorization p := hprime.factorization_pos_of_dvd
    (by exact (Nat.mem_primeFactors.mp hp).2.2) (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  rw [he, Nat.totient_prime_pow_succ hprime, pow_succ]
  have := hprime.two_le
  have hb : p ≤ 2 * (p - 1) := by omega
  calc
    p ^ e * p ≤ p ^ e * (2 * (p - 1)) := Nat.mul_le_mul_left _ hb
    _ = 2 * (p ^ e * (p - 1)) := by ring

private theorem prime_power_sum_le {m K : ℕ} (hm : m ≠ 0)
    (c : Fin K → MCongruence m) (hc : SpansTrivial c) :
    ∑ p ∈ m.primeFactors, p ^ m.factorization p ≤ 2 * K := by
  calc
    _ ≤ ∑ p ∈ m.primeFactors, 2 * Nat.totient (p ^ m.factorization p) :=
      sum_le_sum fun p hp => totient_half hp
    _ = 2 * ∑ p ∈ m.primeFactors, Nat.totient (p ^ m.factorization p) := by rw [mul_sum]
    _ ≤ _ := Nat.mul_le_mul_left _ (counting_lemma hm c hc)

end D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity

namespace D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity
open Finset

private theorem small_log_bound {m : ℕ} (y : ℝ) (hy : 0 ≤ y) :
    ∑ p ∈ m.primeFactors.filter (fun p => ((p ^ m.factorization p : ℕ) : ℝ) ≤ y),
      Real.log (p ^ m.factorization p : ℕ) ≤ 8 * y := by
  classical
  let s := m.primeFactors.filter (fun p => ((p ^ m.factorization p : ℕ) : ℝ) ≤ y)
  have hpair := prime_power_pairwise m s (filter_subset _ _)
  have hdiv : (∏ p ∈ s, p ^ m.factorization p) ∣ Nat.lcmUpto ⌊y⌋₊ := by
    rw [← Finset.lcm_eq_prod hpair]
    apply Finset.lcm_dvd
    intro p hp
    apply dvd_lcm (f := id)
    exact mem_Icc.mpr ⟨(prime_power_two_le (mem_filter.mp hp).1).trans' (by norm_num),
      Nat.le_floor (mem_filter.mp hp).2⟩
  have hprodpos : 0 < ∏ p ∈ s, p ^ m.factorization p := by
    apply prod_pos
    intro p hp
    exact lt_of_lt_of_le (by norm_num) (prime_power_two_le (mem_filter.mp hp).1)
  have hlog : (∑ p ∈ s, Real.log (p ^ m.factorization p : ℕ)) ≤
      Real.log (Nat.lcmUpto ⌊y⌋₊) := by
    rw [← Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (prime_power_two_le (mem_filter.mp hp).1))))]
    rw [← Nat.cast_prod]
    exact Real.log_le_log (by exact_mod_cast hprodpos)
      (by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos _) hdiv)
  have hpsi := Chebyshev.psi_le_const_mul_self (x := y) hy
  rw [Chebyshev.psi_eq_psi_coe_floor y, Chebyshev.psi_eq_log_lcmUpto] at hpsi
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  exact hlog.trans (hpsi.trans (by nlinarith))

private theorem log_prime_power_sum {m : ℕ} (hm : m ≠ 0) :
    Real.log m = ∑ p ∈ m.primeFactors, Real.log (p ^ m.factorization p : ℕ) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm]
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (prime_power_two_le hp)))

private theorem logarithm_bound {m : ℕ} (hm : m ≠ 0) (hx : 64 ≤ Real.log m) :
    Real.log m ^ 2 ≤ 32 *
      (∑ p ∈ m.primeFactors, ((p ^ m.factorization p : ℕ) : ℝ)) * Real.log (Real.log m) := by
  classical
  let x := Real.log m
  let y := x / 16
  let L : ℝ := ∑ p ∈ m.primeFactors, ((p ^ m.factorization p : ℕ) : ℝ)
  have hx0 : 0 < x := by dsimp [x]; linarith
  have hy4 : 4 ≤ y := by dsimp [y, x]; linarith
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hy4
  have hyexp : Real.exp 1 ≤ y := Real.exp_one_lt_three.le.trans (by linarith)
  let s := m.primeFactors.filter (fun p => ((p ^ m.factorization p : ℕ) : ℝ) ≤ y)
  let t := m.primeFactors.filter (fun p => ¬ ((p ^ m.factorization p : ℕ) : ℝ) ≤ y)
  have hsmall : (∑ p ∈ s, Real.log (p ^ m.factorization p : ℕ)) ≤ x / 2 := by
    have h := small_log_bound (m := m) y hy0.le
    dsimp [s, y] at *
    linarith
  have hlarge : (∑ p ∈ t, Real.log (p ^ m.factorization p : ℕ)) ≤
      (Real.log y / y) * L := by
    calc
      _ ≤ ∑ p ∈ t, (Real.log y / y) * ((p ^ m.factorization p : ℕ) : ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpgt : y < ((p ^ m.factorization p : ℕ) : ℝ) := lt_of_not_ge (mem_filter.mp hp).2
        have hmono := Real.log_div_self_antitoneOn hyexp (hyexp.trans hpgt.le) hpgt.le
        exact (div_le_iff₀ (hy0.trans hpgt)).1 hmono
      _ = (Real.log y / y) * ∑ p ∈ t, ((p ^ m.factorization p : ℕ) : ℝ) := by rw [mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left
        · exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
        · exact div_nonneg (Real.log_nonneg (by linarith)) hy0.le
  have hsplit : x = (∑ p ∈ s, Real.log (p ^ m.factorization p : ℕ)) +
      ∑ p ∈ t, Real.log (p ^ m.factorization p : ℕ) := by
    dsimp [s, t]
    rw [sum_filter_add_sum_filter_not]
    exact log_prime_power_sum hm
  have hbound : x / 2 ≤ (Real.log y / y) * L := by linarith
  have hmul := (le_div_iff₀ hy0).1 (show x / 2 ≤ (Real.log y * L) / y by simpa only [div_mul_eq_mul_div] using hbound)
  have hyx : y ≤ x := div_le_self hx0.le (by norm_num : (1 : ℝ) ≤ 16)
  have hlog : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyx
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have : x ^ 2 ≤ 32 * L * Real.log x := by dsimp [y] at hmul; nlinarith
  exact this

end D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity

namespace D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity
open Finset Filter

private theorem spanning_nonempty {m : ℕ} (hm : m ≠ 0) :
    {K : ℕ | ∃ c : Fin K → MCongruence m, SpansTrivial c}.Nonempty := by
  refine ⟨m, ?_⟩
  let c : Fin m → MCongruence m := fun j =>
    { a := m, b := j.val, one_le := Nat.one_le_iff_ne_zero.mpr hm, dvd := dvd_rfl }
  refine ⟨c, ?_⟩
  intro x y hx hy h
  have hj : (c ⟨x, hx⟩).Holds x := Int.ModEq.refl _
  have hh : (y : ℤ) ≡ (x : ℤ) [ZMOD (m : ℤ)] := (h ⟨x, hx⟩).1 hj
  have he : y % m = x % m := Int.natCast_modEq_iff.mp hh
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using he.symm

private theorem ac_prime_power_bound {m : ℕ} (hm : m ≠ 0) :
    ∑ p ∈ m.primeFactors, p ^ m.factorization p ≤ 2 * acTrivial m := by
  have hmem : acTrivial m ∈ {K : ℕ | ∃ c : Fin K → MCongruence m, SpansTrivial c} :=
    csInf_mem (spanning_nonempty hm)
  obtain ⟨c, hc⟩ := hmem
  exact prime_power_sum_le hm c hc

private theorem ratio_bound_of_log {m : ℕ} (hm : 64 ≤ Real.log m) :
    (1 / 64 : ℝ) ≤ (acTrivial m : ℝ) / (Real.log m ^ 2 / Real.log (Real.log m)) := by
  have hm0 : m ≠ 0 := by
    intro hz
    norm_num [hz] at hm
  have hlog0 : 0 < Real.log m := by linarith
  have hloglog : 0 < Real.log (Real.log m) := Real.log_pos (by linarith)
  have hpow0 : 0 < Real.log m ^ 2 := sq_pos_of_pos hlog0
  have hden : 0 < Real.log m ^ 2 / Real.log (Real.log m) := div_pos hpow0 hloglog
  have hL := ac_prime_power_bound hm0
  have hLR : (∑ p ∈ m.primeFactors, ((p ^ m.factorization p : ℕ) : ℝ)) ≤
      2 * (acTrivial m : ℝ) := by exact_mod_cast hL
  have hmain := logarithm_bound hm0 hm
  have hlow : Real.log m ^ 2 ≤ 64 * (acTrivial m : ℝ) * Real.log (Real.log m) := by
    nlinarith
  apply (le_div_iff₀ hden).2
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hloglog).2
  nlinarith

private theorem eventual_ratio_bound :
    ∀ᶠ m : ℕ in atTop,
      (1 / 64 : ℝ) ≤ (acTrivial m : ℝ) / (Real.log m ^ 2 / Real.log (Real.log m)) := by
  apply Filter.eventually_atTop.mpr
  refine ⟨⌈Real.exp 64⌉₊, fun m hm => ?_⟩
  have hmc : Real.exp 64 ≤ (m : ℝ) :=
    (Nat.le_ceil (Real.exp 64)).trans (by exact_mod_cast hm)
  have hmpos : (0 : ℝ) < m := (Real.exp_pos 64).trans_le hmc
  exact ratio_bound_of_log ((Real.le_log_iff_exp_le hmpos).2 hmc)

theorem result : D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity.claim := by
  have he : ∀ᶠ m : ℕ in atTop,
      ((1 / 64 : ℝ) : EReal) ≤
        (((acTrivial m : ℝ) / (Real.log m ^ 2 / Real.log (Real.log m)) : ℝ) : EReal) := by
    filter_upwards [eventual_ratio_bound] with m hm
    exact_mod_cast hm
  have hlim := Filter.le_liminf_of_le (by isBoundedDefault) he
  have hpos : (0 : EReal) < ((1 / 64 : ℝ) : EReal) := by norm_num
  exact hpos.trans_le hlim

end D5.S3.Arith.Congruence.BorsPanarioWangArithmeticComplexity
