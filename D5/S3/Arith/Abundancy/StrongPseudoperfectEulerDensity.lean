/- GID: D5/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/StrongPseudoperfectEulerDensity
   mirror-E: none(waiver:analytic-estimate)
   anchors: [mathlib/module/Mathlib.Data.Nat.Squarefree]
   utility: none
   digest: Strong pseudoperfection has zero relative density among Euler forms. -/

import D5.S3.Arith.Abundancy.StrongPseudoperfectDensity
import D5.S3.PrimeGaps.ModFourChebyshev
import Mathlib.Data.Nat.Squarefree

/-!
Admission basis: open-problem-resolution; utility: none.
The source is McCormack--Zelinsky Question 44.
The Euler predicate permits even square factors and every positive exponent congruent to one.

Direct frozen dependencies:
* StrongPseudoperfectDensity.StronglyPseudoperfect
* StrongPseudoperfectDensity.prime_mem_codes
* ModFourChebyshev.prime_count_lower

Declaration proof shapes and live consumers:
* prime_le_sigma: bind-only; eulerSP_subset.
* squarefree_mul_sq_dvd: bind-only; sigma_square_le_double.
* sigma_square_le_double: bind-only; sigma_square_sum_nat.
* sum_Icc_id_le_sq: bind-only; sigma_square_sum_nat.
* sigma_square_sum_nat: bind-only; sigma_square_sum.
* reciprocal_square_sum_le_two: bind-only; sigma_square_sum, highPowers_card.
* sigma_square_sum: bind-only; smallSquares_card.
* smallSquares_card: bind-only; eulerSP_envelope.
* largeSquares_card: bind-only; eulerSP_envelope.
* highPowers_card: bind-only; eulerSP_envelope.
* eulerSP_subset: bind-only; eulerSP_envelope.
* eulerSP_envelope: bind-only; eulerSP_bound.
* eulerSP_bound: bind-only; result.
* eulerCount_pos: bind-only; result.
* primeCount_le_eulerCount: bind-only; result.
* result: bind-only; the named external open-problem resolution.
Definitions are the source predicate, its two counts and finite parameter sets used above.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity

open StrongPseudoperfectDensity
attribute [local instance] Classical.propDecidable

/-- Euler's form, with exactly the positivity and congruence conditions in the source. -/
def EulerForm (n : ℕ) : Prop :=
  ∃ q s m : ℕ, q.Prime ∧ q % 4 = 1 ∧ s % 4 = 1 ∧ 0 < m ∧
    Nat.Coprime q m ∧ n = q ^ s * m ^ 2

/-- The positive Euler-form integers up to the threshold. -/
def eulerCount (X : ℕ) : ℕ :=
  ((Icc 1 X).filter EulerForm).card

/-- Those Euler-form integers that are strongly pseudoperfect. -/
def eulerSPCount (X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun n => EulerForm n ∧ StronglyPseudoperfect n)).card

private lemma prime_le_sigma {m q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m)
    (hsp : StronglyPseudoperfect (q * m)) : q ≤ ArithmeticFunction.sigma 1 m := by
  have hc := prime_mem_codes hq hqm (by simpa [mul_comm] using hsp)
  obtain ⟨U, hU, heq⟩ := mem_image.mp hc
  rw [mem_powerset] at hU
  calc
    q = (∑ d ∈ U, d) / (2 * m - ∑ d ∈ U, m / d) := heq.symm
    _ ≤ ∑ d ∈ U, d := Nat.div_le_self _ _
    _ ≤ ∑ d ∈ m.divisors, d := sum_le_sum_of_subset hU
    _ = _ := (ArithmeticFunction.sigma_one_apply m).symm

private lemma squarefree_mul_sq_dvd {a b m : ℕ} (ha : Squarefree a) :
    a * b ^ 2 ∣ m ^ 2 ↔ a * b ∣ m := by
  constructor
  · intro hd
    have hb : b ^ 2 ∣ m ^ 2 := dvd_trans (dvd_mul_left _ _) hd
    have hbm : b ∣ m := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hb
    obtain ⟨k, rfl⟩ := hbm
    by_cases hb0 : b = 0
    · simp_all
    have hak : a ∣ k ^ 2 := by
      apply (Nat.mul_dvd_mul_iff_left (by positivity : 0 < b ^ 2)).mp
      simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hd
    have hak' : a ∣ k := (ha.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hak
    simpa [mul_comm] using Nat.mul_dvd_mul_left b hak'
  · intro hd
    have hsq := pow_dvd_pow_of_dvd hd 2
    exact dvd_trans ⟨a, by ring⟩ hsq

private lemma sigma_square_le_double (m T : ℕ) (hm : 0 < m) (hmT : m ≤ T) :
    ArithmeticFunction.sigma 1 (m ^ 2) ≤
      ∑ a ∈ Icc 1 T, ∑ b ∈ Icc 1 (T / a),
        if a * b ∣ m then a * b ^ 2 else 0 := by
  classical
  choose b a hab hsf using (fun d : ℕ => exists_sq_mul_squarefree d)
  let f (d : ℕ) : (Σ _ : ℕ, ℕ) := ⟨a d, b d⟩
  let K := (Icc 1 T).sigma (fun a => Icc 1 (T / a))
  have hdvd (d : ℕ) (hd : d ∈ (m ^ 2).divisors) : a d * b d ∣ m := by
    apply (squarefree_mul_sq_dvd (hsf d)).mp
    rw [mul_comm (a d), hab d]
    exact Nat.dvd_of_mem_divisors hd
  have hpos (d : ℕ) (hd : d ∈ (m ^ 2).divisors) : 0 < a d ∧ 0 < b d := by
    refine ⟨Nat.pos_of_ne_zero (hsf d).ne_zero, ?_⟩
    have hd0 := Nat.pos_of_mem_divisors hd
    have he := hab d
    by_contra! hb
    have : b d = 0 := by omega
    simp [this] at he
    omega
  have hinj : Set.InjOn f ↑((m ^ 2).divisors) := by
    intro d hd e he h
    have ha : a d = a e := congrArg Sigma.fst h
    have hb : b d = b e := congrArg Sigma.snd h
    rw [← hab d, ← hab e, ha, hb]
  have hmem : ((m ^ 2).divisors.image f) ⊆ K := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hz
    have hmul : a d * b d ≤ T := (Nat.le_of_dvd hm (hdvd d hd)).trans hmT
    obtain ⟨ha, hb⟩ := hpos d hd
    apply mem_sigma.mpr
    refine ⟨mem_Icc.mpr ⟨ha, ?_⟩, mem_Icc.mpr ⟨hb, ?_⟩⟩
    · nlinarith
    · change b d ≤ T / a d
      exact (Nat.le_div_iff_mul_le ha).mpr (by simpa [mul_comm] using hmul)
  rw [ArithmeticFunction.sigma_one_apply]
  let g : (Σ _ : ℕ, ℕ) → ℕ :=
    fun z => if z.1 * z.2 ∣ m then z.1 * z.2 ^ 2 else 0
  have hsum := sum_sigma (Icc 1 T) (fun a => Icc 1 (T / a)) g
  change (∑ d ∈ (m ^ 2).divisors, d) ≤
    ∑ a ∈ Icc 1 T, ∑ b ∈ Icc 1 (T / a), g ⟨a, b⟩
  rw [← hsum]
  apply sum_le_sum_of_injOn f hinj hmem
  · intro d hd
    change d ≤ if a d * b d ∣ m then a d * b d ^ 2 else 0
    rw [if_pos (hdvd d hd)]
    exact le_of_eq (by simpa only [mul_comm (b d ^ 2)] using (hab d).symm)
  · intro z hz _
    exact Nat.zero_le _

private lemma sum_Icc_id_le_sq (L : ℕ) : (∑ b ∈ Icc 1 L, b) ≤ L ^ 2 := by
  calc
    _ ≤ ∑ _b ∈ Icc 1 L, L := sum_le_sum fun b hb => (mem_Icc.mp hb).2
    _ = _ := by simp [pow_two]

private lemma sigma_square_sum_nat (T : ℕ) :
    (∑ m ∈ Icc 1 T, ArithmeticFunction.sigma 1 (m ^ 2)) ≤
      ∑ a ∈ Icc 1 T, T * (T / a) ^ 2 := by
  calc
    _ ≤ ∑ m ∈ Icc 1 T, ∑ a ∈ Icc 1 T, ∑ b ∈ Icc 1 (T / a),
        if a * b ∣ m then a * b ^ 2 else 0 := by
      apply sum_le_sum
      intro m hm
      exact sigma_square_le_double m T (mem_Icc.mp hm).1 (mem_Icc.mp hm).2
    _ = ∑ a ∈ Icc 1 T, ∑ b ∈ Icc 1 (T / a),
        a * b ^ 2 * (T / (a * b)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      rw [← sum_filter]
      simp only [sum_const, smul_eq_mul]
      have hc : ((Icc 1 T).filter (fun m => a * b ∣ m)).card = T / (a * b) :=
        Nat.Ioc_filter_dvd_card_eq_div T (a * b)
      rw [hc, mul_comm]
    _ ≤ ∑ a ∈ Icc 1 T, ∑ b ∈ Icc 1 (T / a), T * b := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      calc
        _ = b * ((a * b) * (T / (a * b))) := by ring
        _ ≤ b * T := Nat.mul_le_mul_left b (Nat.mul_div_le T (a * b))
        _ = _ := mul_comm _ _
    _ ≤ ∑ a ∈ Icc 1 T, T * (T / a) ^ 2 := by
      apply sum_le_sum
      intro a ha
      rw [← mul_sum]
      exact Nat.mul_le_mul_left T (sum_Icc_id_le_sq (T / a))

private lemma reciprocal_square_sum_le_two (T : ℕ) :
    (∑ a ∈ Icc 1 T, 1 / (a : ℝ) ^ 2) ≤ 2 := by
  have hI : Icc 1 T = Ioo 0 (T + 1) := by
    ext a
    simp only [mem_Icc, mem_Ioo]
    omega
  simpa only [hI, one_div, Nat.cast_zero, zero_add, div_one] using
    (sum_Ioo_inv_sq_le (α := ℝ) 0 (T + 1))

private lemma sigma_square_sum (T : ℕ) :
    (∑ m ∈ Icc 1 T, (ArithmeticFunction.sigma 1 (m ^ 2) : ℝ)) ≤
      3 * (T : ℝ) ^ 3 := by
  have hn := sigma_square_sum_nat T
  calc
    _ ≤ ∑ a ∈ Icc 1 T, (T : ℝ) * ((T / a : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hn
    _ ≤ ∑ a ∈ Icc 1 T, (T : ℝ) ^ 3 * (1 / (a : ℝ) ^ 2) := by
      apply sum_le_sum
      intro a ha
      have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by have := (mem_Icc.mp ha).1; omega)
      calc
        _ ≤ (T : ℝ) * ((T : ℝ) / a) ^ 2 := by
          gcongr
          exact Nat.cast_div_le
        _ = _ := by field_simp
    _ = (T : ℝ) ^ 3 * (∑ a ∈ Icc 1 T, 1 / (a : ℝ) ^ 2) := by rw [mul_sum]
    _ ≤ (T : ℝ) ^ 3 * 2 :=
      mul_le_mul_of_nonneg_left (reciprocal_square_sum_le_two T) (by positivity)
    _ ≤ _ := by nlinarith [pow_nonneg (Nat.cast_nonneg T : (0 : ℝ) ≤ T) 3]

private def smallSquares (T : ℕ) : Finset ℕ :=
  (Icc 1 T).biUnion fun m =>
    (Icc 1 (ArithmeticFunction.sigma 1 (m ^ 2))).image (fun q => q * m ^ 2)

private def largeSquares (X T : ℕ) : Finset ℕ :=
  (Icc (T + 1) X).biUnion fun m =>
    (Icc 1 (X / m ^ 2)).image (fun q => q * m ^ 2)

private def highPowers (X : ℕ) : Finset ℕ :=
  (Icc 2 X).biUnion fun q =>
    (Icc 1 (Nat.sqrt X / q ^ 2)).image (fun a => q ^ 5 * a ^ 2)

private lemma smallSquares_card (T : ℕ) :
    ((smallSquares T).card : ℝ) ≤ 3 * (T : ℝ) ^ 3 := by
  have h : (smallSquares T).card ≤
      ∑ m ∈ Icc 1 T, ArithmeticFunction.sigma 1 (m ^ 2) := by
    apply (card_biUnion_le).trans
    apply sum_le_sum
    intro m hm
    exact (card_image_le).trans_eq (by simp)
  have hR : ((smallSquares T).card : ℝ) ≤
      ∑ m ∈ Icc 1 T, (ArithmeticFunction.sigma 1 (m ^ 2) : ℝ) := by
    exact_mod_cast h
  exact hR.trans (sigma_square_sum T)

private lemma largeSquares_card (X T : ℕ) :
    ((largeSquares X T).card : ℝ) ≤ 2 * (X : ℝ) / (T + 1) := by
  have h : (largeSquares X T).card ≤
      ∑ m ∈ Icc (T + 1) X, X / m ^ 2 := by
    apply (card_biUnion_le).trans
    apply sum_le_sum
    intro m hm
    exact (card_image_le).trans_eq (by simp)
  calc
    _ ≤ ∑ m ∈ Icc (T + 1) X, ((X / m ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ ∑ m ∈ Icc (T + 1) X, (X : ℝ) * (1 / (m : ℝ) ^ 2) := by
      apply sum_le_sum
      intro m hm
      simpa [Nat.cast_pow, div_eq_mul_inv, one_div] using
        (Nat.cast_div_le (m := X) (n := m ^ 2) :
          ((X / m ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) / (m ^ 2 : ℕ))
    _ = (X : ℝ) * (∑ m ∈ Icc (T + 1) X, 1 / (m : ℝ) ^ 2) := by rw [mul_sum]
    _ ≤ (X : ℝ) * (2 / ((T : ℝ) + 1)) := by
      have hI : Icc (T + 1) X = Ioo T (X + 1) := by
        ext m
        simp only [mem_Icc, mem_Ioo]
        omega
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [hI, one_div] using (sum_Ioo_inv_sq_le (α := ℝ) T (X + 1))
    _ = _ := by ring

private lemma highPowers_card (X : ℕ) :
    ((highPowers X).card : ℝ) ≤ (Nat.sqrt X : ℝ) := by
  have h : (highPowers X).card ≤ ∑ q ∈ Icc 2 X, Nat.sqrt X / q ^ 2 := by
    apply (card_biUnion_le).trans
    apply sum_le_sum
    intro q hq
    exact (card_image_le).trans_eq (by simp)
  have hsum : (∑ q ∈ Icc 2 X, 1 / (q : ℝ) ^ 2) ≤ 1 := by
    by_cases hX : 1 ≤ X
    · have ht := reciprocal_square_sum_le_two X
      rw [← add_sum_Ioc_eq_sum_Icc hX] at ht
      simp only [Nat.cast_one, one_pow, div_one] at ht
      change (1 : ℝ) + ∑ q ∈ Icc 2 X, 1 / (q : ℝ) ^ 2 ≤ 2 at ht
      linarith
    · have hX0 : X = 0 := by omega
      simp [hX0]
  calc
    _ ≤ ∑ q ∈ Icc 2 X, ((Nat.sqrt X / q ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ ∑ q ∈ Icc 2 X, (Nat.sqrt X : ℝ) * (1 / (q : ℝ) ^ 2) := by
      apply sum_le_sum
      intro q hq
      simpa [Nat.cast_pow, div_eq_mul_inv, one_div] using
        (Nat.cast_div_le (m := Nat.sqrt X) (n := q ^ 2) :
          ((Nat.sqrt X / q ^ 2 : ℕ) : ℝ) ≤ (Nat.sqrt X : ℝ) / (q ^ 2 : ℕ))
    _ = (Nat.sqrt X : ℝ) * (∑ q ∈ Icc 2 X, 1 / (q : ℝ) ^ 2) := by rw [mul_sum]
    _ ≤ (Nat.sqrt X : ℝ) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := mul_one _

private lemma eulerSP_subset (X T : ℕ) :
    (Icc 1 X).filter (fun n => EulerForm n ∧ StronglyPseudoperfect n) ⊆
      smallSquares T ∪ largeSquares X T ∪ highPowers X := by
  intro n hn
  obtain ⟨hnI, ⟨q, s, m, hq, hq4, hs4, hm, hcop, rfl⟩, hsp⟩ := mem_filter.mp hn
  have hs : 0 < s := by omega
  have hqpow : q ≤ q ^ s := Nat.le_self_pow hs.ne' q
  have hm2 : 1 ≤ m ^ 2 := by have := pow_pos hm 2; omega
  have hq0 : 0 < q := hq.pos
  have hqX : q ≤ X := by
    have hnX := (mem_Icc.mp hnI).2
    nlinarith
  have hmX : m ≤ X := by
    have hnX := (mem_Icc.mp hnI).2
    have hmm := Nat.le_self_pow (by decide : 2 ≠ 0) m
    nlinarith [hq.pos]
  by_cases hs1 : s = 1
  · subst s
    simp only [pow_one] at hnI hsp
    have hqm : ¬ q ∣ m ^ 2 := hq.coprime_iff_not_dvd.mp (hcop.pow_right 2)
    have hsig := prime_le_sigma hq hqm hsp
    apply mem_union_left
    by_cases hmT : m ≤ T
    · apply mem_union_left
      apply mem_biUnion.mpr
      refine ⟨m, mem_Icc.mpr ⟨hm, hmT⟩, mem_image.mpr ?_⟩
      exact ⟨q, mem_Icc.mpr ⟨hq.pos, hsig⟩, by simp⟩
    · apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨m, mem_Icc.mpr ⟨by omega, hmX⟩, mem_image.mpr ?_⟩
      refine ⟨q, mem_Icc.mpr ⟨hq.pos, ?_⟩, by simp⟩
      exact (Nat.le_div_iff_mul_le (by positivity : 0 < m ^ 2)).mpr
        (mem_Icc.mp hnI).2
  · have hs5 : 5 ≤ s := by omega
    let j := (s - 5) / 4
    have hsrepr : s = 5 + 4 * j := by dsimp [j]; omega
    let a := q ^ (2 * j) * m
    have ha : 0 < a := by dsimp [a]; positivity
    have heq : q ^ s * m ^ 2 = q ^ 5 * a ^ 2 := by
      rw [hsrepr]
      dsimp [a]
      rw [pow_add, mul_pow, ← pow_mul,
        show 2 * j * 2 = 4 * j by omega]
      ring
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨q, mem_Icc.mpr ⟨hq.two_le, hqX⟩, mem_image.mpr ?_⟩
    refine ⟨a, mem_Icc.mpr ⟨ha, ?_⟩, heq.symm⟩
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ 2)).mpr
    apply Nat.le_sqrt'.mpr
    calc
      (a * q ^ 2) ^ 2 = q ^ 4 * a ^ 2 := by ring
      _ ≤ q ^ 5 * a ^ 2 := by
        exact Nat.mul_le_mul_right (a ^ 2)
          (Nat.pow_le_pow_right hq.pos (by decide : 4 ≤ 5))
      _ ≤ X := by simpa only [heq] using (mem_Icc.mp hnI).2

private lemma eulerSP_envelope (X T : ℕ) :
    (eulerSPCount X : ℝ) ≤
      3 * (T : ℝ) ^ 3 + 2 * (X : ℝ) / (T + 1) + Nat.sqrt X := by
  have hc := (card_le_card (eulerSP_subset X T)).trans
    (card_union_le (smallSquares T ∪ largeSquares X T) (highPowers X))
  have hc' : eulerSPCount X ≤
      (smallSquares T).card + (largeSquares X T).card + (highPowers X).card := by
    exact hc.trans (Nat.add_le_add_right
      (card_union_le (smallSquares T) (largeSquares X T)) _)
  have hR : (eulerSPCount X : ℝ) ≤
      ((smallSquares T).card : ℝ) + (largeSquares X T).card + (highPowers X).card := by
    exact_mod_cast hc'
  linarith [smallSquares_card T, largeSquares_card X T, highPowers_card X]

private lemma eulerSP_bound (X : ℕ) (hX : 16 ≤ X) :
    (eulerSPCount X : ℝ) ≤ 6 * (X : ℝ) ^ (3 / 4 : ℝ) := by
  let x : ℝ := X
  let u : ℝ := x ^ (1 / 4 : ℝ)
  let T : ℕ := ⌊u⌋₊
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < X by omega)
  have hu : 0 < u := Real.rpow_pos_of_pos hx _
  have hTu : (T : ℝ) ≤ u := Nat.floor_le hu.le
  have huT : u < (T : ℝ) + 1 := Nat.lt_floor_add_one u
  have hpow : u ^ 3 = x ^ (3 / 4 : ℝ) := by
    dsimp only [u]
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  have hdiv : x / u = x ^ (3 / 4 : ℝ) := by
    dsimp only [u]
    calc
      x / x ^ (1 / 4 : ℝ) = x ^ (1 : ℝ) / x ^ (1 / 4 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (3 / 4 : ℝ) := by rw [← Real.rpow_sub hx]; norm_num
  have hsmall : 3 * (T : ℝ) ^ 3 ≤ 3 * x ^ (3 / 4 : ℝ) := by
    rw [← hpow]
    gcongr
  have hlarge : 2 * x / (T + 1) ≤ 2 * x ^ (3 / 4 : ℝ) := by
    rw [← hdiv, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hx.le hu (huT.le)) (by norm_num)
  have hhigh : (Nat.sqrt X : ℝ) ≤ x ^ (3 / 4 : ℝ) := by
    apply Real.nat_sqrt_le_real_sqrt.trans
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ X))
      (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)
  have hen := eulerSP_envelope X T
  change (eulerSPCount X : ℝ) ≤ 3 * (T : ℝ) ^ 3 + 2 * x / (T + 1) + Nat.sqrt X at hen
  linarith

private lemma eulerCount_pos (X : ℕ) (hX : 5 ≤ X) : 0 < eulerCount X := by
  apply card_pos.mpr
  refine ⟨5, mem_filter.mpr ⟨mem_Icc.mpr ⟨by norm_num, hX⟩, ?_⟩⟩
  exact ⟨5, 1, 1, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num⟩

private lemma primeCount_le_eulerCount (X : ℕ) :
    D5.S3.PrimeGaps.ModFourChebyshev.primeCount X ≤ eulerCount X := by
  unfold D5.S3.PrimeGaps.ModFourChebyshev.primeCount eulerCount
  rw [Nat.floor_natCast]
  apply card_le_card
  intro p hp
  obtain ⟨hpI, hpPrime, hpMod⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨hpI, p, 1, 1, hpPrime, hpMod, by norm_num, by norm_num,
    by simp, by simp⟩

/-- Being strongly pseudoperfect is a strong restriction on Euler-form integers. -/
theorem result :
    Tendsto (fun X : ℕ => (eulerSPCount X : ℝ) / eulerCount X) atTop (𝓝 0) := by
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun X : ℕ =>
      6 * exp 50 * (log (X : ℝ) / (X : ℝ) ^ (1 / 4 : ℝ))) atTop (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => log x / x ^ (1 / 4 : ℝ))
        atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
    simpa using (ht.comp hnat).const_mul (6 * exp 50)
  apply squeeze_zero' (Eventually.of_forall (fun X => by positivity)) ?_ hlim
  filter_upwards [eventually_ge_atTop (16 : ℕ), hnat.eventually_ge_atTop (exp 50)] with X hX hexp
  have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hx1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < log (X : ℝ) := log_pos hx1
  have hcount : (0 : ℝ) < eulerCount X := by exact_mod_cast eulerCount_pos X (by omega)
  have hlow : exp (-50) * (X : ℝ) / log X ≤ (eulerCount X : ℝ) :=
    (D5.S3.PrimeGaps.ModFourChebyshev.prime_count_lower hexp).trans
      (by exact_mod_cast primeCount_le_eulerCount X)
  have hlop : 0 < exp (-50) * (X : ℝ) / log X := by positivity
  calc
    _ ≤ (6 * (X : ℝ) ^ (3 / 4 : ℝ)) / eulerCount X :=
      div_le_div_of_nonneg_right (eulerSP_bound X hX) hcount.le
    _ ≤ (6 * (X : ℝ) ^ (3 / 4 : ℝ)) /
        (exp (-50) * (X : ℝ) / log X) :=
      div_le_div_of_nonneg_left (by positivity) hlop hlow
    _ = _ := by
      have hpow : (X : ℝ) ^ (3 / 4 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) = X := by
        rw [← Real.rpow_add hx]
        norm_num
      have he : exp (-50 : ℝ) * exp 50 = 1 := by rw [← exp_add]; norm_num
      have hu : (X : ℝ) ^ (1 / 4 : ℝ) ≠ 0 := (rpow_pos_of_pos hx _).ne'
      field_simp [hlog.ne', (exp_pos (-50 : ℝ)).ne', hx.ne', hu]
      nlinarith [hpow, he]

end D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
