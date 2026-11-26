/- GID: D5/S3/Arith/Abundancy/WeightedTotientEulerDensity
   generality: G
   mirror-B: D5/B/S3/Arith/Abundancy/WeightedTotientEulerDensity
   mirror-E: none(waiver:analytic-estimate)
   anchors: [mathlib/module/Mathlib.Data.Nat.Totient]
   utility: none
   digest: The weighted totient condition D1 is strong among Euler forms. -/

import D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
import Mathlib.Data.Nat.Totient

/-!
Admission basis: open-problem-resolution, McCormack--Zelinsky Question 45.
Direct dependencies:
* StrongPseudoperfectDensity.divisor_split.
* StrongPseudoperfectEulerDensity.EulerForm, eulerCount, smallSquares, largeSquares,
  highPowers, smallSquares_card, largeSquares_card, highPowers_card, eulerCount_pos,
  primeCount_le_eulerCount.
* ModFourChebyshev.prime_count_lower, through the directly imported counting module.
The independent pseudoperfect requirement is retained. Counts exclude zero.

Declaration proof shapes and live consumers:
* weightA_nonneg: bind-only; prime_le_sigma.
* prime_le_sigma: bind-only; eulerD1_subset.
* eulerD1_subset: bind-only; eulerD1_envelope.
* eulerD1_envelope: bind-only; eulerD1_bound.
* eulerD1_bound: bind-only; result.
* result: bind-only; the named external open-problem resolution, preregistered in #31746.
Definitions are consumed by these statements and the final relative count.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology

namespace D5.S3.Arith.Abundancy.WeightedTotientEulerDensity

open StrongPseudoperfectEulerDensity
attribute [local instance] Classical.propDecidable

/-- A subset of the proper divisors with sum equal to the integer. -/
def Pseudoperfect (n : ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ n.properDivisors ∧ ∑ d ∈ T, d = n

/-- The weighted logarithmic totient mean in equation (12). -/
def weightA (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ d ∈ S, ((d : ℝ) / (2 * n)) * log (Nat.totient d)

/-- The logarithm of the complementary totient sum in equation (14). -/
def weightC (S : Finset ℕ) (n : ℕ) : ℝ :=
  log (∑ d ∈ S, (Nat.totient (n / d) : ℝ) / (2 * d))

/-- The source's D1 condition, including its independent pseudoperfect clause. -/
def D1 (n : ℕ) : Prop :=
  Pseudoperfect n ∧ ∃ S : Finset ℕ, S ⊆ n.divisors ∧
    ∑ d ∈ S, d = 2 * n ∧ weightA S n ≤ weightC S n

/-- Positive Euler-form integers satisfying D1, counted without multiplicity. -/
def eulerD1Count (X : ℕ) : ℕ :=
  ((Icc 1 X).filter (fun n => EulerForm n ∧ D1 n)).card

private lemma weightA_nonneg {S : Finset ℕ} {n : ℕ} (hS : S ⊆ n.divisors) :
    0 ≤ weightA S n := by
  apply sum_nonneg
  intro d hd
  apply mul_nonneg (by positivity)
  apply log_nonneg
  exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_mem_divisors (hS hd))

private lemma prime_le_sigma {q r : ℕ} (hq : q.Prime) (hr : 0 < r)
    (hD : D1 (q * r)) : q ≤ ArithmeticFunction.sigma 1 r := by
  by_contra! hlt
  obtain ⟨_, S, hS, hsum, hAC⟩ := hD
  have hqpos : 0 < q := hq.pos
  have hqr : 0 < q * r := Nat.mul_pos hqpos hr
  have hrsig : r ≤ ArithmeticFunction.sigma 1 r := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact single_le_sum (fun d _ => Nat.zero_le d) (Nat.mem_divisors_self r hr.ne')
  have hrq : r < q := hrsig.trans_lt hlt
  let U := S.filter (fun d => ¬ q ∣ d)
  have hU : U ⊆ r.divisors := by
    intro d hd
    obtain ⟨hdS, hqd⟩ := mem_filter.mp hd
    have hdD : d ∈ (r * q).divisors := by simpa [mul_comm] using hS hdS
    rcases StrongPseudoperfectDensity.divisor_split hq hdD with hdR | ⟨e, _, he⟩
    · exact hdR
    · exact (hqd (by rw [he]; exact dvd_mul_left q e)).elim
  have hu : (∑ d ∈ U, d) < q := by
    apply lt_of_le_of_lt _ hlt
    rw [ArithmeticFunction.sigma_one_apply]
    exact sum_le_sum_of_subset hU
  have hqu : q ∣ ∑ d ∈ U, d := by
    have hv : q ∣ ∑ d ∈ S.filter (fun d => q ∣ d), d := by
      exact dvd_sum (fun d hd => (mem_filter.mp hd).2)
    have htotal : q ∣ (∑ d ∈ S.filter (fun d => q ∣ d), d) + ∑ d ∈ U, d := by
      rw [show (∑ d ∈ S.filter (fun d => q ∣ d), d) + ∑ d ∈ U, d =
          ∑ d ∈ S, d from sum_filter_add_sum_filter_not S (fun d => q ∣ d) id]
      rw [hsum]
      exact dvd_mul_of_dvd_right (dvd_mul_right q r) 2
    exact (Nat.dvd_add_iff_right hv).mpr htotal
  have hu0 : ∑ d ∈ U, d = 0 := Nat.eq_zero_of_dvd_of_lt hqu hu
  have hall : ∀ d ∈ S, q ∣ d := by
    intro d hd
    by_contra hqd
    have hdU : d ∈ U := mem_filter.mpr ⟨hd, hqd⟩
    have hdz : d ≤ ∑ e ∈ U, e := single_le_sum (fun e _ => Nat.zero_le e) hdU
    have hdp := Nat.pos_of_mem_divisors (hS hd)
    omega
  let T := r.divisors.filter (fun e => q * e ∈ S)
  have hT : T ⊆ r.divisors := filter_subset _ _
  have hST : T.image (fun e => q * e) = S := by
    ext d
    constructor
    · rintro hd
      obtain ⟨e, he, rfl⟩ := mem_image.mp hd
      exact (mem_filter.mp he).2
    · intro hd
      obtain ⟨e, he⟩ := hall d hd
      have heR : e ∈ r.divisors := by
        apply Nat.mem_divisors.mpr
        refine ⟨?_, hr.ne'⟩
        apply (Nat.mul_dvd_mul_iff_left hq.pos).mp
        simpa only [he] using Nat.dvd_of_mem_divisors (hS hd)
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨heR, by simpa [he] using hd⟩,
        he.symm⟩
  have hSne : S.Nonempty := by
    by_contra hempty
    have : S = ∅ := not_nonempty_iff_eq_empty.mp hempty
    simp [this] at hsum
    omega
  have hZpos : 0 < ∑ d ∈ S, (Nat.totient (q * r / d) : ℝ) / (2 * d) := by
    apply sum_pos
    · intro d hd
      have hdD := hS hd
      have hdiv : 0 < q * r / d :=
        Nat.div_pos (Nat.le_of_dvd hqr (Nat.dvd_of_mem_divisors hdD))
          (Nat.pos_of_mem_divisors hdD)
      have ht := Nat.totient_pos.mpr hdiv
      have hdpos := Nat.pos_of_mem_divisors hdD
      positivity
    · exact hSne
  have hZbound : (∑ d ∈ S, (Nat.totient (q * r / d) : ℝ) / (2 * d)) ≤
      (r : ℝ) / (2 * q) := by
    rw [← hST, sum_image]
    · calc
        _ = ∑ e ∈ T, (Nat.totient (r / e) : ℝ) / (2 * (q * e)) := by
          apply sum_congr rfl
          intro e he
          rw [Nat.mul_div_mul_left _ _ hq.pos, Nat.cast_mul]
        _ ≤ ∑ e ∈ T, (Nat.totient (r / e) : ℝ) / (2 * q) := by
          apply sum_le_sum
          intro e he
          have hep := Nat.pos_of_mem_divisors (hT he)
          have he1 : (1 : ℝ) ≤ e := by exact_mod_cast hep
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith [hq.pos]
        _ ≤ ∑ e ∈ r.divisors, (Nat.totient (r / e) : ℝ) / (2 * q) := by
          apply sum_le_sum_of_subset_of_nonneg hT
          intros
          positivity
        _ = (r : ℝ) / (2 * q) := by
          rw [← sum_div]
          congr 1
          exact_mod_cast (Nat.sum_div_divisors r Nat.totient).trans (Nat.sum_totient r)
    · intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hq.pos hab
  have hZlt : (∑ d ∈ S, (Nat.totient (q * r / d) : ℝ) / (2 * d)) < 1 := by
    apply hZbound.trans_lt
    apply (div_lt_one (by positivity : (0 : ℝ) < 2 * q)).mpr
    exact_mod_cast (by omega : r < 2 * q)
  have hC : weightC S (q * r) < 0 := log_neg hZpos hZlt
  have hA := weightA_nonneg hS
  linarith

private lemma eulerD1_subset (X T : ℕ) :
    (Icc 1 X).filter (fun n => EulerForm n ∧ D1 n) ⊆
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
    have hsig := prime_le_sigma hq (by positivity : 0 < m ^ 2) hsp
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

private lemma eulerD1_envelope (X T : ℕ) :
    (eulerD1Count X : ℝ) ≤
      3 * (T : ℝ) ^ 3 + 2 * (X : ℝ) / (T + 1) + Nat.sqrt X := by
  have hc := (card_le_card (eulerD1_subset X T)).trans
    (card_union_le (smallSquares T ∪ largeSquares X T) (highPowers X))
  have hc' : eulerD1Count X ≤
      (smallSquares T).card + (largeSquares X T).card + (highPowers X).card := by
    exact hc.trans (Nat.add_le_add_right
      (card_union_le (smallSquares T) (largeSquares X T)) _)
  have hR : (eulerD1Count X : ℝ) ≤
      ((smallSquares T).card : ℝ) + (largeSquares X T).card + (highPowers X).card := by
    exact_mod_cast hc'
  linarith [smallSquares_card T, largeSquares_card X T, highPowers_card X]

private lemma eulerD1_bound (X : ℕ) (hX : 1 ≤ X) :
    (eulerD1Count X : ℝ) ≤ 4 * (X : ℝ) ^ (5 / 6 : ℝ) := by
  let x : ℝ := X
  let u : ℝ := x ^ (1 / 6 : ℝ)
  let T : ℕ := ⌊u⌋₊
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < X by omega)
  have hu : 0 < u := Real.rpow_pos_of_pos hx _
  have hp (k : ℕ) : u ^ k = x ^ ((1 / 6 : ℝ) * k) := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast hx.le]
  have hp3 : u ^ 3 = x ^ (1 / 2 : ℝ) := by convert hp 3 using 1 <;> norm_num
  have hp5 : u ^ 5 = x ^ (5 / 6 : ℝ) := by convert hp 5 using 1 <;> norm_num
  have hp6 : u ^ 6 = x := by simpa using hp 6
  have hTu : (T : ℝ) ≤ u := Nat.floor_le hu.le
  have huT : u < (T : ℝ) + 1 := Nat.lt_floor_add_one u
  have hsmall : 3 * (T : ℝ) ^ 3 ≤ 3 * u ^ 3 := by gcongr
  have hlarge : 2 * x / (T + 1) ≤ 2 * u ^ 5 := by
    calc
      _ ≤ 2 * x / u := div_le_div_of_nonneg_left (by positivity) hu huT.le
      _ = _ := by rw [← hp6]; field_simp
  have hhigh : (Nat.sqrt X : ℝ) ≤ u ^ 3 := by
    rw [hp3]
    exact Real.nat_sqrt_le_real_sqrt.trans_eq (Real.sqrt_eq_rpow _)
  by_cases hu2 : u < 2
  · have hc : eulerD1Count X ≤ X :=
      (card_le_card (filter_subset _ _)).trans_eq (by simp)
    have hpow : u ^ 6 ≤ 4 * u ^ 5 := by
      calc
        _ = u ^ 5 * u := by ring
        _ ≤ u ^ 5 * 4 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by ring
    calc
      _ ≤ x := by dsimp [x]; exact_mod_cast hc
      _ = u ^ 6 := hp6.symm
      _ ≤ 4 * u ^ 5 := hpow
      _ = _ := by rw [hp5]
  · have hu2' : 2 ≤ u := le_of_not_gt hu2
    have huSq : 2 ≤ u ^ 2 := by nlinarith
    have h35 : 4 * u ^ 3 ≤ 2 * u ^ 5 := by
      nlinarith [mul_nonneg (by positivity : 0 ≤ u ^ 3) (by linarith : 0 ≤ u ^ 2 - 2)]
    have hen := eulerD1_envelope X T
    change (eulerD1Count X : ℝ) ≤
      3 * (T : ℝ) ^ 3 + 2 * x / (T + 1) + Nat.sqrt X at hen
    rw [← hp5]
    linarith

/-- The weighted totient condition D1 is a strong restriction on Euler-form integers. -/
theorem result :
    Tendsto (fun X : ℕ => (eulerD1Count X : ℝ) / eulerCount X) atTop (𝓝 0) := by
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun X : ℕ =>
      4 * exp 50 * (log (X : ℝ) / (X : ℝ) ^ (1 / 6 : ℝ))) atTop (𝓝 0) := by
    have ht : Tendsto (fun x : ℝ => log x / x ^ (1 / 6 : ℝ))
        atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero
    simpa using (ht.comp hnat).const_mul (4 * exp 50)
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
    _ ≤ (4 * (X : ℝ) ^ (5 / 6 : ℝ)) / eulerCount X :=
      div_le_div_of_nonneg_right (eulerD1_bound X (by omega)) hcount.le
    _ ≤ (4 * (X : ℝ) ^ (5 / 6 : ℝ)) /
        (exp (-50) * (X : ℝ) / log X) :=
      div_le_div_of_nonneg_left (by positivity) hlop hlow
    _ = _ := by
      have hpow : (X : ℝ) ^ (5 / 6 : ℝ) * (X : ℝ) ^ (1 / 6 : ℝ) = X := by
        rw [← Real.rpow_add hx]
        norm_num
      have he : exp (-50 : ℝ) * exp 50 = 1 := by rw [← exp_add]; norm_num
      have hu : (X : ℝ) ^ (1 / 6 : ℝ) ≠ 0 := (rpow_pos_of_pos hx _).ne'
      field_simp [hlog.ne', (exp_pos (-50 : ℝ)).ne', hx.ne', hu]
      nlinarith [hpow, he]

end D5.S3.Arith.Abundancy.WeightedTotientEulerDensity
