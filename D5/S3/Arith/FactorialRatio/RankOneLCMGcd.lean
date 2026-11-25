/- GID: D5/S3/Arith/FactorialRatio/RankOneLCMGcd
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/RankOneLCMGcd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Chebyshev]
   utility: none
   digest: Exact gcd and multinomial LCM identities for products of prefix LCMs. -/

module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Ring

/-!
For natural numbers `M ≤ H`, the product of prefix LCMs over `M < k ≤ H`
is the gcd of factorial products of all `(M+1)`-tuples summing to `H-M`.
The complementary product over `1 ≤ k ≤ M` is the LCM of the corresponding
multinomial coefficients multiplied by `H! / (H-M)!`.

For a fixed prime `p` and tuple sum `u = H-M`, the least possible sum of the
quotients by `p` is `(u+M)/p-M` in natural arithmetic. Every tuple with that quotient sum lifts
by bounded remainders to a tuple of sum `u`. This gives the same recursion
for the minimum factorial valuation and the valuation of the tail product.
The minimizing composition can depend on the prime. The identities are
motivated by the Alpoge-inspired rank-one window calculation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.RankOneLCMGcd

open Finset
open scoped Nat

/-- Product of the prefix LCMs at the quotients `H / k` for `M < k ≤ H`. -/
@[expose] public def tailLCM (H M : ℕ) : ℕ :=
  ∏ k ∈ Ioc M H, Nat.lcmUpto (H / k)

/-- Product of the prefix LCMs at the quotients `H / k` for `1 ≤ k ≤ M`. -/
@[expose] public def prefixLCM (H M : ℕ) : ℕ :=
  ∏ k ∈ Ioc 0 M, Nat.lcmUpto (H / k)

/-- The product of the factorials of the parts of a tuple. -/
@[expose] public def factorialProduct {r : ℕ} (a : Fin r → ℕ) : ℕ :=
  ∏ i, (a i)!

private theorem tailLCM_ne_zero (H M : ℕ) : tailLCM H M ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => Nat.lcmUpto_ne_zero (H / k)

private theorem factorialProduct_ne_zero {r : ℕ} (a : Fin r → ℕ) :
    factorialProduct a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (a i)

private def tailVal (p H M : ℕ) : ℕ :=
  ∑ k ∈ Ioc M H, Nat.log p (H / k)

private theorem factorization_tailLCM (H M : ℕ) {p : ℕ} (hp : p.Prime) :
    (tailLCM H M).factorization p = tailVal p H M := by
  unfold tailLCM tailVal
  rw [Nat.factorization_prod_apply (fun k _ => Nat.lcmUpto_ne_zero (H / k))]
  exact Finset.sum_congr rfl fun k _ => Nat.factorization_lcmUpto _ hp

private theorem tailVal_mono (p M : ℕ) {H H' : ℕ} (h : H ≤ H') :
    tailVal p H M ≤ tailVal p H' M := by
  unfold tailVal
  calc
    _ ≤ ∑ k ∈ Ioc M H, Nat.log p (H' / k) :=
      Finset.sum_le_sum fun k _ => Nat.log_mono_right (Nat.div_le_div_right h)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk => Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hk).1, (Finset.mem_Ioc.mp hk).2.trans h⟩)
      (fun _ _ _ => Nat.zero_le _)

private theorem tailVal_eq_zero (p H M : ℕ) (h : H ≤ M) :
    tailVal p H M = 0 := by
  simp [tailVal, Finset.Ioc_eq_empty_of_le h]

/-- The log-count recursion is a one-step count of multiples of p. -/
private theorem tailVal_step (p H M : ℕ) (hp : p.Prime) :
    tailVal p H M = H / p - M + tailVal p (H / p) M := by
  have hs : Ioc M (H / p) ⊆ Ioc M H := by
    intro k hk
    obtain ⟨hkM, hkH⟩ := Finset.mem_Ioc.mp hk
    exact Finset.mem_Ioc.mpr ⟨hkM, hkH.trans (Nat.div_le_self _ _)⟩
  have hz : ∀ k ∈ Ioc M H, k ∉ Ioc M (H / p) →
      Nat.log p (H / k) = 0 := by
    intro k hk hn
    obtain ⟨hkM, _⟩ := Finset.mem_Ioc.mp hk
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le M) hkM
    have hkgt : H / p < k := by
      by_contra h
      exact hn (Finset.mem_Ioc.mpr ⟨hkM, Nat.le_of_not_gt h⟩)
    have hmul : H < k * p := (Nat.div_lt_iff_lt_mul hp.pos).mp hkgt
    exact Nat.log_of_lt ((Nat.div_lt_iff_lt_mul hkpos).mpr (by
      simpa [Nat.mul_comm] using hmul))
  have hstep : ∀ k ∈ Ioc M (H / p),
      Nat.log p (H / k) = 1 + Nat.log p ((H / p) / k) := by
    intro k hk
    obtain ⟨hkM, hkH⟩ := Finset.mem_Ioc.mp hk
    have hkpos : 0 < k := lt_of_le_of_lt (Nat.zero_le M) hkM
    have hmul : k * p ≤ H := (Nat.le_div_iff_mul_le hp.pos).mp hkH
    have hle : p ≤ H / k := (Nat.le_div_iff_mul_le hkpos).mpr (by
      simpa [Nat.mul_comm] using hmul)
    have hlog : 0 < Nat.log p (H / k) := Nat.log_pos hp.one_lt hle
    have heq : H / k / p = H / p / k := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k p]
    have hdiv := Nat.log_div_base p (H / k)
    rw [heq] at hdiv
    omega
  unfold tailVal
  calc
    _ = ∑ k ∈ Ioc M (H / p), Nat.log p (H / k) :=
      (Finset.sum_subset hs hz).symm
    _ = ∑ k ∈ Ioc M (H / p), (1 + Nat.log p ((H / p) / k)) :=
      Finset.sum_congr rfl hstep
    _ = _ := by simp [Finset.sum_add_distrib]

private def cost {r : ℕ} (p : ℕ) (a : Fin r → ℕ) : ℕ :=
  ∑ i, padicValNat p (a i)!

private theorem factorization_factorialProduct {r : ℕ}
    (a : Fin r → ℕ) {p : ℕ} (hp : p.Prime) :
    (factorialProduct a).factorization p = cost p a := by
  unfold factorialProduct cost
  rw [Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero (a i))]
  exact Finset.sum_congr rfl fun i _ => Nat.factorization_def _ hp

private theorem cost_quotient {r p : ℕ} (hp : p.Prime) (a : Fin r → ℕ) :
    cost p a = (∑ i, a i / p) + cost p (fun i => a i / p) := by
  let : Fact p.Prime := ⟨hp⟩
  unfold cost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    padicValNat p (a i)! = padicValNat p (p * (a i / p))! :=
      (padicValNat_mul_div_factorial (p := p) (a i)).symm
    _ = a i / p + padicValNat p (a i / p)! := by
      rw [padicValNat_factorial_mul, Nat.add_comm]

private theorem cost_lift {r p : ℕ} (hp : p.Prime) (b c : Fin r → ℕ)
    (hc : ∀ i, c i < p) :
    cost p (fun i => p * b i + c i) = (∑ i, b i) + cost p b := by
  let : Fact p.Prime := ⟨hp⟩
  unfold cost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [padicValNat_factorial_mul_add (b i) (hc i), padicValNat_factorial_mul,
    Nat.add_comm]

/-- Every integer between zero and the total capacity has a bounded tuple. -/
private theorem exists_bounded_tuple (r cap d : ℕ) (hd : d ≤ r * cap) :
    ∃ c : Fin r → ℕ, (∑ i, c i) = d ∧ ∀ i, c i ≤ cap := by
  induction r generalizing d with
  | zero =>
    have hd0 : d = 0 := by simpa using hd
    subst d
    exact ⟨fun _ => 0, by simp, fun i => Fin.elim0 i⟩
  | succ r ih =>
    let x := min d cap
    have hx : x ≤ d := min_le_left _ _
    have hxc : x ≤ cap := min_le_right _ _
    have htail : d - x ≤ r * cap := by
      dsimp [x]
      by_cases h : d ≤ cap
      · simp [min_eq_left h]
      · rw [min_eq_right (Nat.le_of_not_ge h)]
        rw [Nat.succ_mul] at hd
        omega
    obtain ⟨c, hsum, hc⟩ := ih (d - x) htail
    refine ⟨Fin.cons x c, ?_, ?_⟩
    · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hxc
      · simpa using hc j

private theorem cap_eq (p M : ℕ) (hp : 1 ≤ p) :
    (M + 1) * (p - 1) + (M + 1) = (M + 1) * p := by
  calc
    _ = (M + 1) * ((p - 1) + 1) := by ring
    _ = _ := by rw [Nat.sub_add_cancel hp]

/-- The smallest quotient total compatible with u and M+1 remainders. -/
private theorem quotient_lower (p M u q : ℕ) (hp : p.Prime)
    (h : u ≤ p * q + (M + 1) * (p - 1)) :
    (u + M) / p - M ≤ q := by
  have heq : p * (q + M + 1) =
      p * q + ((M + 1) * (p - 1) + (M + 1)) := by
    rw [cap_eq p M hp.one_le]
    ring
  have hlt : u + M < (q + M + 1) * p := by
    rw [Nat.mul_comm (q + M + 1) p, heq]
    omega
  have hd := (Nat.div_lt_iff_lt_mul hp.pos).mpr hlt
  omega

/-- The proposed quotient total is feasible, with bounded residue sum. -/
private theorem quotient_feasible (p M u : ℕ) (hp : p.Prime) :
    p * ((u + M) / p - M) ≤ u ∧
      u ≤ p * ((u + M) / p - M) + (M + 1) * (p - 1) := by
  let d := (u + M) / p
  let t := d - M
  change p * t ≤ u ∧ u ≤ p * t + (M + 1) * (p - 1)
  have hd : p * d + (u + M) % p = u + M := Nat.div_add_mod _ _
  have hr : (u + M) % p < p := Nat.mod_lt _ hp.pos
  have hcap := cap_eq p M hp.one_le
  by_cases h : d ≤ M
  · have ht : t = 0 := Nat.sub_eq_zero_of_le h
    have hmul := Nat.mul_le_mul_left p h
    have heq : p * M + p = (M + 1) * p := by ring
    rw [ht, mul_zero, zero_add]
    omega
  · have hMd : M ≤ d := by omega
    have hdt : d = t + M := by dsimp [t]; omega
    have heq : p * d = p * t + p * M := by rw [hdt, Nat.mul_add]
    have hm : M ≤ p * M := by
      simpa using Nat.mul_le_mul_right M hp.one_le
    have heq' : p * M + p = (M + 1) * p := by ring
    omega

private theorem sum_quotient_bounds {p M u : ℕ} (hp : p.Prime)
    (a : Fin (M + 1) → ℕ) (ha : (∑ i, a i) = u) :
    p * (∑ i, a i / p) ≤ u ∧
      u ≤ p * (∑ i, a i / p) + (M + 1) * (p - 1) := by
  have heq : p * (∑ i, a i / p) + (∑ i, a i % p) = u := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← ha]
    exact Finset.sum_congr rfl fun i _ => Nat.div_add_mod _ _
  have hc : (∑ i, a i % p) ≤ (M + 1) * (p - 1) := by
    calc
      _ ≤ ∑ _i : Fin (M + 1), (p - 1) :=
        Finset.sum_le_sum fun i _ => by
          have := Nat.mod_lt (a i) hp.pos
          omega
      _ = _ := by simp
  omega

private theorem quotient_lt {p u q : ℕ} (hp : p.Prime)
    (hu : 0 < u) (hq : p * q ≤ u) : q < u := by
  have htwo : 2 ≤ p := hp.two_le
  have hmul := Nat.mul_le_mul_right q htwo
  omega

private theorem tailVal_shift (p M u : ℕ) (hp : p.Prime) :
    tailVal p (u + M) M =
      ((u + M) / p - M) + tailVal p (((u + M) / p - M) + M) M := by
  have hclip : tailVal p ((u + M) / p) M =
      tailVal p (((u + M) / p - M) + M) M := by
    by_cases h : M ≤ (u + M) / p
    · rw [Nat.sub_add_cancel h]
    · have h' : (u + M) / p ≤ M := by omega
      rw [tailVal_eq_zero _ _ _ h', Nat.sub_eq_zero_of_le h', zero_add,
        tailVal_eq_zero _ _ _ (Nat.le_refl M)]
  rw [tailVal_step p (u + M) M hp, hclip]

/-- Lower bound for every tuple, and attainment for each fixed prime.
The same induction gives both claims, including the zero-total case. -/
private theorem factorial_cost_min (p M u : ℕ) (hp : p.Prime) :
    (∀ a : Fin (M + 1) → ℕ, (∑ i, a i) = u →
      tailVal p (u + M) M ≤ cost p a) ∧
    (∃ a : Fin (M + 1) → ℕ, (∑ i, a i) = u ∧
      cost p a = tailVal p (u + M) M) := by
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu : u = 0
    · subst u
      constructor
      · intro a ha
        simp [tailVal]
      · refine ⟨fun _ => 0, by simp, ?_⟩
        simp [cost, tailVal, Nat.factorial_zero]
    have hupos : 0 < u := Nat.pos_of_ne_zero hu
    let t := (u + M) / p - M
    have htstep : tailVal p (u + M) M = t + tailVal p (t + M) M :=
      tailVal_shift p M u hp
    obtain ⟨htlow, hthigh⟩ := quotient_feasible p M u hp
    change p * t ≤ u at htlow
    change u ≤ p * t + (M + 1) * (p - 1) at hthigh
    have htlt : t < u := quotient_lt hp hupos htlow
    constructor
    · intro a ha
      let b : Fin (M + 1) → ℕ := fun i => a i / p
      let q := ∑ i, b i
      obtain ⟨hqlow, hqhigh⟩ := sum_quotient_bounds hp a ha
      change p * q ≤ u at hqlow
      change u ≤ p * q + (M + 1) * (p - 1) at hqhigh
      have htq : t ≤ q := quotient_lower p M u q hp hqhigh
      have hqlt := quotient_lt hp hupos hqlow
      have hrec := (ih q hqlt).1 b rfl
      have hmono := tailVal_mono p M (Nat.add_le_add_right htq M)
      rw [htstep, cost_quotient hp a]
      change t + tailVal p (t + M) M ≤ q + cost p b
      omega
    · obtain ⟨b, hb, hbcost⟩ := (ih t htlt).2
      let d := u - p * t
      have hd : d ≤ (M + 1) * (p - 1) := by dsimp [d]; omega
      obtain ⟨c, hc, hbound⟩ := exists_bounded_tuple (M + 1) (p - 1) d hd
      have hres : ∀ i, c i < p := fun i => by
        have hi := hbound i
        have := hp.pos
        omega
      refine ⟨fun i => p * b i + c i, ?_, ?_⟩
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hb, hc]
        dsimp [d]
        omega
      · rw [cost_lift hp b c hres, hb, hbcost, htstep]

/-- Divisibility for every weak composition of `H - M`. -/
private theorem tailLCM_dvd_factorialProduct (H M : ℕ) (hMH : M ≤ H)
    (a : Fin (M + 1) → ℕ) (ha : (∑ i, a i) = H - M) :
    tailLCM H M ∣ factorialProduct a := by
  apply (Nat.factorization_prime_le_iff_dvd (tailLCM_ne_zero H M)
    (factorialProduct_ne_zero a)).mp
  intro p hp
  rw [factorization_tailLCM H M hp, factorization_factorialProduct a hp]
  have h := (factorial_cost_min p M (H - M) hp).1 a ha
  simpa only [Nat.sub_add_cancel hMH] using h

/-- Exact primewise attainment. The optimizing tuple may depend on p. -/
private theorem exists_factorization_eq (H M p : ℕ) (hMH : M ≤ H) (hp : p.Prime) :
    ∃ a : Fin (M + 1) → ℕ, (∑ i, a i) = H - M ∧
      (factorialProduct a).factorization p = (tailLCM H M).factorization p := by
  obtain ⟨a, ha, hval⟩ := (factorial_cost_min p M (H - M) hp).2
  refine ⟨a, ha, ?_⟩
  rw [factorization_factorialProduct a hp, factorization_tailLCM H M hp]
  simpa only [Nat.sub_add_cancel hMH] using hval

/-- The tail product is the gcd of the factorial products of all weak compositions. -/
public theorem tailLCM_eq_gcd (H M : ℕ) (hMH : M ≤ H) :
    tailLCM H M =
      (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd factorialProduct := by
  classical
  let s := Finset.Nat.antidiagonalTuple (M + 1) (H - M)
  let G := s.gcd factorialProduct
  change tailLCM H M = G
  have hAG : tailLCM H M ∣ G := by
    apply Finset.dvd_gcd
    intro a ha
    exact tailLCM_dvd_factorialProduct H M hMH a
      (Finset.Nat.mem_antidiagonalTuple.mp ha)
  have hGne : G ≠ 0 := by
    apply Finset.gcd_ne_zero_iff.mpr
    obtain ⟨a, ha, _⟩ := exists_factorization_eq H M 2 hMH Nat.prime_two
    exact ⟨a, Finset.Nat.mem_antidiagonalTuple.mpr ha, factorialProduct_ne_zero a⟩
  apply Nat.dvd_antisymm hAG
  apply (Nat.factorization_prime_le_iff_dvd hGne (tailLCM_ne_zero H M)).mp
  intro p hp
  obtain ⟨a, ha, hval⟩ := exists_factorization_eq H M p hMH hp
  have hamem : a ∈ s := Finset.Nat.mem_antidiagonalTuple.mpr ha
  have hg : G ∣ factorialProduct a := Finset.gcd_dvd hamem
  have hle := (Nat.factorization_prime_le_iff_dvd hGne
    (factorialProduct_ne_zero a)).mpr hg p hp
  exact hle.trans_eq hval

private theorem tailLCM_zero_right (H : ℕ) : tailLCM H 0 = H ! := by
  rw [tailLCM_eq_gcd H 0 (Nat.zero_le _)]
  simp [factorialProduct]

private theorem prefix_mul_tail (H M : ℕ) (hMH : M ≤ H) :
    prefixLCM H M * tailLCM H M = H ! := by
  unfold prefixLCM
  rw [tailLCM, Finset.prod_Ioc_consecutive _ (Nat.zero_le M) hMH]
  exact tailLCM_zero_right H

/-- The factorial of the tuple sum is the tail product times the multinomial LCM. -/
private theorem tail_mul_multinomial_lcm (H M : ℕ) (hMH : M ≤ H) :
    tailLCM H M *
      (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).lcm
        (Nat.multinomial Finset.univ) = (H - M)! := by
  classical
  let s := Finset.Nat.antidiagonalTuple (M + 1) (H - M)
  let multinomial := Nat.multinomial (Finset.univ : Finset (Fin (M + 1)))
  let C := s.lcm multinomial
  change tailLCM H M * C = (H - M)!
  have hmul (a : Fin (M + 1) → ℕ) (ha : a ∈ s) :
      factorialProduct a * multinomial a = (H - M)! := by
    unfold factorialProduct multinomial
    rw [Nat.multinomial_spec, Finset.Nat.mem_antidiagonalTuple.mp ha]
  obtain ⟨a, ha, _⟩ := exists_factorization_eq H M 2 hMH Nat.prime_two
  have hamem : a ∈ s := Finset.Nat.mem_antidiagonalTuple.mpr ha
  have htailDvd (b : Fin (M + 1) → ℕ) (hb : b ∈ s) :
      tailLCM H M ∣ factorialProduct b :=
    tailLCM_dvd_factorialProduct H M hMH b (Finset.Nat.mem_antidiagonalTuple.mp hb)
  have htailFact : tailLCM H M ∣ (H - M)! := by
    rw [← hmul a hamem]
    exact (htailDvd a hamem).trans (dvd_mul_right _ _)
  apply Nat.dvd_antisymm
  · apply (Nat.dvd_div_iff_mul_dvd htailFact).mp
    apply Finset.lcm_dvd
    intro b hb
    apply (Nat.dvd_div_iff_mul_dvd htailFact).mpr
    rw [← hmul b hb]
    exact Nat.mul_dvd_mul (htailDvd b hb) (dvd_refl _)
  · have hgcd : (H - M)! ∣ s.gcd (fun b => factorialProduct b * C) := by
      apply Finset.dvd_gcd
      intro b hb
      rw [← hmul b hb]
      exact Nat.mul_dvd_mul (dvd_refl _) (Finset.dvd_lcm hb)
    rw [Finset.gcd_mul_right, normalize_eq] at hgcd
    exact (tailLCM_eq_gcd H M hMH).symm ▸ hgcd

/-- The prefix product is the multinomial LCM times the exact factorial ratio. -/
public theorem prefixLCM_eq_factorial_ratio_mul_multinomial_lcm
    (H M : ℕ) (hMH : M ≤ H) :
    prefixLCM H M = H ! / (H - M)! *
      (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).lcm
        (Nat.multinomial Finset.univ) := by
  let C := (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).lcm
      (Nat.multinomial Finset.univ)
  change prefixLCM H M = H ! / (H - M)! * C
  have htail : tailLCM H M * C = (H - M)! := tail_mul_multinomial_lcm H M hMH
  have hdiv := Nat.factorial_dvd_factorial (Nat.sub_le H M)
  apply (Nat.mul_left_inj (tailLCM_ne_zero H M)).mp
  calc
    prefixLCM H M * tailLCM H M = H ! := prefix_mul_tail H M hMH
    _ = (H ! / (H - M)!) * (H - M)! := (Nat.div_mul_cancel hdiv).symm
    _ = (H ! / (H - M)!) * C * tailLCM H M := by rw [← htail]; ring

#print axioms tailLCM_eq_gcd
#print axioms prefixLCM_eq_factorial_ratio_mul_multinomial_lcm

end D5.S3.Arith.FactorialRatio.RankOneLCMGcd
