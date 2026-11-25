/- GID: D5/S3/Arith/FactorialRatio/Weighted/CompositionGcd
   generality: G
   mirror-B: D5/B/S3/Arith/FactorialRatio/Weighted/CompositionGcd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: Simultaneous prime-power floor minima and exact nonnegative weighted factorial gcds. -/

module

public import D5.S3.Arith.FactorialRatio.RankOneLCMGcd
public import D5.S3.Arith.FactorialRatio.CompactFactorialGcd
public import OmegaMath.Arithmetic.WeightedFactorialGcd
public import OmegaChecks.NatCorrespondence
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.Tactic.Ring

/-!
For a prime p, equality in the ordinary factorial valuation lower bound
forces equality in every prime-power floor lower bound. The same composition
therefore minimizes every nonnegative weighting of those floors. Rational
primes may use different compositions.

The cutoff H in `weightedValue` includes all primes and powers relevant to
inputs n at most H. The power index j represents exponent j+1, so coefficients
`c p 0` are the coefficients of division by p, not of division by one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd

open Finset
open scoped Nat NumberField
open RankOneLCMGcd

namespace SF
open Omega.Arithmetic.SimultaneousFloor
open OmegaChecks.NatCorrespondence

private theorem sumBelow_eq_sum_range (n : ℕ) (f : Omega.Nat → Omega.Nat) :
    toStd (sumBelow (fromStd n) f) = ∑ i ∈ range n, toStd (f (fromStd i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change toStd ((sumBelow (fromStd n) f).add (f (fromStd n))) = _
    rw [toStd_add, ih, Finset.sum_range_succ]

private noncomputable def liftProfile (f : ℕ → ℕ) (i : Omega.Nat) : Omega.Nat :=
  fromStd (f (toStd i))

private theorem sumBelow_lift (n : ℕ) (f : ℕ → ℕ) :
    toStd (sumBelow (fromStd n) (liftProfile f)) = ∑ i ∈ range n, f i := by
  simp only [sumBelow_eq_sum_range, liftProfile, toStd_fromStd]

private theorem eq_of_toStd_eq {a b : Omega.Nat} (h : toStd a = toStd b) : Omega.Eq a b := by
  have hab : a = b := (fromStd_toStd a).symm.trans
    ((congrArg fromStd h).trans (fromStd_toStd b))
  cases hab
  exact Omega.Eq.refl a

private theorem lt_toStd {n : ℕ} {i : Omega.Nat}
    (hi : Omega.Nat.lt i (fromStd n)) : toStd i < n := by
  have h := (toStd_le_iff i.succ (fromStd n)).mpr hi
  change (toStd i).succ ≤ toStd (fromStd n) at h
  exact Nat.lt_of_succ_le (by simpa only [toStd_fromStd] using h)

private theorem lt_fromStd {i n : ℕ} (hi : i < n) :
    Omega.Nat.lt (fromStd i) (fromStd n) := by
  apply (toStd_le_iff (fromStd i).succ (fromStd n)).mp
  change (toStd (fromStd i)).succ ≤ toStd (fromStd n)
  simpa only [toStd_fromStd] using Nat.succ_le_of_lt hi

private theorem lift_order (n : ℕ) (f g : ℕ → ℕ) (h : ∀ i < n, f i ≤ g i) :
    ∀ i, Omega.Nat.lt i (fromStd n) → Omega.Nat.le (liftProfile f i) (liftProfile g i) := by
  intro i hi
  apply (toStd_le_iff _ _).mp
  simpa only [liftProfile, toStd_fromStd] using h (toStd i) (lt_toStd hi)

private theorem toStd_mul (a b : Omega.Nat) : toStd (a.mul b) = toStd a * toStd b := by
  induction b using Omega.Nat.rec with
  | zero =>
    have hz : a.mul Omega.Nat.zero = Omega.Nat.zero := by
      simpa only [Nat.mul_eq] using fromOmegaEq (Omega.Nat.mul_zero a)
    rw [hz]
    change 0 = toStd a * 0
    exact (Nat.mul_zero _).symm
  | succ b ih =>
    have hm : a.mul b.succ = (a.mul b).add a := by
      simpa only [Nat.mul_eq, Nat.add_eq] using fromOmegaEq (Omega.Nat.mul_succ a b)
    rw [hm, toStd_add, ih]
    change toStd a * toStd b + toStd a = toStd a * (toStd b).succ
    exact (Nat.mul_succ _ _).symm

private theorem weightedTotal_eq_sum_range (n : ℕ) (c f : Omega.Nat → Omega.Nat) :
    toStd (Omega.Arithmetic.WeightedFactorialGcd.weightedTotal (fromStd n) c f) =
      ∑ i ∈ range n, toStd (c (fromStd i)) * toStd (f (fromStd i)) := by
  simp only [Omega.Arithmetic.WeightedFactorialGcd.weightedTotal,
    sumBelow_eq_sum_range, toStd_mul]

/-- The strict finite-saturation theorem interpreted on the ordinary natural numbers. -/
private theorem saturation_range (n : ℕ) (f g : ℕ → ℕ)
    (h : ∀ i < n, f i ≤ g i) (hs : (∑ i ∈ range n, f i) = ∑ i ∈ range n, g i) :
    ∀ i < n, f i = g i := by
  have heq := saturation (fromStd n) (liftProfile f) (liftProfile g) (lift_order n f g h)
    (eq_of_toStd_eq (by rw [sumBelow_lift, sumBelow_lift]; exact hs))
  intro i hi
  have hh := congrArg toStd (fromOmegaEq (heq (fromStd i) (lt_fromStd hi)))
  simpa only [liftProfile, toStd_fromStd] using hh

private theorem weighted_saturation_range (n : ℕ) (f g c : ℕ → ℕ)
    (h : ∀ i < n, f i ≤ g i) (hs : (∑ i ∈ range n, f i) = ∑ i ∈ range n, g i) :
    (∑ i ∈ range n, c i * f i) = ∑ i ∈ range n, c i * g i := by
  have hw := Omega.Arithmetic.WeightedFactorialGcd.saturation_weighted
    (fromStd n) (liftProfile f) (liftProfile g) (lift_order n f g h)
    (eq_of_toStd_eq (by rw [sumBelow_lift, sumBelow_lift]; exact hs)) (liftProfile c)
  have hh := congrArg toStd (fromOmegaEq hw)
  simpa only [weightedTotal_eq_sum_range, liftProfile, toStd_fromStd] using hh

private theorem weighted_partition_range (n : ℕ) (c d f : ℕ → ℕ) :
    (∑ i ∈ range n, (c i + d i) * f i) =
      (∑ i ∈ range n, c i * f i) + ∑ i ∈ range n, d i * f i := by
  have hw := Omega.Arithmetic.WeightedFactorialGcd.weightedTotal_partition
    (fromStd n) (liftProfile c) (liftProfile d) (liftProfile f)
  have hh := congrArg toStd (fromOmegaEq hw)
  simpa only [toStd_add, weightedTotal_eq_sum_range, liftProfile, toStd_fromStd] using hh

end SF

/-- The total of the quotients of the parts by q. -/
@[expose] public def floorProfile {r : ℕ} (q : ℕ) (a : Fin r → ℕ) : ℕ :=
  ∑ i, a i / q

/-- The least possible quotient total for a composition of H-M into M+1 parts. -/
@[expose] public def floorMinimum (H M q : ℕ) : ℕ := H / q - M

private theorem part_le_head {H M : ℕ} (hMH : M ≤ H)
    (a : Fin (M + 1) → ℕ) (ha : (∑ i, a i) = H - M) (i : Fin (M + 1)) :
    a i ≤ H := by
  have hi : a i ≤ ∑ i, a i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
  rw [ha] at hi
  exact hi.trans (Nat.sub_le H M)

private theorem floor_lower {H M q : ℕ} (hq : 0 < q) (hMH : M ≤ H)
    (a : Fin (M + 1) → ℕ) (ha : (∑ i, a i) = H - M) :
    floorMinimum H M q ≤ floorProfile q a := by
  have hsum : q * floorProfile q a + (∑ i, a i % q) = H - M := by
    rw [floorProfile, Finset.mul_sum, ← Finset.sum_add_distrib, ← ha]
    exact Finset.sum_congr rfl fun i _ => Nat.div_add_mod _ _
  have hrem : (∑ i, a i % q) ≤ (M + 1) * (q - 1) := by
    calc
      _ ≤ ∑ _i : Fin (M + 1), (q - 1) :=
        Finset.sum_le_sum fun i _ => by have := Nat.mod_lt (a i) hq; omega
      _ = _ := by simp
  have hcap : (M + 1) * (q - 1) + (M + 1) = (M + 1) * q := by
    calc
      _ = (M + 1) * ((q - 1) + 1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hq]
  have hmul : q * (floorProfile q a + M + 1) =
      q * floorProfile q a + ((M + 1) * (q - 1) + (M + 1)) := by
    rw [hcap]
    ring
  have hlt : H < (floorProfile q a + M + 1) * q := by
    rw [mul_comm _ q, hmul]
    omega
  have hd := (Nat.div_lt_iff_lt_mul hq).mpr hlt
  unfold floorMinimum
  omega

private theorem power_cutoff {p H : ℕ} (hp : p.Prime) : H / p ^ (H + 2) = 0 := by
  apply Nat.div_eq_of_lt
  have h : H + 2 < p ^ (H + 2) := Nat.lt_pow_self hp.one_lt
  omega

private theorem factorial_profile_sum {H M p : ℕ} (hp : p.Prime) (hMH : M ≤ H)
    (a : Fin (M + 1) → ℕ) (ha : (∑ i, a i) = H - M) :
    (factorialProduct a).factorization p =
      ∑ j ∈ range (H + 1), floorProfile (p ^ (j + 1)) a := by
  let _ : Fact p.Prime := ⟨hp⟩
  unfold factorialProduct floorProfile
  rw [Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero (a i))]
  calc
    _ = ∑ i, ∑ j ∈ range (H + 1), a i / p ^ (j + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hlog : Nat.log p (a i) < H + 2 :=
        lt_of_le_of_lt ((Nat.log_le_self p (a i)).trans (part_le_head hMH a ha i))
          (by omega)
      rw [Nat.factorization_def _ hp, padicValNat_factorial hlog,
        Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    _ = _ := Finset.sum_comm

private theorem tail_profile_sum {H M p : ℕ} (hp : p.Prime) :
    (tailLCM H M).factorization p =
      ∑ j ∈ range (H + 1), floorMinimum H M (p ^ (j + 1)) := by
  rw [CompactFactorialGcd.tail_factorization_sum (H := H) (M := M) (K := H + 2)
    hp (by rw [power_cutoff hp]; omega),
    Finset.sum_Ico_eq_sum_range]
  simp [floorMinimum, Nat.add_comm]

private theorem saturation_of_factorial_equality {H M p : ℕ}
    (hp : p.Prime) (hMH : M ≤ H) (a : Fin (M + 1) → ℕ)
    (ha : (∑ i, a i) = H - M)
    (heq : (factorialProduct a).factorization p = (tailLCM H M).factorization p) :
    ∀ j : ℕ, 0 < j → floorProfile (p ^ j) a = floorMinimum H M (p ^ j) := by
  have hs : (∑ j ∈ range (H + 1), floorMinimum H M (p ^ (j + 1))) =
      ∑ j ∈ range (H + 1), floorProfile (p ^ (j + 1)) a := by
    rw [← tail_profile_sum hp, ← factorial_profile_sum hp hMH a ha]
    exact heq.symm
  have heach := SF.saturation_range (H + 1)
    (fun j => floorMinimum H M (p ^ (j + 1)))
    (fun j => floorProfile (p ^ (j + 1)) a)
    (fun j _ => floor_lower (pow_pos hp.pos _) hMH a ha) hs
  intro j hj
  by_cases hsmall : j ≤ H + 1
  · simpa [Nat.sub_add_cancel hj] using (heach (j - 1) (by omega)).symm
  · have hpow : H < p ^ j := by
      have hh : j < p ^ j := Nat.lt_pow_self hp.one_lt
      omega
    have hzero : H / p ^ j = 0 := Nat.div_eq_of_lt hpow
    have hazero : ∀ i, a i / p ^ j = 0 := fun i =>
      Nat.div_eq_of_lt ((part_le_head hMH a ha i).trans_lt hpow)
    simp [floorProfile, floorMinimum, hzero, hazero]

/-- A prime has one composition minimizing every one of its power-floor sums. -/
public theorem simultaneous_floor_minimum (H M p : ℕ) (hMH : M ≤ H) (hp : p.Prime) :
    ∃ a : Fin (M + 1) → ℕ, (∑ i, a i) = H - M ∧
      ∀ j : ℕ, 0 < j → floorProfile (p ^ j) a = floorMinimum H M (p ^ j) := by
  obtain ⟨a, ha, heq⟩ := RankOneLCMGcd.exists_factorization_eq H M p hMH hp
  exact ⟨a, ha, saturation_of_factorial_equality hp hMH a ha heq⟩

/-- Weighted prime exponent; index j corresponds to the power p^(j+1). -/
@[expose] public def weightedExponent (H : ℕ) (c : ℕ → ℕ → ℕ) (p n : ℕ) : ℕ :=
  ∑ j ∈ range (H + 1), c p j * (n / p ^ (j + 1))

/-- Weighted factorial for inputs n<=H, with a common finite cutoff H. -/
@[expose] public def weightedValue (H : ℕ) (c : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE H, p ^ weightedExponent H c p n

@[expose] public def weightedProduct {r : ℕ} (H : ℕ) (c : ℕ → ℕ → ℕ)
    (a : Fin r → ℕ) : ℕ := ∏ i, weightedValue H c (a i)

/-- Product of the weighted primewise lower bounds. -/
@[expose] public def weightedTail (H M : ℕ) (c : ℕ → ℕ → ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE H,
    p ^ (∑ j ∈ range (H + 1), c p j * floorMinimum H M (p ^ (j + 1)))

private theorem weightedValue_ne_zero (H : ℕ) (c : ℕ → ℕ → ℕ) (n : ℕ) :
    weightedValue H c n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.mem_primesLE.mp hp).2.ne_zero

private theorem weightedProduct_ne_zero {r : ℕ} (H : ℕ) (c : ℕ → ℕ → ℕ)
    (a : Fin r → ℕ) : weightedProduct H c a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => weightedValue_ne_zero H c (a i)

private theorem weightedTail_ne_zero (H M : ℕ) (c : ℕ → ℕ → ℕ) :
    weightedTail H M c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.mem_primesLE.mp hp).2.ne_zero

private theorem prime_product_factorization (P : Finset ℕ) (e : ℕ → ℕ)
    (hP : ∀ p ∈ P, p.Prime) (p : ℕ) :
    (∏ q ∈ P, q ^ e q).factorization p = if p ∈ P then e p else 0 := by
  rw [Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (hP q hq).ne_zero)]
  by_cases hp : p ∈ P
  · rw [if_pos hp]
    calc
      _ = (p ^ e p).factorization p := by
        apply Finset.sum_eq_single p
        · intro q hq hqp
          rw [(hP q hq).factorization_pow]
          simp [hqp, Ne.symm hqp]
        · exact fun hn => (hn hp).elim
      _ = e p := Nat.factorization_pow_self (hP p hp)
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp : q ≠ p := fun heq => hp (heq ▸ hq)
    rw [(hP q hq).factorization_pow]
    simp [hqp, Ne.symm hqp]

private theorem weightedProduct_factorization {r : ℕ} (H : ℕ) (c : ℕ → ℕ → ℕ)
    (a : Fin r → ℕ) {p : ℕ} (hp : p ∈ Nat.primesLE H) :
    (weightedProduct H c a).factorization p =
      ∑ j ∈ range (H + 1), c p j * floorProfile (p ^ (j + 1)) a := by
  unfold weightedProduct
  rw [Nat.factorization_prod_apply (fun i _ => weightedValue_ne_zero H c (a i))]
  simp_rw [weightedValue, prime_product_factorization _ _
    (fun q hq => (Nat.mem_primesLE.mp hq).2), if_pos hp, weightedExponent]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

private theorem weightedTail_factorization (H M : ℕ) (c : ℕ → ℕ → ℕ)
    {p : ℕ} (hp : p ∈ Nat.primesLE H) :
    (weightedTail H M c).factorization p =
      ∑ j ∈ range (H + 1), c p j * floorMinimum H M (p ^ (j + 1)) := by
  unfold weightedTail
  rw [prime_product_factorization _ _ (fun q hq => (Nat.mem_primesLE.mp hq).2), if_pos hp]

private theorem weightedProduct_factorization_outside {r : ℕ} (H : ℕ)
    (c : ℕ → ℕ → ℕ) (a : Fin r → ℕ) {p : ℕ} (hp : p ∉ Nat.primesLE H) :
    (weightedProduct H c a).factorization p = 0 := by
  unfold weightedProduct
  rw [Nat.factorization_prod_apply (fun i _ => weightedValue_ne_zero H c (a i))]
  simp [weightedValue, prime_product_factorization _ _
    (fun q hq => (Nat.mem_primesLE.mp hq).2), hp]

private theorem weightedTail_dvd {H M : ℕ} (hMH : M ≤ H)
    (c : ℕ → ℕ → ℕ) (a : Fin (M + 1) → ℕ) (ha : (∑ i, a i) = H - M) :
    weightedTail H M c ∣ weightedProduct H c a := by
  apply (Nat.factorization_prime_le_iff_dvd (weightedTail_ne_zero H M c)
    (weightedProduct_ne_zero H c a)).mp
  intro p hp
  by_cases hpin : p ∈ Nat.primesLE H
  · rw [weightedTail_factorization H M c hpin, weightedProduct_factorization H c a hpin]
    exact Finset.sum_le_sum fun j _ =>
      Nat.mul_le_mul_left _ (floor_lower (pow_pos hp.pos _) hMH a ha)
  · have hz : (weightedTail H M c).factorization p = 0 := by
      unfold weightedTail
      rw [prime_product_factorization _ _ (fun q hq => (Nat.mem_primesLE.mp hq).2),
        if_neg hpin]
    rw [hz]
    exact Nat.zero_le _

private theorem weighted_attainment {H M : ℕ} (hMH : M ≤ H)
    (c : ℕ → ℕ → ℕ) {p : ℕ} (hp : p.Prime) :
    ∃ a : Fin (M + 1) → ℕ, (∑ i, a i) = H - M ∧
      (weightedProduct H c a).factorization p = (weightedTail H M c).factorization p := by
  obtain ⟨a, ha, heq⟩ := simultaneous_floor_minimum H M p hMH hp
  refine ⟨a, ha, ?_⟩
  by_cases hpin : p ∈ Nat.primesLE H
  · rw [weightedProduct_factorization H c a hpin, weightedTail_factorization H M c hpin]
    exact Finset.sum_congr rfl fun j _ => congrArg (c p j * ·) (heq (j + 1) (by omega))
  · rw [weightedProduct_factorization_outside H c a hpin]
    unfold weightedTail
    rw [prime_product_factorization _ _ (fun q hq => (Nat.mem_primesLE.mp hq).2), if_neg hpin]

private theorem saturated_weighted_profile {H M p : ℕ}
    (hp : p.Prime) (hMH : M ≤ H) (a : Fin (M + 1) → ℕ)
    (ha : (∑ i, a i) = H - M)
    (heq : (factorialProduct a).factorization p = (tailLCM H M).factorization p)
    (c : ℕ → ℕ → ℕ) :
    (∑ j ∈ range (H + 1), c p j * floorMinimum H M (p ^ (j + 1))) =
      ∑ j ∈ range (H + 1), c p j * floorProfile (p ^ (j + 1)) a := by
  have hs : (∑ j ∈ range (H + 1), floorMinimum H M (p ^ (j + 1))) =
      ∑ j ∈ range (H + 1), floorProfile (p ^ (j + 1)) a := by
    rw [← tail_profile_sum hp, ← factorial_profile_sum hp hMH a ha]
    exact heq.symm
  exact SF.weighted_saturation_range (H + 1)
    (fun j => floorMinimum H M (p ^ (j + 1)))
    (fun j => floorProfile (p ^ (j + 1)) a)
    (c p)
    (fun j _ => floor_lower (pow_pos hp.pos _) hMH a ha)
    hs

private theorem tail_ne_zero (H M : ℕ) : tailLCM H M ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => Nat.lcmUpto_ne_zero (H / k)

private theorem factorialProduct_ne_zero {r : ℕ} (a : Fin r → ℕ) :
    factorialProduct a ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (a i)

private theorem certificate_attainment {H M : ℕ}
    (C : Finset (Fin (M + 1) → ℕ)) (heq : C.gcd factorialProduct = tailLCM H M)
    {p : ℕ} (hp : p.Prime) :
    ∃ a ∈ C, (factorialProduct a).factorization p = (tailLCM H M).factorization p := by
  classical
  by_contra hn
  push_neg at hn
  have hd : p ^ ((tailLCM H M).factorization p + 1) ∣ C.gcd factorialProduct := by
    apply Finset.dvd_gcd
    intro a ha
    apply (hp.pow_dvd_iff_le_factorization (factorialProduct_ne_zero a)).mpr
    have hdiv : tailLCM H M ∣ factorialProduct a := heq ▸ Finset.gcd_dvd ha
    have hle := (Nat.factorization_prime_le_iff_dvd (tail_ne_zero H M)
      (factorialProduct_ne_zero a)).mpr hdiv p hp
    have hne := hn a ha
    omega
  rw [heq] at hd
  have hbad := (hp.pow_dvd_iff_le_factorization (tail_ne_zero H M)).mp hd
  omega

/-- Exact weighted factorial gcd over all weak compositions, including H=M=0. -/
public theorem weighted_composition_gcd (H M : ℕ) (hMH : M ≤ H) (c : ℕ → ℕ → ℕ) :
    (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd (weightedProduct H c) =
      weightedTail H M c := by
  classical
  let S := Finset.Nat.antidiagonalTuple (M + 1) (H - M)
  have hlow : weightedTail H M c ∣ S.gcd (weightedProduct H c) := by
    apply Finset.dvd_gcd
    intro a ha
    exact weightedTail_dvd hMH c a (Finset.Nat.mem_antidiagonalTuple.mp ha)
  have hne : S.gcd (weightedProduct H c) ≠ 0 := by
    obtain ⟨a, ha, _⟩ := weighted_attainment hMH c Nat.prime_two
    exact Finset.gcd_ne_zero_iff.mpr
      ⟨a, Finset.Nat.mem_antidiagonalTuple.mpr ha, weightedProduct_ne_zero H c a⟩
  apply Nat.dvd_antisymm _ hlow
  apply (Nat.factorization_prime_le_iff_dvd hne (weightedTail_ne_zero H M c)).mp
  intro p hp
  obtain ⟨a, ha, heq⟩ := weighted_attainment hMH c hp
  have hd : S.gcd (weightedProduct H c) ∣ weightedProduct H c a :=
    Finset.gcd_dvd (Finset.Nat.mem_antidiagonalTuple.mpr ha)
  exact ((Nat.factorization_prime_le_iff_dvd hne
    (weightedProduct_ne_zero H c a)).mpr hd p hp).trans_eq heq

/-- Any finite exact ordinary-factorial certificate is exact for every natural weighting. -/
public theorem exact_certificate_is_universal (H M : ℕ) (hMH : M ≤ H)
    (C : Finset (Fin (M + 1) → ℕ))
    (hC : ∀ a ∈ C, (∑ i, a i) = H - M)
    (hordinary : C.gcd factorialProduct = tailLCM H M) (c : ℕ → ℕ → ℕ) :
    C.gcd (weightedProduct H c) = weightedTail H M c := by
  classical
  have hnonempty : C.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.gcd_empty] at hordinary
    exact tail_ne_zero H M hordinary.symm
  have hG : C.gcd (weightedProduct H c) ≠ 0 := by
    obtain ⟨a, ha⟩ := hnonempty
    exact Finset.gcd_ne_zero_iff.mpr ⟨a, ha, weightedProduct_ne_zero H c a⟩
  apply Nat.dvd_antisymm
  · apply (Nat.factorization_prime_le_iff_dvd hG (weightedTail_ne_zero H M c)).mp
    intro p hp
    obtain ⟨a, ha, heq⟩ := certificate_attainment C hordinary hp
    have hle := (Nat.factorization_prime_le_iff_dvd hG
      (weightedProduct_ne_zero H c a)).mpr (Finset.gcd_dvd ha) p hp
    by_cases hpin : p ∈ Nat.primesLE H
    · rw [weightedProduct_factorization H c a hpin] at hle
      rw [weightedTail_factorization H M c hpin]
      exact hle.trans_eq (saturated_weighted_profile hp hMH a (hC a ha) heq c).symm
    · rw [weightedProduct_factorization_outside H c a hpin] at hle
      exact hle.trans (Nat.zero_le _)
  · exact Finset.dvd_gcd fun a ha => weightedTail_dvd hMH c a (hC a ha)

/-- A bounded composition and at most one composition per small prime suffice for all weights. -/
public theorem exists_small_universal_certificate (H M : ℕ) (hMH : M ≤ H) :
    ∃ C : Finset (Fin (M + 1) → ℕ),
      (∀ a ∈ C, (∑ i, a i) = H - M) ∧
      C.card ≤ Nat.primeCounting (H / (M + 1)) + 1 ∧
      C.gcd factorialProduct = tailLCM H M ∧
      ∀ c : ℕ → ℕ → ℕ, C.gcd (weightedProduct H c) = weightedTail H M c := by
  classical
  let t := H / (M + 1)
  have hcap : H - M ≤ (M + 1) * t := by
    have hd := Nat.div_add_mod H (M + 1)
    have hr := Nat.mod_lt H (by omega : 0 < M + 1)
    dsimp [t]
    omega
  obtain ⟨balanced, hbalanced, hbound⟩ := RankOneLCMGcd.exists_bounded_tuple
    (M + 1) t (H - M) hcap
  have hw : ∀ p, p.Prime → ∃ a : Fin (M + 1) → ℕ,
      (∑ i, a i) = H - M ∧
        (factorialProduct a).factorization p = (tailLCM H M).factorization p :=
    fun p hp => RankOneLCMGcd.exists_factorization_eq H M p hMH hp
  let witness (p : ℕ) : Fin (M + 1) → ℕ :=
    if hp : p.Prime then Classical.choose (hw p hp) else balanced
  have hwitness (p : ℕ) (hp : p.Prime) :
      (∑ i, witness p i) = H - M ∧
        (factorialProduct (witness p)).factorization p = (tailLCM H M).factorization p := by
    simpa only [witness, dif_pos hp] using Classical.choose_spec (hw p hp)
  let C := insert balanced ((Nat.primesLE t).image witness)
  have hC : ∀ a ∈ C, (∑ i, a i) = H - M := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hbalanced
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact (hwitness p (Nat.mem_primesLE.mp hp).2).1
  have hcard : C.card ≤ Nat.primeCounting t + 1 := by
    calc
      C.card ≤ ((Nat.primesLE t).image witness).card + 1 := Finset.card_insert_le _ _
      _ ≤ (Nat.primesLE t).card + 1 := Nat.add_le_add_right (Finset.card_image_le) _
      _ = _ := by rw [Nat.primesLE_card_eq_primeCounting]
  have hG : C.gcd factorialProduct ≠ 0 :=
    Finset.gcd_ne_zero_iff.mpr ⟨balanced, Finset.mem_insert_self _ _, factorialProduct_ne_zero _⟩
  have htail : tailLCM H M ∣ C.gcd factorialProduct := by
    apply Finset.dvd_gcd
    intro a ha
    rw [tailLCM_eq_gcd H M hMH]
    exact Finset.gcd_dvd (Finset.Nat.mem_antidiagonalTuple.mpr (hC a ha))
  have hexact : C.gcd factorialProduct = tailLCM H M := by
    apply Nat.dvd_antisymm _ htail
    apply (Nat.factorization_prime_le_iff_dvd hG (tail_ne_zero H M)).mp
    intro p hp
    by_cases hpt : p ≤ t
    · have hmem : witness p ∈ C := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨p, Nat.mem_primesLE.mpr ⟨hpt, hp⟩, rfl⟩)
      exact ((Nat.factorization_prime_le_iff_dvd hG (factorialProduct_ne_zero _)).mpr
        (Finset.gcd_dvd hmem) p hp).trans_eq (hwitness p hp).2
    · have hzero : (factorialProduct balanced).factorization p = 0 := by
        unfold factorialProduct
        rw [Nat.factorization_prod_apply (fun i _ => Nat.factorial_ne_zero _)]
        apply Finset.sum_eq_zero
        intro i _
        exact Nat.factorization_eq_zero_of_not_dvd (fun hd =>
          hpt ((hp.dvd_factorial.mp hd).trans (hbound i)))
      have hle := (Nat.factorization_prime_le_iff_dvd hG
        (factorialProduct_ne_zero balanced)).mpr
        (Finset.gcd_dvd (Finset.mem_insert_self balanced _)) p hp
      rw [hzero] at hle
      exact hle.trans (Nat.zero_le _)
  exact ⟨C, hC, hcard, hexact, exact_certificate_is_universal H M hMH C hC hexact⟩

private theorem factorial_factorization_sum {H n p : ℕ} (hp : p.Prime) (hn : n ≤ H) :
    (n !).factorization p = ∑ j ∈ range (H + 1), n / p ^ (j + 1) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p n < H + 2 :=
    lt_of_le_of_lt ((Nat.log_le_self p n).trans hn) (by omega)
  rw [Nat.factorization_def _ hp, padicValNat_factorial hlog,
    Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem weightedValue_cutoff (H n : ℕ) (c : ℕ → ℕ → ℕ) (hn : n ≤ H) :
    weightedValue H c n = weightedValue n c n := by
  classical
  have hsub : Nat.primesLE n ⊆ Nat.primesLE H := by
    intro p hp
    obtain ⟨hpn, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpn.trans hn, hpprime⟩
  have hexp (p : ℕ) (hp : p.Prime) : weightedExponent H c p n = weightedExponent n c p n := by
    unfold weightedExponent
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hnot
    have hjn : n + 1 ≤ j := by simpa using hnot
    have hpow : j + 1 < p ^ (j + 1) := Nat.lt_pow_self hp.one_lt
    simp [Nat.div_eq_of_lt (show n < p ^ (j + 1) by omega)]
  unfold weightedValue
  calc
    _ = ∏ p ∈ Nat.primesLE H, p ^ weightedExponent n c p n :=
      Finset.prod_congr rfl fun p hp => congrArg (p ^ ·) (hexp p (Nat.mem_primesLE.mp hp).2)
    _ = _ := by
      symm
      apply Finset.prod_subset hsub
      intro p hp hnot
      have hpprime := (Nat.mem_primesLE.mp hp).2
      have hnp : n < p := by
        by_contra h
        exact hnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
      have hz : ∀ j : ℕ, n / p ^ (j + 1) = 0 := by
        intro j
        have hle : p ≤ p ^ (j + 1) := by
          rw [pow_succ']
          exact Nat.le_mul_of_pos_right _ (pow_pos hpprime.pos _)
        exact Nat.div_eq_of_lt (hnp.trans_le hle)
      simp [weightedExponent, hz]

private theorem weightedValue_constant (H n d : ℕ) (hn : n ≤ H) :
    weightedValue H (fun _ _ => d) n = (n !) ^ d := by
  apply Nat.eq_of_factorization_eq (weightedValue_ne_zero _ _ _)
    (pow_ne_zero _ (Nat.factorial_ne_zero _))
  intro p
  by_cases hp : p.Prime
  · by_cases hpH : p ≤ H
    · have hpin := Nat.mem_primesLE.mpr ⟨hpH, hp⟩
      rw [weightedValue, prime_product_factorization _ _
        (fun q hq => (Nat.mem_primesLE.mp hq).2), if_pos hpin,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        factorial_factorization_sum hp hn]
      exact (Finset.mul_sum _ _ _).symm
    · have hpin : p ∉ Nat.primesLE H := fun h => hpH (Nat.mem_primesLE.mp h).1
      have hnot : ¬ p ∣ n ! := fun h => hpH ((hp.dvd_factorial.mp h).trans hn)
      simp [weightedValue, prime_product_factorization _ _
        (fun q hq => (Nat.mem_primesLE.mp hq).2), hpin,
        Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hnot]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem weightedTail_constant (H M d : ℕ) :
    weightedTail H M (fun _ _ => d) = (tailLCM H M) ^ d := by
  apply Nat.eq_of_factorization_eq (weightedTail_ne_zero _ _ _)
    (pow_ne_zero _ (tail_ne_zero _ _))
  intro p
  by_cases hp : p.Prime
  · by_cases hpH : p ≤ H
    · rw [weightedTail_factorization H M _ (Nat.mem_primesLE.mpr ⟨hpH, hp⟩),
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, tail_profile_sum hp]
      exact (Finset.mul_sum _ _ _).symm
    · have hpin : p ∉ Nat.primesLE H := fun h => hpH (Nat.mem_primesLE.mp h).1
      have hzero : (tailLCM H M).factorization p = 0 := by
        rw [tail_profile_sum hp]
        apply Finset.sum_eq_zero
        intro j _
        have hpow : p ≤ p ^ (j + 1) := by
          calc
            p = p * 1 := (mul_one _).symm
            _ ≤ p * p ^ j := Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hp.pos)
            _ = p ^ (j + 1) := (pow_succ' _ _).symm
        have hlt : H < p ^ (j + 1) := (lt_of_not_ge hpH).trans_le hpow
        simp [floorMinimum, Nat.div_eq_of_lt hlt]
      simp [weightedTail, prime_product_factorization _ _
        (fun q hq => (Nat.mem_primesLE.mp hq).2), hpin,
        Nat.factorization_pow, hzero]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem weightedValue_add (H : ℕ) (c c' : ℕ → ℕ → ℕ) (n : ℕ) :
    weightedValue H c n * weightedValue H c' n =
      weightedValue H (fun p j => c p j + c' p j) n := by
  unfold weightedValue weightedExponent
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add]
  apply congrArg (p ^ ·)
  exact (SF.weighted_partition_range (H + 1) (c p) (c' p)
    (fun j => n / p ^ (j + 1))).symm

private theorem weightedTail_add (H M : ℕ) (c c' : ℕ → ℕ → ℕ) :
    weightedTail H M c * weightedTail H M c' =
      weightedTail H M (fun p j => c p j + c' p j) := by
  unfold weightedTail
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add]
  apply congrArg (p ^ ·)
  exact (SF.weighted_partition_range (H + 1) (c p) (c' p)
    (fun j => floorMinimum H M (p ^ (j + 1)))).symm

private theorem residue_power_reindex {p f H n : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hn : n ≤ H) :
    (∑ j ∈ range (H + 1), n / (p ^ f) ^ (j + 1)) =
      ∑ j ∈ range (H + 1), if f ∣ j + 1 then n / p ^ (j + 1) else 0 := by
  classical
  apply Finset.sum_bij_ne_zero (fun j _ _ => f * (j + 1) - 1)
  · intro j hj hnonzero
    apply Finset.mem_range.mpr
    have hpos : 0 < f * (j + 1) := Nat.mul_pos hf (by omega)
    have hdenom : p ^ (f * (j + 1)) ≤ n := by
      by_contra h
      apply hnonzero
      rw [← pow_mul]
      exact Nat.div_eq_of_lt (lt_of_not_ge h)
    have hpower : f * (j + 1) < p ^ (f * (j + 1)) := Nat.lt_pow_self hp.one_lt
    omega
  · intro j hj hjnz k hk hknz heq
    have hjpos : 0 < f * (j + 1) := Nat.mul_pos hf (by omega)
    have hkpos : 0 < f * (k + 1) := Nat.mul_pos hf (by omega)
    have hm : f * (j + 1) = f * (k + 1) := by omega
    have hh := Nat.mul_left_cancel hf hm
    omega
  · intro k hk hnonzero
    have hdiv : f ∣ k + 1 := by
      by_contra h
      simp [h] at hnonzero
    have hmul : f * ((k + 1) / f) = k + 1 := Nat.mul_div_cancel' hdiv
    have hqpos : (0 : ℕ) < (k + 1) / f := by
      apply Nat.pos_of_ne_zero
      intro hz
      rw [hz, mul_zero] at hmul
      exact (Nat.succ_ne_zero k) hmul.symm
    let j := (k + 1) / f - 1
    have hj : j ∈ range (H + 1) := by
      have hkbound := Finset.mem_range.mp hk
      have hqle := Nat.div_le_self (k + 1) f
      apply Finset.mem_range.mpr
      dsimp [j]
      omega
    have he : f * (j + 1) = k + 1 := by
      dsimp [j]
      rw [Nat.sub_add_cancel hqpos]
      exact hmul
    refine ⟨j, hj, ?_, ?_⟩
    · rw [← pow_mul, he]
      simpa only [if_pos hdiv] using hnonzero
    · omega
  · intro j hj hnonzero
    have hpos : 0 < f * (j + 1) := Nat.mul_pos hf (by omega)
    rw [Nat.sub_add_cancel hpos, if_pos (dvd_mul_right f (j + 1)), ← pow_mul]

namespace NumberFieldNorm

variable (K : Type*) [Field K] [NumberField K]

local instance ringOfIntegersInfinite : Infinite (𝓞 K) :=
  Module.Free.infinite ℤ (𝓞 K)

/-- The rational prime ideal generated by p. -/
@[expose] public def rationalPrimeIdeal (p : ℕ) : Ideal ℤ := Ideal.span {(p : ℤ)}

/-- Actual prime ideals in the ring of integers lying above the rational ideal (p). -/
@[expose] public noncomputable def primesAbove (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal p) (𝓞 K)

/-- Norm weights at p^(j+1), using the actual residue degrees of primes over p. -/
@[expose] public noncomputable def normWeight (p j : ℕ) : ℕ :=
  ∑ P ∈ primesAbove K p,
    if P.inertiaDeg ℤ ∣ j + 1 then P.inertiaDeg ℤ else 0

/-- The finite Euler ideal expressed in rational-prime power coordinates. -/
@[expose] public noncomputable def residueFactorialIdeal (H n : ℕ) : Ideal (𝓞 K) :=
  ∏ p ∈ Nat.primesLE H, ∏ P ∈ primesAbove K p,
    P ^ (∑ j ∈ range (H + 1), if P.inertiaDeg ℤ ∣ j + 1 then n / p ^ (j + 1) else 0)

/-- The full-ring factorial ideal in its prime-ideal Euler-product presentation. -/
@[expose] public noncomputable def fullRingFactorialIdeal (n : ℕ) : Ideal (𝓞 K) :=
  ∏ p ∈ Nat.primesLE n, ∏ P ∈ primesAbove K p,
    P ^ (∑ j ∈ range (n + 1), n / P.absNorm ^ (j + 1))

/-- The integer quotient complementary to the norm of the finite Euler ideal. -/
@[expose] public noncomputable def normComplement (n : ℕ) : ℕ :=
  (n !) ^ Module.finrank ℚ K / (fullRingFactorialIdeal K n).absNorm

public theorem rationalPrimeIdeal_ne_bot {p : ℕ} (hp : p.Prime) :
    rationalPrimeIdeal p ≠ ⊥ := by
  simpa [rationalPrimeIdeal, Ideal.span_singleton_eq_bot] using
    (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)

public theorem rationalPrimeIdeal_isPrime {p : ℕ} (hp : p.Prime) :
    (rationalPrimeIdeal p).IsPrime := by
  apply (Ideal.span_singleton_prime (show (p : ℤ) ≠ 0 by exact_mod_cast hp.ne_zero)).mpr
  exact Nat.prime_iff_prime_int.mp hp

private theorem normWeight_le_degree {p : ℕ} (hp : p.Prime) (j : ℕ) :
    normWeight K p j ≤ Module.finrank ℚ K := by
  letI : (rationalPrimeIdeal p).IsPrime := rationalPrimeIdeal_isPrime hp
  letI : (rationalPrimeIdeal p).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ (rationalPrimeIdeal_ne_bot hp)
  have hsum := Ideal.sum_ramification_inertia (𝓞 K) ℚ K (rationalPrimeIdeal_ne_bot hp)
  calc
    normWeight K p j ≤ ∑ P ∈ primesAbove K p, P.inertiaDeg ℤ := by
      exact Finset.sum_le_sum fun P _ => by split_ifs <;> omega
    _ ≤ ∑ P ∈ primesAbove K p,
        Ideal.ramificationIdx' (rationalPrimeIdeal p) P *
          Ideal.inertiaDeg' (rationalPrimeIdeal p) P := by
      apply Finset.sum_le_sum
      intro P hP
      obtain ⟨hprime, hover⟩ :=
        (IsDedekindDomain.mem_primesOverFinset_iff (rationalPrimeIdeal_ne_bot hp) (𝓞 K)).mp hP
      letI : P.IsPrime := hprime
      letI : P.LiesOver (rationalPrimeIdeal p) := hover
      letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P (rationalPrimeIdeal p)
      rw [Ideal.inertiaDeg'_eq_inertiaDeg]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero
        (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P (rationalPrimeIdeal_ne_bot hp)))
    _ = Module.finrank ℚ K := hsum

private theorem residueFactorialIdeal_norm (H n : ℕ) :
    (residueFactorialIdeal K H n).absNorm = weightedValue H (normWeight K) n := by
  classical
  unfold residueFactorialIdeal weightedValue weightedExponent normWeight
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  letI : (rationalPrimeIdeal p).IsPrime := rationalPrimeIdeal_isPrime hpprime
  letI : (rationalPrimeIdeal p).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ (rationalPrimeIdeal_ne_bot hpprime)
  rw [map_prod]
  calc
    _ = ∏ P ∈ primesAbove K p,
        p ^ (P.inertiaDeg ℤ * (∑ j ∈ range (H + 1),
          if P.inertiaDeg ℤ ∣ j + 1 then n / p ^ (j + 1) else 0)) := by
      apply Finset.prod_congr rfl
      intro P hP
      obtain ⟨hprime, hover⟩ :=
        (IsDedekindDomain.mem_primesOverFinset_iff (rationalPrimeIdeal_ne_bot hpprime) (𝓞 K)).mp hP
      letI : P.IsPrime := hprime
      letI : P.LiesOver (rationalPrimeIdeal p) := hover
      letI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
        simpa only [rationalPrimeIdeal] using hover
      rw [map_pow, ← Ideal.pow_inertiaDeg p P, pow_mul]
    _ = p ^ (∑ P ∈ primesAbove K p, P.inertiaDeg ℤ *
        (∑ j ∈ range (H + 1), if P.inertiaDeg ℤ ∣ j + 1 then n / p ^ (j + 1) else 0)) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ = _ := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      split_ifs <;> simp

private theorem residueFactorialIdeal_eq_normEuler (H n : ℕ) (hn : n ≤ H) :
    residueFactorialIdeal K H n =
      ∏ p ∈ Nat.primesLE H, ∏ P ∈ primesAbove K p,
        P ^ (∑ j ∈ range (H + 1), n / P.absNorm ^ (j + 1)) := by
  classical
  unfold residueFactorialIdeal
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime := (Nat.mem_primesLE.mp hp).2
  letI : (rationalPrimeIdeal p).IsPrime := rationalPrimeIdeal_isPrime hpprime
  letI : (rationalPrimeIdeal p).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ (rationalPrimeIdeal_ne_bot hpprime)
  apply Finset.prod_congr rfl
  intro P hP
  obtain ⟨hprime, hover⟩ :=
    (IsDedekindDomain.mem_primesOverFinset_iff (rationalPrimeIdeal_ne_bot hpprime) (𝓞 K)).mp hP
  letI : P.IsPrime := hprime
  letI : P.LiesOver (rationalPrimeIdeal p) := hover
  letI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa only [rationalPrimeIdeal] using hover
  rw [← Ideal.pow_inertiaDeg p P]
  exact congrArg (P ^ ·) (residue_power_reindex hpprime (P.inertiaDeg_pos ℤ) hn).symm

private theorem residueFactorialIdeal_cutoff (H n : ℕ) (hn : n ≤ H) :
    residueFactorialIdeal K H n = residueFactorialIdeal K n n := by
  classical
  have hsub : Nat.primesLE n ⊆ Nat.primesLE H := by
    intro p hp
    obtain ⟨hpn, hpprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpn.trans hn, hpprime⟩
  have hsum (p : ℕ) (hp : p.Prime) (f : ℕ) :
      (∑ j ∈ range (H + 1), if f ∣ j + 1 then n / p ^ (j + 1) else 0) =
        ∑ j ∈ range (n + 1), if f ∣ j + 1 then n / p ^ (j + 1) else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hnot
    have hjn : n + 1 ≤ j := by simpa using hnot
    have hpow : j + 1 < p ^ (j + 1) := Nat.lt_pow_self hp.one_lt
    have hz : n / p ^ (j + 1) = 0 := Nat.div_eq_of_lt (by omega)
    simp [hz]
  unfold residueFactorialIdeal
  calc
    _ = ∏ p ∈ Nat.primesLE H, ∏ P ∈ primesAbove K p,
        P ^ (∑ j ∈ range (n + 1), if P.inertiaDeg ℤ ∣ j + 1 then n / p ^ (j + 1) else 0) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact Finset.prod_congr rfl fun P _ =>
        congrArg (P ^ ·) (hsum p (Nat.mem_primesLE.mp hp).2 _)
    _ = _ := by
      symm
      apply Finset.prod_subset hsub
      intro p hp hnot
      have hnp : n < p := by
        have hpprime := (Nat.mem_primesLE.mp hp).2
        by_contra h
        exact hnot (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
      apply Finset.prod_eq_one
      intro P _
      have hz : ∀ j : ℕ, n / p ^ (j + 1) = 0 := by
        intro j
        have hpprime := (Nat.mem_primesLE.mp hp).2
        have hle : p ≤ p ^ (j + 1) := by
          rw [pow_succ']
          exact Nat.le_mul_of_pos_right _ (pow_pos hpprime.pos _)
        exact Nat.div_eq_of_lt (hnp.trans_le hle)
      simp [hz]

private theorem fullRingFactorialIdeal_eq_residue (H n : ℕ) (hn : n ≤ H) :
    fullRingFactorialIdeal K n = residueFactorialIdeal K H n := by
  rw [residueFactorialIdeal_cutoff K H n hn,
    residueFactorialIdeal_eq_normEuler K n n (Nat.le_refl n)]
  rfl

private theorem fullRingFactorialIdeal_norm (H n : ℕ) (hn : n ≤ H) :
    (fullRingFactorialIdeal K n).absNorm = weightedValue H (normWeight K) n := by
  rw [fullRingFactorialIdeal_eq_residue K n n (Nat.le_refl n), residueFactorialIdeal_norm]
  exact (weightedValue_cutoff H n (normWeight K) hn).symm

private theorem weight_complement (H : ℕ) (p : ℕ) (hp : p ∈ Nat.primesLE H) (j : ℕ) :
    normWeight K p j + (Module.finrank ℚ K - normWeight K p j) = Module.finrank ℚ K :=
  Nat.add_sub_of_le (normWeight_le_degree K (Nat.mem_primesLE.mp hp).2 j)

private theorem norm_times_complement (H n : ℕ) (hn : n ≤ H) :
    (residueFactorialIdeal K H n).absNorm *
        weightedValue H (fun p j => Module.finrank ℚ K - normWeight K p j) n =
      (n !) ^ Module.finrank ℚ K := by
  rw [residueFactorialIdeal_norm, weightedValue_add]
  rw [← weightedValue_constant H n (Module.finrank ℚ K) hn]
  unfold weightedValue weightedExponent
  apply Finset.prod_congr rfl
  intro p hp
  congr 1
  exact Finset.sum_congr rfl fun j _ => congrArg (· * (n / p ^ (j + 1)))
    (weight_complement K H p hp j)

private theorem complement_eq_weightedValue (H n : ℕ) (hn : n ≤ H) :
    normComplement K n =
      weightedValue H (fun p j => Module.finrank ℚ K - normWeight K p j) n := by
  unfold normComplement
  rw [fullRingFactorialIdeal_eq_residue K H n hn,
    ← norm_times_complement K H n hn, residueFactorialIdeal_norm]
  exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (weightedValue_ne_zero _ _ _))

/-- Full-ring Euler factorial ideals, their integral complements, and both composition gcds. -/
public theorem number_field_norm_and_complement (H M : ℕ) (hMH : M ≤ H) :
    (∀ p : ℕ, p.Prime → ∀ j : ℕ, normWeight K p j ≤ Module.finrank ℚ K) ∧
    (∀ n ≤ H, fullRingFactorialIdeal K n = residueFactorialIdeal K H n) ∧
    (∀ n ≤ H, (fullRingFactorialIdeal K n).absNorm * normComplement K n =
      (n !) ^ Module.finrank ℚ K) ∧
    (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
        (fun a => ∏ i, (fullRingFactorialIdeal K (a i)).absNorm) =
      weightedTail H M (normWeight K) ∧
    (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
        (fun a => ∏ i, normComplement K (a i)) =
      weightedTail H M (fun p j => Module.finrank ℚ K - normWeight K p j) ∧
    weightedTail H M (normWeight K) *
        weightedTail H M (fun p j => Module.finrank ℚ K - normWeight K p j) =
      (tailLCM H M) ^ Module.finrank ℚ K := by
  classical
  refine ⟨fun p hp j => normWeight_le_degree K hp j,
    fun n hn => fullRingFactorialIdeal_eq_residue K H n hn, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [fullRingFactorialIdeal_eq_residue K H n hn, complement_eq_weightedValue K H n hn]
    exact norm_times_complement K H n hn
  · calc
      _ = (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
          (weightedProduct H (normWeight K)) := by
        apply Finset.gcd_congr rfl
        intro a ha
        apply Finset.prod_congr rfl
        intro i _
        exact fullRingFactorialIdeal_norm K H (a i)
          (part_le_head hMH a (Finset.Nat.mem_antidiagonalTuple.mp ha) i)
      _ = _ := weighted_composition_gcd H M hMH (normWeight K)
  · calc
      _ = (Finset.Nat.antidiagonalTuple (M + 1) (H - M)).gcd
          (weightedProduct H (fun p j => Module.finrank ℚ K - normWeight K p j)) := by
        apply Finset.gcd_congr rfl
        intro a ha
        apply Finset.prod_congr rfl
        intro i _
        exact complement_eq_weightedValue K H (a i)
          (part_le_head hMH a (Finset.Nat.mem_antidiagonalTuple.mp ha) i)
      _ = _ := weighted_composition_gcd H M hMH _
  · rw [weightedTail_add, ← weightedTail_constant H M (Module.finrank ℚ K)]
    unfold weightedTail
    apply Finset.prod_congr rfl
    intro p hp
    congr 1
    exact Finset.sum_congr rfl fun j _ => congrArg
      (· * floorMinimum H M (p ^ (j + 1))) (weight_complement K H p hp j)

end NumberFieldNorm

end D5.S3.Arith.FactorialRatio.Weighted.CompositionGcd
