/- GID: D5/S3/Arith/CyclotomicFiveResidueSum
   generality: G
   mirror-B: D5/B/S3/Arith/CyclotomicFiveResidueSum
   mirror-E: none(waiver:symbolic-arithmetic-no-numerical-evidence)
   anchors: []
   utility: none
   digest: Exact sums of units whose fifth cyclotomic value is a unit. -/

import D5.S3.Arith.ChineseRemainder
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.CyclotomicFiveResidueSum

def phi5 (u : ℕ) : ℕ := u ^ 4 + u ^ 3 + u ^ 2 + u + 1

def goodUnits (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter fun u => Nat.Coprime u n ∧ Nat.Coprime (phi5 u) n

private def admissible (n u : ℕ) : Prop := Nat.Coprime u n ∧ Nat.Coprime (phi5 u) n

private instance (n u : ℕ) : Decidable (admissible n u) :=
  inferInstanceAs (Decidable (Nat.Coprime u n ∧ Nat.Coprime (phi5 u) n))

private def residueSum (n : ℕ) : ℕ :=
  ∑ u ∈ Finset.range n, if admissible n u then u else 0

private theorem residueSum_eq (n : ℕ) : residueSum n = ∑ u ∈ goodUnits n, u := by
  rw [goodUnits, Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro u hu
    simp only [Finset.mem_Ico, Finset.mem_range] at *
    exact hu.2
  · intro u hu hnot
    have hu' := Finset.mem_range.mp hu
    have hn' : ¬(1 ≤ u ∧ u < n) := by simpa only [Finset.mem_Ico] using hnot
    have : u = 0 := by omega
    simp [this]

/-- The only zero of the fifth cyclotomic value modulo five is the class one. -/
theorem phi5_mod_five_eq_zero_iff (u : ℕ) : phi5 u % 5 = 0 ↔ u % 5 = 1 := by
  have h : u % 5 < 5 := Nat.mod_lt _ (by decide)
  have hm : phi5 u % 5 = phi5 (u % 5) % 5 := by
    simp [phi5, Nat.add_mod, Nat.pow_mod]
  rw [hm]
  interval_cases hmod : u % 5 <;> norm_num [phi5]

private theorem admissible_five_pow (a u : ℕ) :
    admissible (5 ^ (a + 1)) u ↔ 2 ≤ u % 5 := by
  have hp : Nat.Prime 5 := by decide
  simp only [admissible, Nat.coprime_pow_right_iff (Nat.succ_pos a)]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd,
    Nat.coprime_comm (n := phi5 u), hp.coprime_iff_not_dvd,
    Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, phi5_mod_five_eq_zero_iff]
  omega

private theorem block_sum (q : ℕ) :
    (∑ u ∈ Finset.range (5 * q), if 2 ≤ u % 5 then u else 0) =
      9 * q + 15 * ∑ j ∈ Finset.range q, j := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    norm_num [Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod]
    ring

/-- Exact representative sum for every positive power of five. -/
theorem sum_goodUnits_five_pow (a : ℕ) :
    (∑ u ∈ goodUnits (5 ^ (a + 1)), u) =
      9 * 5 ^ a + 15 * (5 ^ a * (5 ^ a - 1) / 2) := by
  rw [← residueSum_eq]
  simp_rw [residueSum, admissible_five_pow]
  rw [pow_succ', block_sum, Finset.sum_range_id]

private theorem scaled_sum_five_pow_not_dvd (a b : ℕ) (hb : ¬5 ∣ b) :
    ¬5 ^ (a + 1) ∣ b * ∑ u ∈ goodUnits (5 ^ (a + 1)), u := by
  let q := 5 ^ a
  have hq : 0 < q := pow_pos (by decide) _
  have hs : (∑ u ∈ goodUnits (5 ^ (a + 1)), u) =
      9 * q + 15 * ∑ j ∈ Finset.range q, j := by
    rw [sum_goodUnits_five_pow, Finset.sum_range_id]
  have hsum := Finset.sum_range_id_mul_two q
  have hid : 2 * (∑ u ∈ goodUnits (5 ^ (a + 1)), u) = q * (15 * q + 3) := by
    rw [hs]
    have : q - 1 + 1 = q := Nat.sub_add_cancel hq
    nlinarith
  intro h
  have hd : q * 5 ∣ q * (b * (15 * q + 3)) := by
    have hh := dvd_mul_of_dvd_right h 2
    rw [show 2 * (b * ∑ u ∈ goodUnits (5 ^ (a + 1)), u) =
      b * (2 * ∑ u ∈ goodUnits (5 ^ (a + 1)), u) by ring, hid] at hh
    simpa [q, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh
  have hd' := (Nat.mul_dvd_mul_iff_left hq).mp hd
  have h3 : 5 ∣ b * 3 := by
    have hm := Nat.mod_eq_zero_of_dvd hd'
    apply Nat.dvd_of_mod_eq_zero
    simpa [Nat.mul_mod, Nat.add_mod] using hm
  exact (show Nat.Prime 5 by decide).not_dvd_mul hb (by decide) h3

/-- The conjectured nonvanishing for the entire family of powers of five. -/
theorem residue_sum_five_pow_ne_zero (a : ℕ) :
    (∑ u ∈ goodUnits (5 ^ (a + 1)), u) % (5 ^ (a + 1)) ≠ 0 := by
  simpa using scaled_sum_five_pow_not_dvd a 1 (by decide) ∘ Nat.dvd_of_mod_eq_zero

private def cyclo {R : Type*} [Semiring R] (x : R) : R :=
  x ^ 4 + x ^ 3 + x ^ 2 + x + 1

private def good {R : Type*} [Semiring R] (x : R) : Prop :=
  IsUnit x ∧ IsUnit (cyclo x)

private theorem good_cast (n u : ℕ) : good (u : ZMod n) ↔ admissible n u := by
  unfold good cyclo admissible phi5
  rw [show (u : ZMod n) ^ 4 + (u : ZMod n) ^ 3 + (u : ZMod n) ^ 2 + u + 1 =
    ((u ^ 4 + u ^ 3 + u ^ 2 + u + 1 : ℕ) : ZMod n) by push_cast; rfl]
  simp only [ZMod.isUnit_iff_coprime]

/-- This count includes the unique residue modulo one, as required by CRT. -/
def residueCount (n : ℕ) : ℕ :=
  ∑ u ∈ Finset.range n, if admissible n u then 1 else 0

private theorem sum_zmod {M : Type*} [AddCommMonoid M] (n : ℕ) [NeZero n]
    (f : ℕ → M) : (∑ x : ZMod n, f x.val) = ∑ u ∈ Finset.range n, f u := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n + 1)

open Classical in
private theorem count_eq_zmod (n : ℕ) [NeZero n] :
    residueCount n = ∑ x : ZMod n, if good x then 1 else 0 := by
  classical
  rw [residueCount, ← sum_zmod]
  apply Finset.sum_congr rfl
  intro x _
  simp only [← good_cast, ZMod.natCast_zmod_val]

open Classical in
private theorem sum_eq_zmod (n : ℕ) [NeZero n] :
    (residueSum n : ZMod n) = ∑ x : ZMod n, if good x then x else 0 := by
  classical
  simp only [residueSum, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [← sum_zmod]
  apply Finset.sum_congr rfl
  intro x _
  simp only [← good_cast, ZMod.natCast_zmod_val]

private theorem good_crt (m n : ℕ) (h : Nat.Coprime m n) (x : ZMod (m * n)) :
    good x ↔ good ((ZMod.chineseRemainder h x).1) ∧
      good ((ZMod.chineseRemainder h x).2) := by
  let e := ZMod.chineseRemainder h
  have hc : e (cyclo x) = cyclo (e x) := by simp [cyclo]
  rw [good, ← MulEquiv.isUnit_map (f := e),
    ← MulEquiv.isUnit_map (f := e) (x := cyclo x), hc]
  simp only [Prod.isUnit_iff]
  change (IsUnit (e x).1 ∧ IsUnit (e x).2) ∧
    (IsUnit (cyclo (e x).1) ∧ IsUnit (cyclo (e x).2)) ↔
      (IsUnit (e x).1 ∧ IsUnit (cyclo (e x).1)) ∧
        (IsUnit (e x).2 ∧ IsUnit (cyclo (e x).2))
  tauto

/-- CRT multiplies the admissible counts, including the modulus-one endpoint. -/
theorem residueCount_mul (m n : ℕ) [NeZero m] [NeZero n] (h : Nat.Coprime m n) :
    residueCount (m * n) = residueCount m * residueCount n := by
  classical
  rw [count_eq_zmod, count_eq_zmod, count_eq_zmod]
  have hb := ChineseRemainder.chinese_remainder_bijective m n h
  change Function.Bijective (ZMod.chineseRemainder h) at hb
  rw [Fintype.sum_bijective _ hb _
    (fun x : ZMod m × ZMod n => if good x.1 ∧ good x.2 then (1 : ℕ) else 0)
    (fun x => by simp only [good_crt m n h x])]
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ x : ZMod m, ∀ y : ZMod n,
    (if good x ∧ good y then (1 : ℕ) else 0) =
      (if good x then 1 else 0) * (if good y then 1 else 0) by
        intro x y; split_ifs <;> simp_all]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

/-- Projecting the sum through CRT gives each first-factor residue equal multiplicity. -/
theorem sum_goodUnits_mul_cast (m n : ℕ) [NeZero m] [NeZero n] (h : Nat.Coprime m n) :
    ((∑ u ∈ goodUnits (m * n), u : ℕ) : ZMod m) =
      residueCount n * ((∑ u ∈ goodUnits m, u : ℕ) : ZMod m) := by
  classical
  let e := ZMod.chineseRemainder h
  let f : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  have hs := congrArg f (sum_eq_zmod (m * n))
  simp only [map_natCast, map_sum, apply_ite, map_zero] at hs
  rw [← residueSum_eq, ← residueSum_eq, hs, sum_eq_zmod]
  have hc : (residueCount n : ZMod m) =
      ∑ y : ZMod n, if good y then 1 else 0 := by
    rw [count_eq_zmod]
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hc]
  have hb := ChineseRemainder.chinese_remainder_bijective m n h
  change Function.Bijective e at hb
  rw [Fintype.sum_bijective _ hb _
    (fun x : ZMod m × ZMod n => if good x.1 ∧ good x.2 then x.1 else 0)
    (fun x => by simp only [good_crt m n h x]; rfl)]
  rw [Fintype.sum_prod_type]
  have hi (x : ZMod m) (y : ZMod n) :
      (if good x ∧ good y then x else 0) =
        (if good x then x else 0) * (if good y then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hi]
  rw [mul_comm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

private theorem admissible_period (p k u : ℕ) :
    admissible p (p * k + u) ↔ admissible p u := by
  rw [← good_cast, ← good_cast]
  simp

private theorem count_blocks (p k : ℕ) :
    (∑ u ∈ Finset.range (p * k), if admissible p u then 1 else 0) =
      k * residueCount p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [admissible_period]
    change k * residueCount p + residueCount p = (k + 1) * residueCount p
    ring

/-- Every admissible residue modulo a prime has equally many lifts to each positive power. -/
theorem residueCount_pow (p a : ℕ) :
    residueCount (p ^ (a + 1)) = p ^ a * residueCount p := by
  unfold residueCount
  simp only [admissible, Nat.coprime_pow_right_iff (Nat.succ_pos a)]
  change (∑ u ∈ Finset.range (p ^ (a + 1)), if admissible p u then 1 else 0) = _
  rw [pow_succ', count_blocks]
  rfl

open Classical in
private theorem fifth_roots_count (p : ℕ) [Fact p.Prime] :
    (∑ x : ZMod p, if x ^ 5 = 1 then (1 : ℕ) else 0) = (p - 1).gcd 5 := by
  classical
  let K := (powMonoidHom 5 : (ZMod p)ˣ →* (ZMod p)ˣ).ker
  let f : K → {x : ZMod p // x ^ 5 = 1} := fun u =>
    ⟨u.val.val, by
      have h : u.val ^ 5 = 1 := u.property
      exact congrArg Units.val h⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Units.ext
      exact congrArg Subtype.val hxy
    · intro x
      have hx : x.val ≠ 0 := by
        intro hh
        have := x.property
        simp [hh] at this
      refine ⟨⟨Units.mk0 x.val hx, ?_⟩, ?_⟩
      · change (Units.mk0 x.val hx) ^ 5 = 1
        apply Units.ext
        exact x.property
      · apply Subtype.ext
        rfl
  calc
    _ = Fintype.card {x : ZMod p // x ^ 5 = 1} := by
      simp [Fintype.card_subtype]
    _ = Nat.card K := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm
    _ = (p - 1).gcd 5 := by
      rw [IsCyclic.card_powMonoidHom_ker]
      simp only [Nat.card_eq_fintype_card, ZMod.card_units]

private theorem prime_count_balance (p : ℕ) [Fact p.Prime] (hp5 : p ≠ 5) :
    residueCount p + (p - 1).gcd 5 = p := by
  classical
  have hp : Nat.Prime p := Fact.out
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp hz
    exact hp5 ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd |>.resolve_left hp.ne_one)
  have hi (x : ZMod p) :
      (if good x then (1 : ℕ) else 0) + (if x ^ 5 = 1 then 1 else 0) +
        (if x = 0 then 1 else 0) = 1 + (if x = 1 then 1 else 0) := by
    have hmul : (x - 1) * cyclo x = x ^ 5 - 1 := by unfold cyclo; ring
    by_cases hx0 : x = 0
    · subst x
      norm_num [good, cyclo]
    by_cases hx1 : x = 1
    · subst x
      norm_num [good, cyclo, isUnit_iff_ne_zero, h5]
    have hr : x ^ 5 = 1 ↔ cyclo x = 0 := by
      rw [← sub_eq_zero, ← hmul, mul_eq_zero]
      simp [sub_eq_zero, hx1]
    by_cases hc : cyclo x = 0 <;> simp [good, isUnit_iff_ne_zero, hx0, hx1, hr, hc]
  have hsum := congrArg (fun f : ZMod p → ℕ => ∑ x, f x) (funext hi)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  rw [← count_eq_zmod, fifth_roots_count] at hsum
  omega

/-- For a prime other than five, the admissible count is prime minus the root-kernel size. -/
theorem residueCount_prime (p : ℕ) [Fact p.Prime] (hp5 : p ≠ 5) :
    residueCount p = p - (p - 1).gcd 5 := by
  have := prime_count_balance p hp5
  omega

private theorem prime_count_not_dvd (p : ℕ) [Fact p.Prime] (hp5 : p ≠ 5) :
    ¬5 ∣ residueCount p := by
  have hp : Nat.Prime p := Fact.out
  have h := prime_count_balance p hp5
  have hg : (p - 1).gcd 5 ∣ 5 := Nat.gcd_dvd_right _ _
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hg with hg | hg
  · rw [hg] at h
    intro hd
    have hg1 : (p - 1).gcd 5 = 1 := hg
    have he : p - 1 = residueCount p := by omega
    have hc : 5 ∣ (p - 1).gcd 5 := Nat.dvd_gcd (he ▸ hd) dvd_rfl
    rw [hg1] at hc
    norm_num at hc
  · rw [hg] at h
    intro hd
    have hpdiv : 5 ∣ p := h ▸ dvd_add hd (dvd_refl 5)
    exact hp5 (((Nat.dvd_prime hp).mp hpdiv).resolve_left (by decide)).symm

/-- The CRT-compatible count is never divisible by five away from multiples of five. -/
theorem residueCount_not_dvd_five (m : ℕ) (hm : ¬5 ∣ m) : ¬5 ∣ residueCount m := by
  revert hm
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp [residueCount, admissible, phi5]
  | prime_pow p e hp he =>
      intro hnot
      obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
      have : Fact p.Prime := ⟨hp⟩
      have hp5 : p ≠ 5 := by
        rintro rfl
        exact hnot (dvd_pow_self 5 (Nat.succ_ne_zero _))
      rw [residueCount_pow]
      apply (show Nat.Prime 5 by decide).not_dvd_mul
      · intro hd
        exact hnot (dvd_mul_of_dvd_left hd p)
      · exact prime_count_not_dvd p hp5
  | coprime a b ha hb hab iha ihb =>
      intro hnot
      have : NeZero a := ⟨by omega⟩
      have : NeZero b := ⟨by omega⟩
      rw [residueCount_mul a b hab]
      exact (show Nat.Prime 5 by decide).not_dvd_mul
        (iha fun h => hnot (dvd_mul_of_dvd_left h b))
        (ihb fun h => hnot (dvd_mul_of_dvd_right h a))

/-- Robert Israel's A290322 conjecture: a multiple of five has nonzero residue sum. -/
theorem residue_sum_ne_zero (n : ℕ) (hn : 2 ≤ n) (h5 : 5 ∣ n) :
    (∑ u ∈ goodUnits n, u) % n ≠ 0 := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 5 (by decide)
  cases e with
  | zero => simp only [pow_zero, one_mul] at he; exact (hm (he ▸ h5)).elim
  | succ a =>
      subst n
      have : NeZero m := ⟨by intro hz; exact hm (hz ▸ dvd_zero 5)⟩
      have hcop : Nat.Coprime (5 ^ (a + 1)) m :=
        ((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr hm).pow_left _
      have hc := sum_goodUnits_mul_cast (5 ^ (a + 1)) m hcop
      intro hz
      have hd : 5 ^ (a + 1) ∣ ∑ u ∈ goodUnits (5 ^ (a + 1) * m), u :=
        dvd_trans (dvd_mul_right _ _) (Nat.dvd_of_mod_eq_zero hz)
      have hzero := (ZMod.natCast_eq_zero_iff _ (5 ^ (a + 1))).mpr hd
      rw [hzero] at hc
      have hbad : 5 ^ (a + 1) ∣
          residueCount m * ∑ u ∈ goodUnits (5 ^ (a + 1)), u := by
        apply (ZMod.natCast_eq_zero_iff _ _).mp
        simpa only [Nat.cast_mul] using hc.symm
      exact scaled_sum_five_pow_not_dvd a (residueCount m)
        (residueCount_not_dvd_five m hm) hbad

#print axioms phi5_mod_five_eq_zero_iff
#print axioms sum_goodUnits_five_pow
#print axioms residue_sum_five_pow_ne_zero
#print axioms residueCount_mul
#print axioms sum_goodUnits_mul_cast
#print axioms residueCount_pow
#print axioms residueCount_prime
#print axioms residueCount_not_dvd_five
#print axioms residue_sum_ne_zero

end D5.S3.Arith.CyclotomicFiveResidueSum
