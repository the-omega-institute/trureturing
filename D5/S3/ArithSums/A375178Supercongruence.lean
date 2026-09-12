/- GID: D5/S3/ArithSums/A375178Supercongruence
   generality: G
   mirror-B: D5/B/S3/ArithSums/A375178Supercongruence
   mirror-E: none(waiver:universal-congruence-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.FieldTheory.Finite.Basic]
   utility: none
   digest: The A375178 binomial cube sum is 1 modulo the fifth power of every prime at least 7. -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset
namespace D5.S3.ArithSums.A375178Supercongruence

/-- OEIS A375178, including its initial zero. -/
def a (n : ℕ) : ℕ := ∑ k ∈ range n, (Nat.choose (n + k - 1) k) ^ 3

private lemma prod_first_order {R : Type*} [CommRing R] {ι : Type*}
    (s : Finset ι) (t : R) (f : ι → R) :
    ∃ r : R, (∏ i ∈ s, (1 + t * f i)) = 1 + t * ∑ i ∈ s, f i + t ^ 2 * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨r + f i * (∑ j ∈ s, f j) + t * f i * r, ?_⟩
    rw [prod_insert hi, sum_insert hi, hr]
    ring

private lemma sum_inverse_pow (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : r < p - 1) :
    ∑ x : ZMod p, x⁻¹ ^ r = 0 := by
  rw [← Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun x => x ^ r) (fun x => x⁻¹ ^ r)]
  · exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) r (by simpa using hr)
  · intro x
    simp

private lemma sum_cast_range {M : Type*} [AddCommMonoid M] (p : ℕ) [NeZero p]
    (f : ZMod p → M) : ∑ k ∈ range p, f k = ∑ x : ZMod p, f x := by
  apply Finset.sum_bij (fun (k : ℕ) _ => (k : ZMod p))
  · simp
  · intro a ha b hb hab
    have := congrArg ZMod.val hab
    simpa [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using this
  · intro b _
    exact ⟨b.val, mem_range.mpr b.val_lt, ZMod.natCast_zmod_val b⟩
  · simp


private def doubleH (p a b : ℕ) [NeZero p] : ZMod p :=
  ∑ x : ZMod p, ∑ y : ZMod p, if x.val < y.val then x⁻¹ ^ a * y⁻¹ ^ b else 0

private lemma doubleH_reverse (p : ℕ) [Fact p.Prime] :
    doubleH p 1 3 = doubleH p 3 1 := by
  unfold doubleH
  rw [sum_comm]
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro x
  apply Fintype.sum_equiv (Equiv.neg (ZMod p))
  intro y
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hvx := x.val_lt
  have hvy := y.val_lt
  have hc : y.val < x.val ↔ p - x.val < p - y.val := by omega
  simp only [Equiv.neg_apply, ZMod.neg_val, hx, hy, if_false, ← hc,
    inv_neg, pow_one]
  split_ifs <;> ring

private lemma doubleH_shuffle (p : ℕ) [Fact p.Prime] :
    (∑ x : ZMod p, x⁻¹) * (∑ x : ZMod p, x⁻¹ ^ 3) =
      doubleH p 1 3 + doubleH p 3 1 + ∑ x : ZMod p, x⁻¹ ^ 4 := by
  unfold doubleH
  rw [Fintype.sum_mul_sum]
  have hr :
      (∑ x : ZMod p, ∑ y : ZMod p, if x.val < y.val then x⁻¹ ^ 3 * y⁻¹ else 0) =
      ∑ x : ZMod p, ∑ y : ZMod p, if y.val < x.val then x⁻¹ * y⁻¹ ^ 3 else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y _
    split_ifs <;> ring
  simp only [pow_one]
  rw [hr, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  have hd : x⁻¹ ^ 4 =
      ∑ y : ZMod p, if x = y then x⁻¹ * y⁻¹ ^ 3 else 0 := by simp [pow_succ, mul_assoc]
  rw [hd, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro y _
  have he : x.val = y.val ↔ x = y := ⟨fun h => by simpa only [ZMod.natCast_zmod_val] using congrArg (fun n : ℕ => (n : ZMod p)) h, congrArg ZMod.val⟩
  split_ifs <;> simp_all <;> omega

-- Reversal identifies H(1,3) and H(3,1); shuffle then cancels their sum.
private lemma doubleH_zero (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    doubleH p 1 3 = 0 := by
  have h1 := sum_inverse_pow p 1 (by omega)
  have h4 := sum_inverse_pow p 4 (by omega)
  have hs := doubleH_shuffle p
  simp only [pow_one] at h1
  rw [h1, zero_mul, h4, add_zero, ← doubleH_reverse p] at hs
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have : (2 : ZMod p) * doubleH p 1 3 = 0 := by linear_combination -hs
  exact (mul_eq_zero.mp this).resolve_left htwo


private abbrev R (p : ℕ) := ZMod (p ^ 5)
private def red (p : ℕ) : R p →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide)) (ZMod p)

private lemma p_fifth_zero (p : ℕ) : (p : R p) ^ 5 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

private lemma lift_zero (p : ℕ) [Fact p.Prime] (x : R p) (hx : red p x = 0) :
    (p : R p) ^ 4 * x = 0 := by
  have hv : p ∣ x.val := by
    apply (ZMod.natCast_eq_zero_iff x.val p).mp
    have h := congrArg (red p) (ZMod.natCast_zmod_val x)
    simpa only [map_natCast, hx] using h
  obtain ⟨v, hv⟩ := hv
  have he : x = (p : R p) * v := by
    rw [← ZMod.natCast_zmod_val x, hv, Nat.cast_mul]
  rw [he, ← mul_assoc, ← pow_succ, p_fifth_zero, zero_mul]

private lemma unit_inv (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0 < k) (hkp : k < p) :
    (k : R p) * (k : R p)⁻¹ = 1 := by
  apply ZMod.coe_mul_inv_eq_one
  apply Nat.Coprime.pow_right
  apply Nat.Coprime.symm
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
    (Nat.not_dvd_of_pos_of_lt hk hkp)

private lemma red_inv (p : ℕ) [Fact p.Prime] (k : ℕ) (hkp : k < p) :
    red p (k : R p)⁻¹ = (k : ZMod p)⁻¹ := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.cast_zero, ZMod.inv_zero, map_zero, inv_zero]
  have h := congrArg (red p) (unit_inv p k (by omega) hkp)
  have he : (k : ZMod p) * red p (k : R p)⁻¹ = 1 := by simpa using h
  exact (inv_eq_of_mul_eq_one_right he).symm

private lemma lifted_power_sum (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : r < p - 1) :
    (p : R p) ^ 4 * ∑ k ∈ range p, (k : R p)⁻¹ ^ r = 0 := by
  apply lift_zero
  simp only [map_sum, map_pow]
  have h : (∑ k ∈ range p, red p (k : R p)⁻¹ ^ r) =
      ∑ k ∈ range p, (k : ZMod p)⁻¹ ^ r := by
    apply sum_congr rfl
    intro k hk
    rw [red_inv p k (mem_range.mp hk)]
  rw [h, sum_cast_range p (fun x : ZMod p => x⁻¹ ^ r), sum_inverse_pow p r hr]

private lemma paired_cube {R : Type*} [CommRing R] (t x y : R)
    (ht : t ^ 5 = 0) (hxy : x + y = t * x * y) :
    t ^ 3 * (x ^ 3 + y ^ 3) = -3 * t ^ 4 * x ^ 4 := by
  have hkill : t ^ 4 * (x + y) = 0 := by
    calc
      _ = t ^ 5 * (x * y) := by rw [hxy]; ring
      _ = 0 := by rw [ht, zero_mul]
  linear_combination
    t ^ 3 * (x ^ 2 - x * y + y ^ 2) * hxy +
      (x * y ^ 2 - 2 * x ^ 2 * y + 3 * x ^ 3) * hkill


private lemma sum_range_remove_zero (p : ℕ) [Fact p.Prime] (f : ℕ → R p) (h0 : f 0 = 0) :
    ∑ k ∈ range p, f k = ∑ k ∈ Ico 1 p, f k := by
  rw [sum_Ico_eq_sub f (Nat.Prime.one_lt (Fact.out : p.Prime)).le]
  simp [h0]

-- Pair k with p-k and use the fourth-power sum modulo p.
private lemma cubic_harmonic_lift (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (p : R p) ^ 3 * ∑ k ∈ range p, (k : R p)⁻¹ ^ 3 = 0 := by
  let t : R p := p
  let f : ℕ → R p := fun k => (k : R p)⁻¹ ^ 3
  have hpair (k : ℕ) (hk : k ∈ Ico 1 p) :
      t ^ 3 * (f k + f (p-k)) = -3 * t ^ 4 * (k : R p)⁻¹ ^ 4 := by
    have hks := mem_Ico.mp hk
    have hu := unit_inv p k (by omega) hks.2
    have hv := unit_inv p (p-k) (by omega) (by omega)
    have hxy : (k : R p)⁻¹ + ((p-k : ℕ) : R p)⁻¹ =
        t * (k : R p)⁻¹ * ((p-k : ℕ) : R p)⁻¹ := by
      rw [Nat.cast_sub (by omega : k ≤ p)] at hv ⊢
      dsimp [t]
      linear_combination -((p : R p) - k)⁻¹ * hu - (k : R p)⁻¹ * hv
    exact paired_cube t _ _ (p_fifth_zero p) hxy
  have href : ∑ k ∈ Ico 1 p, f (p-k) = ∑ k ∈ Ico 1 p, f k := by
    simpa using (sum_Ico_reflect f 1 (n := p) (m := p) (by omega))
  have he := sum_congr rfl hpair
  rw [← mul_sum, sum_add_distrib, href, ← mul_sum] at he
  have h4 := lifted_power_sum p 4 (by omega)
  rw [sum_range_remove_zero p (fun k => (k : R p)⁻¹ ^ 4)
    (by simp [ZMod.inv_zero])] at h4
  have hzero : t ^ 3 * ∑ k ∈ Ico 1 p, f k = 0 := by
    have hz : (2 : R p) * (t ^ 3 * ∑ k ∈ Ico 1 p, f k) = 0 := by
      dsimp [t] at he ⊢
      linear_combination he - 3 * h4
    have hi := unit_inv p 2 (by omega) (by omega)
    norm_num only [Nat.cast_ofNat] at hi
    calc
      _ = (2 : R p)⁻¹ * ((2 : R p) * (t ^ 3 * ∑ k ∈ Ico 1 p, f k)) := by
        rw [← mul_assoc, mul_comm (2 : R p)⁻¹, hi, one_mul]
      _ = 0 := by rw [hz, mul_zero]
  rw [sum_range_remove_zero p (fun k => (k : R p)⁻¹ ^ 3)
    (by simp [ZMod.inv_zero])]
  exact hzero


private lemma sum_val_lt (p : ℕ) [Fact p.Prime] (k : ℕ) (hkp : k < p)
    (f : ZMod p → ZMod p) :
    (∑ x : ZMod p, if x.val < k then f x else 0) = ∑ j ∈ range k, f j := by
  rw [← sum_cast_range p (fun x => if x.val < k then f x else 0)]
  calc
    _ = ∑ j ∈ range p, if j < k then f j else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [ZMod.val_natCast_of_lt (mem_range.mp hj)]
    _ = ∑ j ∈ range k, if j < k then f j else 0 := by
      symm
      apply sum_subset (range_mono hkp.le)
      intro j hj hjk
      simp_all
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      simp [mem_range.mp hj]

private lemma doubleH_eq_nested (p : ℕ) [Fact p.Prime] :
    doubleH p 1 3 =
      ∑ k ∈ range p, (k : ZMod p)⁻¹ ^ 3 * ∑ j ∈ range k, (j : ZMod p)⁻¹ := by
  unfold doubleH
  rw [sum_comm, ← sum_cast_range p]
  apply sum_congr rfl
  intro k hk
  rw [ZMod.val_natCast_of_lt (mem_range.mp hk), sum_val_lt p k (mem_range.mp hk)]
  simp only [pow_one, mul_sum, mul_comm]

private lemma lifted_doubleH (p : ℕ) [Fact p.Prime] (hp : 7 ≤ p) :
    (p : R p) ^ 4 *
      (∑ k ∈ range p, (k : R p)⁻¹ ^ 3 * ∑ j ∈ range k, (j : R p)⁻¹) = 0 := by
  apply lift_zero
  simp only [map_sum, map_mul, map_pow]
  have he :
      (∑ k ∈ range p, red p (k : R p)⁻¹ ^ 3 * ∑ j ∈ range k, red p (j : R p)⁻¹) =
      ∑ k ∈ range p, (k : ZMod p)⁻¹ ^ 3 * ∑ j ∈ range k, (j : ZMod p)⁻¹ := by
    apply sum_congr rfl
    intro k hk
    rw [red_inv p k (mem_range.mp hk)]
    congr 1
    apply sum_congr rfl
    intro j hj
    exact red_inv p j (lt_trans (mem_range.mp hj) (mem_range.mp hk))
  rw [he, ← doubleH_eq_nested, doubleH_zero p hp]


private lemma binomial_product (p : ℕ) [Fact p.Prime] :
    ∀ k : ℕ, 0 < k → k < p →
      (Nat.choose (p + k - 1) k : R p) =
        (p : R p) * (k : R p)⁻¹ * ∏ j ∈ range k, (1 + (p : R p) * (j : R p)⁻¹) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk hkp
    by_cases hz : k = 0
    · subst k
      simp [ZMod.inv_zero]
    have hprev := ih (by omega) (by omega)
    have hp0 := (Fact.out : p.Prime).pos
    have hrec := Nat.add_one_mul_choose_eq (p+k-1) k
    rw [show p+k-1+1 = p+k by omega] at hrec
    have hc : ((p : R p) + k) * (Nat.choose (p+k-1) k : R p) =
        (Nat.choose (p+k) (k+1) : R p) * ((k : R p)+1) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using congrArg (fun n : ℕ => (n : R p)) hrec
    have hi := unit_inv p (k+1) (by omega) hkp
    have hj := unit_inv p k (by omega) (by omega)
    push_cast at hi
    rw [show p + (k+1)-1 = p+k by omega, prod_range_succ]
    push_cast
    calc
      _ = ((k : R p)+1)⁻¹ * (((p : R p)+k) * (Nat.choose (p+k-1) k : R p)) := by
        rw [hc]
        linear_combination -(Nat.choose (p+k) (k+1) : R p) * hi
      _ = _ := by
        rw [hprev]
        linear_combination
          (p : R p) * ((k : R p)+1)⁻¹ *
            (∏ j ∈ range k, (1 + (p : R p) * (j : R p)⁻¹)) * hj

private lemma scaled_cube_expansion {S : Type*} [CommRing S] (t x h r : S) (ht : t ^ 5 = 0) :
    (t * x * (1 + t * h + t ^ 2 * r)) ^ 3 = t ^ 3 * x ^ 3 + 3 * t ^ 4 * x ^ 3 * h := by
  have he : t ^ 5 ∣
      (t * x * (1 + t * h + t ^ 2 * r)) ^ 3 - (t ^ 3 * x ^ 3 + 3 * t ^ 4 * x ^ 3 * h) := by
    refine ⟨x ^ 3 * (3*r + 3*h^2 + t*(6*h*r+h^3) + t^2*(3*r^2+3*h^2*r) +
      t^3*3*h*r^2 + t^4*r^3), ?_⟩
    ring
  rw [ht, zero_dvd_iff, sub_eq_zero] at he
  exact he

private lemma binomial_cube_expansion (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 0 < k) (hkp : k < p) :
    (Nat.choose (p+k-1) k : R p) ^ 3 =
      (p : R p) ^ 3 * (k : R p)⁻¹ ^ 3 +
        3 * (p : R p) ^ 4 * (k : R p)⁻¹ ^ 3 * ∑ j ∈ range k, (j : R p)⁻¹ := by
  rw [binomial_product p k hk hkp]
  obtain ⟨r, hr⟩ := prod_first_order (range k) (p : R p) (fun j : ℕ => (j : R p)⁻¹)
  rw [hr]
  exact scaled_cube_expansion _ _ _ _ (p_fifth_zero p)


/-- The fifth-power supercongruence conjectured in the OEIS entry. -/
theorem supercongruence (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    a p ≡ 1 [MOD p ^ 5] := by
  let : Fact p.Prime := ⟨hp⟩
  apply (ZMod.natCast_eq_natCast_iff (a p) 1 (p ^ 5)).mp
  simp only [Nat.cast_one]
  change (a p : R p) = 1
  unfold a
  push_cast
  have hsplit := sum_range_add_sum_Ico
    (fun k => (Nat.choose (p+k-1) k : R p) ^ 3) (by omega : 1 ≤ p)
  simp only [sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_pow] at hsplit
  rw [← hsplit]
  suffices (∑ k ∈ Ico 1 p, (Nat.choose (p+k-1) k : R p) ^ 3) = 0 by
    rw [this, add_zero]
  have he :
      (∑ k ∈ Ico 1 p, (Nat.choose (p+k-1) k : R p) ^ 3) =
      (p : R p) ^ 3 * (∑ k ∈ Ico 1 p, (k : R p)⁻¹ ^ 3) +
      3 * (p : R p) ^ 4 *
        (∑ k ∈ Ico 1 p, (k : R p)⁻¹ ^ 3 * ∑ j ∈ range k, (j : R p)⁻¹) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [binomial_cube_expansion p k (by have := (mem_Ico.mp hk).1; omega) (mem_Ico.mp hk).2]
    ring
  have h3 := cubic_harmonic_lift p hp7
  have h13 := lifted_doubleH p hp7
  rw [sum_range_remove_zero p _ (by simp [ZMod.inv_zero])] at h3
  rw [sum_range_remove_zero p _ (by simp [ZMod.inv_zero])] at h13
  rw [he, h3, zero_add, mul_assoc, h13, mul_zero]

end D5.S3.ArithSums.A375178Supercongruence
