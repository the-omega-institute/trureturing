/- GID: D5/S3/CharacterSums/PrimePowerKloostermanRootCount
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cardinality bounds for the unit roots in prime-power Kloosterman stationary phase. -/

import D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false

namespace D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase

noncomputable section

/-- The unit roots of the quadratic fiber with coefficients `a` and `b`. -/
def unitQuadraticRoots {q : ℕ} [NeZero q] (a : ZMod q) (b : (ZMod q)ˣ) :
    Finset (ZMod q)ˣ :=
  Finset.univ.filter fun x => a * (x : ZMod q) ^ 2 = (b : ZMod q)

private theorem mem_unitQuadraticRoots {q : ℕ} [NeZero q]
    {a : ZMod q} {b x : (ZMod q)ˣ} :
    x ∈ unitQuadraticRoots a b ↔ a * (x : ZMod q) ^ 2 = (b : ZMod q) := by
  simp only [unitQuadraticRoots, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem sq_eq_of_quadratic_eq {R : Type*} [CommMonoid R] {a b x y : R}
    (hb : IsUnit b) (hx : a * x ^ 2 = b) (hy : a * y ^ 2 = b) :
    x ^ 2 = y ^ 2 := by
  have ha : IsUnit a := isUnit_of_mul_isUnit_left (hy.symm ▸ hb)
  exact ha.mul_left_cancel (hx.trans hy.symm)

local instance primeNeZeroForRootCount {p : ℕ} [Fact p.Prime] : NeZero p :=
  ⟨(Fact.out : p.Prime).ne_zero⟩

private theorem eq_or_eq_neg_of_sq_eq_odd {p r : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hp : p ≠ 2) {x y : ZMod (p ^ r)} (hy : IsUnit y)
    (hsq : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have hprime : p.Prime := Fact.out
  let f : ZMod (p ^ r) →+* ZMod p := ZMod.castHom (dvd_pow_self p hr.ne') (ZMod p)
  have hunit (z : ZMod (p ^ r)) : IsUnit z ↔ f z ≠ 0 := by
    obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
    simp only [f, map_natCast, ZMod.isUnit_natCast_iff_not_dvd_pow hprime hr,
      ne_eq, ZMod.natCast_eq_zero_iff]
  have hprod : (x + y) * (x - y) = 0 := by rw [← sq_sub_sq, hsq, sub_self]
  by_cases hsub : f (x - y) = 0
  · have hadd : f (x + y) ≠ 0 := by
      intro h
      rw [map_sub, sub_eq_zero] at hsub
      rw [map_add, hsub] at h
      exact (hunit y).1 hy ((ZMod.add_self_eq_zero_iff_eq_zero
        (hprime.odd_of_ne_two hp)).1 h)
    have hu := (hunit (x + y)).2 hadd
    have hz : x - y = 0 := hu.mul_left_cancel (by simpa only [mul_zero] using hprod)
    exact Or.inl (sub_eq_zero.mp hz)
  · have hu := (hunit (x - y)).2 hsub
    have hz : x + y = 0 := hu.mul_right_cancel (by simpa only [zero_mul] using hprod)
    exact Or.inr (eq_neg_iff_add_eq_zero.mpr hz)

/-- A unit quadratic fiber at a positive power of an odd prime has at most two roots. -/
theorem card_unitQuadraticRoots_le_two {p r : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hp : p ≠ 2) (a : ZMod (p ^ r)) (b : (ZMod (p ^ r))ˣ) :
    (unitQuadraticRoots a b).card ≤ 2 := by
  rcases (unitQuadraticRoots a b).eq_empty_or_nonempty with hempty | ⟨y, hy⟩
  · simp [hempty]
  · refine (Finset.card_le_card_of_injOn
      (s := unitQuadraticRoots a b) (t := {(y : ZMod (p ^ r)), -(y : ZMod (p ^ r))})
      (fun x : (ZMod (p ^ r))ˣ => (x : ZMod (p ^ r))) ?_
      Units.val_injective.injOn).trans Finset.card_le_two
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    exact eq_or_eq_neg_of_sq_eq_odd hr hp y.isUnit
      (sq_eq_of_quadratic_eq b.isUnit (mem_unitQuadraticRoots.mp hx)
        (mem_unitQuadraticRoots.mp hy))

private theorem dvd_of_two_pow_dvd_twice_odd_mul {s : ℕ} {k z : ℤ}
    (hk : k % 2 = 1) (hd : (2 : ℤ) ^ (s + 1) ∣ (2 * k) * z) :
    (2 : ℤ) ^ s ∣ z := by
  have hcop : IsCoprime (2 : ℤ) k := ⟨-(k / 2), 1, by omega⟩
  rw [pow_succ, mul_comm ((2 : ℤ) ^ s) 2, mul_assoc] at hd
  have hdiv : (2 : ℤ) ^ s ∣ k * z :=
    Int.dvd_of_mul_dvd_mul_left (by decide : (2 : ℤ) ≠ 0) hd
  exact hcop.pow_left.dvd_of_dvd_mul_left hdiv

private theorem two_pow_dvd_sub_or_add {s : ℕ} {x y : ℤ}
    (hx : x % 2 = 1) (hy : y % 2 = 1)
    (hprod : (2 : ℤ) ^ (s + 1) ∣ (x + y) * (x - y)) :
    (2 : ℤ) ^ s ∣ x - y ∨ (2 : ℤ) ^ s ∣ x + y := by
  let d := (x - y) / 2
  let t := (x + y) / 2
  have hd : x - y = 2 * d := by dsimp only [d]; omega
  have ht : x + y = 2 * t := by dsimp only [t]; omega
  have hsum : d + t = x := by omega
  have hodd : t % 2 = 1 ∨ d % 2 = 1 := by omega
  rcases hodd with h | h
  · rw [ht] at hprod
    exact Or.inl (dvd_of_two_pow_dvd_twice_odd_mul h hprod)
  · rw [hd, mul_comm (x + y) (2 * d)] at hprod
    exact Or.inr (dvd_of_two_pow_dvd_twice_odd_mul h hprod)

private def halfStep (s : ℕ) : ZMod (2 ^ (s + 1)) := ↑((2 : ℤ) ^ s)

/-- The multiples of the smaller modulus give two possible differences in the larger one. -/
private theorem intCast_eq_zero_or_half {s : ℕ} {z : ℤ} (hz : (2 : ℤ) ^ s ∣ z) :
    (z : ZMod (2 ^ (s + 1))) = 0 ∨ (z : ZMod (2 ^ (s + 1))) = halfStep s := by
  obtain ⟨k, rfl⟩ := hz
  have hcast : (((2 : ℤ) ^ s * k : ℤ) : ZMod (2 ^ (s + 1))) =
      (((2 : ℤ) ^ s * (k % 2) : ℤ) : ZMod (2 ^ (s + 1))) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2
    refine ⟨-(k / 2), ?_⟩
    have hsplit : k % 2 - k = 2 * -(k / 2) := by omega
    rw [← mul_sub, hsplit]
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_assoc]
  rw [hcast]
  rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with hk | hk
  · exact Or.inl (by rw [hk, mul_zero, Int.cast_zero])
  · exact Or.inr (by rw [hk, mul_one, halfStep])

private theorem eq_four_lifts_of_sq_eq_two {s : ℕ} {x y : ZMod (2 ^ (s + 1))}
    (hx : IsUnit x) (hy : IsUnit y) (hsq : x ^ 2 = y ^ 2) :
    x = y ∨ x = y + halfStep s ∨ x = -y ∨ x = -y + halfStep s := by
  let : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
  let f : ZMod (2 ^ (s + 1)) →+* ZMod 2 :=
    ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero s)) (ZMod 2)
  have parity (z : ℤ) (hz : IsUnit (z : ZMod (2 ^ (s + 1)))) : z % 2 = 1 := by
    have hne : (z : ZMod 2) ≠ 0 := by
      simpa only [map_intCast] using (hz.map f).ne_zero
    have hndvd : ¬ (2 : ℤ) ∣ z :=
      fun hd => hne ((ZMod.intCast_zmod_eq_zero_iff_dvd z 2).2 hd)
    rw [Int.dvd_iff_emod_eq_zero] at hndvd
    omega
  obtain ⟨X, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨Y, rfl⟩ := ZMod.intCast_surjective y
  have hprod : (2 : ℤ) ^ (s + 1) ∣ (X + Y) * (X - Y) := by
    have hzero : (((X + Y) * (X - Y) : ℤ) : ZMod (2 ^ (s + 1))) = 0 := by
      rw [Int.cast_mul, Int.cast_add, Int.cast_sub, ← sq_sub_sq, hsq, sub_self]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  rcases two_pow_dvd_sub_or_add (parity X hx) (parity Y hy) hprod with h | h
  · rcases intCast_eq_zero_or_half h with hzero | hstep
    · rw [Int.cast_sub] at hzero
      exact Or.inl (sub_eq_zero.mp hzero)
    · rw [Int.cast_sub] at hstep
      exact Or.inr (Or.inl (by simpa only [add_comm (halfStep s)] using
        (sub_eq_iff_eq_add.mp hstep)))
  · rcases intCast_eq_zero_or_half h with hzero | hstep
    · rw [Int.cast_add] at hzero
      exact Or.inr (Or.inr (Or.inl (eq_neg_iff_add_eq_zero.mpr hzero)))
    · have hsub : (X : ZMod (2 ^ (s + 1))) - -(Y : ZMod (2 ^ (s + 1))) = halfStep s := by
        simpa only [Int.cast_add, sub_neg_eq_add] using hstep
      exact Or.inr (Or.inr (Or.inr (by simpa only [add_comm (halfStep s)] using
        (sub_eq_iff_eq_add.mp hsub))))

/-- A unit quadratic fiber at a positive power of two has at most four roots. -/
theorem card_unitQuadraticRoots_le_four_two {r : ℕ} (hr : 0 < r)
    (a : ZMod (2 ^ r)) (b : (ZMod (2 ^ r))ˣ) :
    (unitQuadraticRoots a b).card ≤ 4 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hr.ne'
  by_cases hs : s = 0
  · subst s
    refine (Finset.card_le_univ (unitQuadraticRoots a b)).trans ?_
    change Fintype.card (ZMod 2)ˣ ≤ 4
    rw [Fintype.card_unique]
    decide
  · rcases (unitQuadraticRoots a b).eq_empty_or_nonempty with hempty | ⟨y, hy⟩
    · simp [hempty]
    · let z : ZMod (2 ^ (s + 1)) := (y : ZMod (2 ^ (s + 1)))
      refine (Finset.card_le_card_of_injOn
        (s := unitQuadraticRoots a b) (t := {z, z + halfStep s, -z, -z + halfStep s})
        (fun x : (ZMod (2 ^ (s + 1)))ˣ => (x : ZMod (2 ^ (s + 1)))) ?_
        Units.val_injective.injOn).trans Finset.card_le_four
      intro x hx
      rw [Finset.mem_coe] at hx
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
      exact eq_four_lifts_of_sq_eq_two x.isUnit y.isUnit
        (sq_eq_of_quadratic_eq b.isUnit (mem_unitQuadraticRoots.mp hx)
          (mem_unitQuadraticRoots.mp hy))

/-- Odd-prime bound for the actual stationary roots of the Kloosterman sum. -/
theorem card_stationaryRoots_le_two {p e : ℕ} [Fact p.Prime]
    (he : 2 ≤ e) (hp : p ≠ 2) (a : ZMod (p ^ e)) (b : (ZMod (p ^ e))ˣ) :
    (stationaryRoots (p := p) (e := e) a b).card ≤ 2 := by
  let f := reduceLow (p := p) (e := e)
  let bLow := Units.map f.toMonoidHom b
  change (unitQuadraticRoots (f a) bLow).card ≤ 2
  exact card_unitQuadraticRoots_le_two (p := p) (r := e / 2) (by omega) hp _ _

/-- The bound for the actual stationary roots at powers of two. -/
theorem card_stationaryRoots_le_four_two {e : ℕ} (he : 2 ≤ e)
    (a : ZMod (2 ^ e)) (b : (ZMod (2 ^ e))ˣ) :
    (stationaryRoots (p := 2) (e := e) a b).card ≤ 4 := by
  let f := reduceLow (p := 2) (e := e)
  let bLow := Units.map f.toMonoidHom b
  change (unitQuadraticRoots (f a) bLow).card ≤ 4
  exact card_unitQuadraticRoots_le_four_two (r := e / 2) (by omega) _ _

/-- The odd-prime stationary-phase norm bound for the unnormalized sum. -/
theorem norm_kloosterman_le_two_mul {p e : ℕ} [Fact p.Prime]
    (he : 2 ≤ e) (hp : p ≠ 2) (a : ZMod (p ^ e)) (b : (ZMod (p ^ e))ˣ) :
    ‖kloosterman a b‖ ≤ 2 * ((p ^ (e - e / 2) : ℕ) : ℝ) := by
  have hc : ((stationaryRoots (p := p) (e := e) a b).card : ℝ) ≤ 2 := by
    exact_mod_cast card_stationaryRoots_le_two he hp a b
  rw [mul_comm]
  exact (norm_kloosterman_le_card_roots (p := p) (e := e) he a b).trans
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))

/-- The stationary-phase norm bound at powers of two for the unnormalized sum. -/
theorem norm_kloosterman_le_four_mul_two {e : ℕ} (he : 2 ≤ e)
    (a : ZMod (2 ^ e)) (b : (ZMod (2 ^ e))ˣ) :
    ‖kloosterman a b‖ ≤ 4 * ((2 ^ (e - e / 2) : ℕ) : ℝ) := by
  have hc : ((stationaryRoots (p := 2) (e := e) a b).card : ℝ) ≤ 4 := by
    exact_mod_cast card_stationaryRoots_le_four_two he a b
  rw [mul_comm]
  exact (norm_kloosterman_le_card_roots (p := 2) (e := e) he a b).trans
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))

end

end D5.S3.CharacterSums.PrimePowerKloostermanStationaryPhase
