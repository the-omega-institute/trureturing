/- GID: D5/S1/Recurrence/LucasEvenPeriods
   generality: G
   mirror-B: D5/B/S1/Recurrence/LucasEvenPeriods
   mirror-E: none(waiver:formal-unit-only)
   anchors: []
   utility: none
   digest: Even Lucas companion periods agree except at the exceptional modulus four. -/

import D5.S1.Recurrence.LucasCompanion
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

/-!
The even-parameter, even-modulus period questions in Section 5 of
Fiebig--Mbirika--Spilker, *Period patterns, entry points, and orders in the Lucas
sequences* (arXiv:2408.14632v2), reduce to the odd part and the two-power part.

CRT gives both periods as least common multiples. A companion zero makes the odd-part
periods equal; at an odd zero index their common period has two-adic valuation one
for `q = -1` and two for `q = 1`. The frozen dyadic zero criterion forces the parameter
to vanish on the two-power part. There the matrix has period two or four, while the
trace period drops from four to two exactly at exponent two. The final equivalence
includes both equality outside the exception and inequality inside it.

All declarations are general algebraic or arithmetic proofs. There is no bounded
enumeration, checker, numeric reduction, or certified instance; `utility: none` applies
to the entire module. Only the headline theorem is public.
-/

namespace D5.S1.Recurrence.LucasEvenPeriods

open Matrix LucasEvenDescent LucasCompanion

private abbrev reducedUnit (m : ℕ) (q : ℤˣ) : (ZMod m)ˣ :=
  Units.map (Int.castRingHom (ZMod m)).toMonoidHom q

private theorem map_companion {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : R) (q : Rˣ) :
    Units.map f.mapMatrix.toMonoidHom (companion p q) =
      companion (f p) (Units.map f.toMonoidHom q) := by
  apply Units.ext
  ext i j
  change f ((companion p q : Matrix (Fin 2) (Fin 2) R) i j) = _
  fin_cases i <;> fin_cases j <;> simp [companion]

private theorem map_trace_power {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : R) (q : Rˣ) (n : ℤ) :
    f (lucasV p q n) = lucasV (f p) (Units.map f.toMonoidHom q) n := by
  let F : (Matrix (Fin 2) (Fin 2) R)ˣ →* (Matrix (Fin 2) (Fin 2) S)ˣ :=
    Units.map f.mapMatrix.toMonoidHom
  have h := congrArg Units.val (map_zpow F
    (companion p q) n)
  dsimp only [F] at h
  rw [map_companion] at h
  change (↑(companion p q ^ n) : Matrix (Fin 2) (Fin 2) R).map f = _ at h
  rw [lucasV, AddMonoidHom.map_trace, h]
  rfl

private theorem map_reducedUnit {a b : ℕ} (f : ZMod a →+* ZMod b) (q : ℤˣ) :
    Units.map f.toMonoidHom (reducedUnit a q) = reducedUnit b q := by
  apply Units.ext
  change f (q : ℤ) = (q : ℤ)
  simp

private theorem crt_periods (a b : ℕ) (hab : a.Coprime b) (p : ℤ) (q : ℤˣ) :
    matrixPeriod (p : ZMod (a * b)) (reducedUnit (a * b) q) =
      Nat.lcm (matrixPeriod (p : ZMod a) (reducedUnit a q))
        (matrixPeriod (p : ZMod b) (reducedUnit b q)) ∧
    companionPeriod (p : ZMod (a * b)) (reducedUnit (a * b) q) =
      Nat.lcm (companionPeriod (p : ZMod a) (reducedUnit a q))
        (companionPeriod (p : ZMod b) (reducedUnit b q)) := by
  let e := ZMod.chineseRemainder hab
  let f : ZMod (a * b) →+* ZMod a := (RingHom.fst _ _).comp e.toRingHom
  let g : ZMod (a * b) →+* ZMod b := (RingHom.snd _ _).comp e.toRingHom
  have hinj {x y : ZMod (a * b)} (hf : f x = f y) (hg : g x = g y) : x = y :=
    e.injective (Prod.ext hf hg)
  let F : (Matrix (Fin 2) (Fin 2) (ZMod (a * b)))ˣ →*
      (Matrix (Fin 2) (Fin 2) (ZMod a))ˣ := Units.map f.mapMatrix.toMonoidHom
  let G : (Matrix (Fin 2) (Fin 2) (ZMod (a * b)))ˣ →*
      (Matrix (Fin 2) (Fin 2) (ZMod b))ˣ := Units.map g.mapMatrix.toMonoidHom
  have hFG : Function.Injective (F.prod G) := by
    intro x y h
    apply Units.ext
    ext i j
    apply hinj
    · exact congrArg (fun z => (z.1 : Matrix (Fin 2) (Fin 2) (ZMod a)) i j) h
    · exact congrArg (fun z => (z.2 : Matrix (Fin 2) (Fin 2) (ZMod b)) i j) h
  constructor
  · have h := orderOf_injective (F.prod G) hFG
      (companion (p : ZMod (a * b)) (reducedUnit (a * b) q))
    rw [Prod.orderOf] at h
    change Nat.lcm (orderOf (F (companion _ _))) (orderOf (G (companion _ _))) = _ at h
    dsimp only [F, G] at h
    rw [map_companion f, map_companion g, map_reducedUnit f, map_reducedUnit g] at h
    simpa only [matrixPeriod, map_intCast] using h.symm
  · have hv (n : ℤ) :
        f (lucasV (p : ZMod (a * b)) (reducedUnit (a * b) q) n) =
          lucasV (p : ZMod a) (reducedUnit a q) n ∧
        g (lucasV (p : ZMod (a * b)) (reducedUnit (a * b) q) n) =
          lucasV (p : ZMod b) (reducedUnit b q) n := by
      rw [map_trace_power f, map_trace_power g, map_reducedUnit f, map_reducedUnit g]
      simp only [map_intCast, and_self]
    have hd (k : ℕ) : companionPeriod (p : ZMod (a * b)) (reducedUnit (a * b) q) ∣ k ↔
        Nat.lcm (companionPeriod (p : ZMod a) (reducedUnit a q))
          (companionPeriod (p : ZMod b) (reducedUnit b q)) ∣ k := by
      simp only [Nat.lcm_dvd_iff, companionPeriod_dvd_iff]
      constructor
      · intro h
        constructor <;> intro n
        · simpa only [(hv _).1] using congrArg f (h n)
        · simpa only [(hv _).2] using congrArg g (h n)
      · rintro ⟨ha, hb⟩ n
        apply hinj
        · simpa only [(hv _).1] using ha n
        · simpa only [(hv _).2] using hb n
    exact Nat.dvd_antisymm ((hd _).mpr (dvd_refl _)) ((hd _).mp (dvd_refl _))

private theorem map_integer_trace (m : ℕ) (p : ℤ) (q : ℤˣ) (n : ℕ) :
    (lucasVInt p q n : ZMod m) = lucasV (p : ZMod m) (reducedUnit m q) n := by
  rw [lucasVInt_eq_lucasV]
  exact map_trace_power (Int.castRingHom (ZMod m)) p q n

private theorem reduce_zero {m d : ℕ} (hd : d ∣ m) (p : ℤ) (q : ℤˣ) (r : ℤ)
    (hr : lucasV (p : ZMod m) (reducedUnit m q) r = 0) :
    lucasV (p : ZMod d) (reducedUnit d q) r = 0 := by
  have h := congrArg (ZMod.castHom hd (ZMod d)) hr
  simpa only [map_trace_power, map_intCast, map_reducedUnit, map_zero] using h

private theorem odd_part_period (s : ℕ) (hs : Odd s) (p : ℤ) (q : ℤˣ)
    (hz : ∃ r : ℤ, lucasV (p : ZMod s) (reducedUnit s q) r = 0) :
    companionPeriod (p : ZMod s) (reducedUnit s q) =
      matrixPeriod (p : ZMod s) (reducedUnit s q) := by
  apply companionPeriod_eq_matrixPeriod_of_lucasV_zero _ _ _ hz
  exact (ZMod.isUnit_iff_coprime 2 s).mpr (Nat.coprime_two_left.mpr hs)

private theorem neg_one_matrix_ne {R : Type*} [CommRing R] (h2 : (2 : R) ≠ 0) :
    (-1 : Matrix (Fin 2) (Fin 2) R) ≠ 1 := by
  intro h
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) R => A 0 0) h
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  apply h2
  linear_combination -h00

private theorem four_dvd_order_of_even_power_neg_one {R : Type*} [CommRing R]
    (h2 : (2 : R) ≠ 0) (x : (Matrix (Fin 2) (Fin 2) R)ˣ) (r : ℕ)
    (hr : (x : Matrix (Fin 2) (Fin 2) R) ^ (2 * r) = -1) : 4 ∣ orderOf x := by
  have hx : (x : Matrix (Fin 2) (Fin 2) R) ^ orderOf x = 1 := by
    exact congrArg Units.val (pow_orderOf_eq_one x)
  have hP : (-1 : Matrix (Fin 2) (Fin 2) R) ^ orderOf x = 1 := by
    rw [← hr, ← pow_mul, Nat.mul_comm (2 * r), pow_mul, hx, one_pow]
  obtain ⟨k, hk⟩ := (neg_one_pow_eq_one_iff_even (neg_one_matrix_ne h2)).mp hP
  have hkP : (-1 : Matrix (Fin 2) (Fin 2) R) ^ k = 1 := by
    rw [← hr, ← pow_mul, show 2 * r * k = orderOf x * r by rw [hk]; ring,
      pow_mul, hx, one_pow]
  obtain ⟨j, hj⟩ := (neg_one_pow_eq_one_iff_even (neg_one_matrix_ne h2)).mp hkP
  exact ⟨j, by omega⟩

private theorem odd_modulus_two_ne_zero (s : ℕ) (hs : Odd s) (hs1 : 1 < s) :
    (2 : ZMod s) ≠ 0 := by
  intro h
  have hd : s ∣ 2 := (ZMod.natCast_eq_zero_iff 2 s).mp h
  have hl := Nat.le_of_dvd (by decide : 0 < 2) hd
  obtain ⟨j, hj⟩ := hs
  omega

private theorem odd_part_order_divisibility (s : ℕ) (hs : Odd s) (hs1 : 1 < s)
    (p : ℤ) (q : ℤˣ) (r : ℕ)
    (hr : lucasV (p : ZMod s) (reducedUnit s q) r = 0) :
    2 ∣ matrixPeriod (p : ZMod s) (reducedUnit s q) ∧
      (q = 1 → 4 ∣ matrixPeriod (p : ZMod s) (reducedUnit s q)) := by
  have h2 := odd_modulus_two_ne_zero s hs hs1
  have hm : (-1 : ZMod s) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  rcases Int.units_eq_one_or q with hq | hq
  · subst q
    have hr' := companion_double_of_lucasV_zero (p : ZMod s) (reducedUnit s 1) r hr
    have hn : (companion (p : ZMod s) (reducedUnit s 1) :
        Matrix (Fin 2) (Fin 2) (ZMod s)) ^ (2 * r) = -1 := by
      rw [show (2 : ℤ) * (r : ℤ) = ((2 * r : ℕ) : ℤ) by push_cast; rfl,
        zpow_natCast, Units.val_pow_eq_pow_val] at hr'
      simpa [reducedUnit] using hr'
    have hd := four_dvd_order_of_even_power_neg_one h2 _ r hn
    exact ⟨dvd_trans (by decide : 2 ∣ 4) hd, fun _ => hd⟩
  · subst q
    have hd := companion_power_det (p : ZMod s) (reducedUnit s (-1))
      (matrixPeriod (p : ZMod s) (reducedUnit s (-1)))
    have he : (-1 : ZMod s) ^ matrixPeriod (p : ZMod s) (reducedUnit s (-1)) = 1 := by
      simpa [matrixPeriod, reducedUnit] using hd.symm
    refine ⟨((neg_one_pow_eq_one_iff_even hm).mp he).two_dvd, ?_⟩
    intro h
    have hh := congrArg (fun z : ℤˣ => (z : ℤ)) h
    norm_num at hh

private theorem dyadic_zero_index_odd (p : ℤ) (hp : Even p) (q : ℤˣ)
    (v : ℕ) (hv : 2 ≤ v) (r : ℕ)
    (hr : lucasV (p : ZMod (2 ^ v)) (reducedUnit (2 ^ v) q) r = 0) : Odd r := by
  have hq : Odd (q : ℤ) := by
    rcases Int.units_eq_one_or q with h | h <;> rw [h] <;> norm_num
  have hd : (2 : ℤ) ^ v ∣ lucasVInt p q r := by
    rw [← map_integer_trace] at hr
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr
  rcases Nat.even_or_odd r with he | ho
  · obtain ⟨j, hj⟩ := he
    have heq : r = 2 * j := by omega
    rw [heq] at hd
    have hval := lucasVInt_even_two_adic_valuation p q hp hq j
    have hn : lucasVInt p q (2 * j) ≠ 0 := by
      intro h
      rw [h] at hval
      norm_num at hval
    have hv' := ((padicValInt_dvd_iff v _).mp hd).resolve_left hn
    rw [hval] at hv'
    omega
  · exact ho

private theorem odd_part_valuation (s : ℕ) (hs : Odd s) (hs1 : 1 < s)
    (p : ℤ) (q : ℤˣ) (r : ℕ) (hrpos : 0 < r) (hro : Odd r)
    (hr : lucasV (p : ZMod s) (reducedUnit s q) r = 0) :
    padicValNat 2 (matrixPeriod (p : ZMod s) (reducedUnit s q)) =
      if q = 1 then 2 else 1 := by
  have hl := odd_part_order_divisibility s hs hs1 p q r hr
  have hPpos := matrixPeriod_zmod_pos s (by omega) (p : ZMod s) (reducedUnit s q)
  have hrval : padicValNat 2 r = 0 :=
    padicValNat.eq_zero_of_not_dvd
      (by simpa only [← even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hro))
  have hdouble := companion_double_of_lucasV_zero (p : ZMod s) (reducedUnit s q) r hr
  rw [show (2 : ℤ) * (r : ℤ) = ((2 * r : ℕ) : ℤ) by push_cast; rfl,
    zpow_natCast, Units.val_pow_eq_pow_val] at hdouble
  rcases Int.units_eq_one_or q with hq | hq
  · subst q
    have hn : (companion (p : ZMod s) (reducedUnit s 1) :
        Matrix (Fin 2) (Fin 2) (ZMod s)) ^ (2 * r) = -1 := by
      simpa [reducedUnit] using hdouble
    have hpow : companion (p : ZMod s) (reducedUnit s 1) ^ (4 * r) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      rw [show 4 * r = (2 * r) * 2 by omega, pow_mul, hn, neg_one_sq]
    have hd : matrixPeriod (p : ZMod s) (reducedUnit s 1) ∣ 4 * r :=
      orderOf_dvd_of_pow_eq_one hpow
    have hu := (padicValNat_dvd_iff_le (by omega : 4 * r ≠ 0)).mp
      (pow_padicValNat_dvd.trans hd :
        2 ^ padicValNat 2 (matrixPeriod (p : ZMod s) (reducedUnit s 1)) ∣ 4 * r)
    have hlo := (padicValNat_dvd_iff_le (p := 2) (n := 2) (by omega :
      matrixPeriod (p : ZMod s) (reducedUnit s 1) ≠ 0)).mp (hl.2 rfl)
    rw [padicValNat.mul (by decide) (by omega), hrval] at hu
    have hv4 : padicValNat 2 4 = 2 := padicValNat.prime_pow 2
    rw [hv4] at hu
    norm_num at hu hlo ⊢
    omega
  · subst q
    have hpow : companion (p : ZMod s) (reducedUnit s (-1)) ^ (2 * r) = 1 := by
      apply Units.ext
      simpa [reducedUnit, zpow_natCast, hro.neg_one_pow] using hdouble
    have hd : matrixPeriod (p : ZMod s) (reducedUnit s (-1)) ∣ 2 * r :=
      orderOf_dvd_of_pow_eq_one hpow
    have hu := (padicValNat_dvd_iff_le (by omega : 2 * r ≠ 0)).mp
      (pow_padicValNat_dvd.trans hd :
        2 ^ padicValNat 2 (matrixPeriod (p : ZMod s) (reducedUnit s (-1))) ∣ 2 * r)
    have hlo := one_le_padicValNat_of_dvd (by omega) hl.1
    rw [padicValNat.mul (by decide) (by omega), hrval] at hu
    norm_num at hu ⊢
    omega

private theorem zero_companion_sq {R : Type*} [CommRing R] (q : Rˣ) :
    (companion (0 : R) q : Matrix (Fin 2) (Fin 2) R) ^ 2 = -(q : R) • 1 := by
  have h := companion_double_of_lucasV_zero (0 : R) q 1
    (lucasV_recurrence (0 : R) q).2.1
  simpa using h

private theorem companion_ne_one {R : Type*} [CommRing R] [Nontrivial R]
    (p : R) (q : Rˣ) : companion p q ≠ 1 := by
  intro h
  have h10 := congrArg (fun A : (Matrix (Fin 2) (Fin 2) R)ˣ =>
    (A : Matrix (Fin 2) (Fin 2) R) 1 0) h
  simpa [companion] using h10

private theorem periods_minus_one {R : Type*} [CommRing R] [Finite R] [Nontrivial R]
    (h2 : (2 : R) ≠ 0) :
    matrixPeriod (0 : R) (-1) = 2 ∧ companionPeriod (0 : R) (-1) = 2 := by
  have hsq : companion (0 : R) (-1) ^ (2 : ℕ) = 1 := by
    apply Units.ext
    simpa using zero_companion_sq (-1 : Rˣ)
  have hm : matrixPeriod (0 : R) (-1) = 2 :=
    orderOf_eq_prime hsq (companion_ne_one _ _)
  refine ⟨hm, ?_⟩
  have hd := companionPeriod_dvd_matrixPeriod (0 : R) (-1)
  rw [hm, Nat.dvd_prime Nat.prime_two] at hd
  rcases hd with h | h
  · have ht := (companionPeriod_spec (0 : R) (-1)).2.1 0
    rw [h] at ht
    norm_num only [Nat.cast_one, zero_add] at ht
    rw [(lucasV_recurrence (0 : R) (-1)).2.1,
      (lucasV_recurrence (0 : R) (-1)).1] at ht
    exact False.elim (h2 ht.symm)
  · exact h

private theorem zero_trace_shift_two {R : Type*} [CommRing R] (n : ℤ) :
    lucasV (0 : R) 1 (n + 2) = -lucasV (0 : R) 1 n := by
  have hs : (↑(companion (0 : R) 1 ^ (2 : ℤ)) : Matrix (Fin 2) (Fin 2) R) = -1 := by
    simpa using zero_companion_sq (1 : Rˣ)
  simp only [lucasV, zpow_add, Units.val_mul, hs, mul_neg, mul_one, Matrix.trace_neg]

private theorem periods_plus_one {R : Type*} [CommRing R] [Finite R] [DecidableEq R]
    (h2 : (2 : R) ≠ 0) :
    matrixPeriod (0 : R) 1 = 4 ∧
      companionPeriod (0 : R) 1 = if (4 : R) = 0 then 2 else 4 := by
  have hs : (companion (0 : R) 1 : Matrix (Fin 2) (Fin 2) R) ^ 2 = -1 := by
    simpa using zero_companion_sq (1 : Rˣ)
  have hn : companion (0 : R) 1 ^ (2 : ℕ) ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hs] at h'
    exact neg_one_matrix_ne h2 h'
  have h4 : companion (0 : R) 1 ^ (4 : ℕ) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [show 4 = 2 * 2 by decide, pow_mul, hs, neg_one_sq]
  have hm : matrixPeriod (0 : R) 1 = 4 := by
    exact orderOf_eq_prime_pow (p := 2) (n := 1) hn h4
  have hd := companionPeriod_dvd_matrixPeriod (0 : R) 1
  rw [hm] at hd
  have hn1 : companionPeriod (0 : R) 1 ≠ 1 := by
    intro h
    have ht := (companionPeriod_spec (0 : R) 1).2.1 0
    rw [h] at ht
    norm_num only [Nat.cast_one, zero_add] at ht
    rw [(lucasV_recurrence (0 : R) 1).2.1,
      (lucasV_recurrence (0 : R) 1).1] at ht
    exact h2 ht.symm
  have htwo : companionPeriod (0 : R) 1 = 2 ↔ (4 : R) = 0 := by
    constructor
    · intro h
      have ht := (companionPeriod_spec (0 : R) 1).2.1 0
      rw [h] at ht
      norm_num only [Nat.cast_ofNat] at ht
      change lucasV (0 : R) 1 (0 + 2) = lucasV (0 : R) 1 0 at ht
      rw [zero_trace_shift_two, (lucasV_recurrence (0 : R) 1).1] at ht
      linear_combination -ht
    · intro h
      have ht : Function.Periodic (lucasV (0 : R) 1) (2 : ℤ) := by
        intro n
        rw [zero_trace_shift_two, lucasV_eq_lucasU]
        simp only [zero_mul, sub_zero]
        linear_combination -lucasU (0 : R) 1 (n + 1) * h
      have hdiv := (companionPeriod_dvd_iff (0 : R) 1 2).mpr ht
      exact ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left hn1
  refine ⟨hm, ?_⟩
  split_ifs with h
  · exact htwo.mpr h
  · have hn2 := fun h' => h (htwo.mp h')
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hd
    interval_cases k
    · exact False.elim (hn1 (by simpa only [pow_zero] using he))
    · exact False.elim (hn2 (by simpa only [pow_one] using he))
    · exact he

private theorem dyadic_parameter_zero (p : ℤ) (hp : Even p) (q : ℤˣ)
    (v : ℕ) (hv : 2 ≤ v) (r : ℕ) (hrpos : 0 < r)
    (hr : lucasV (p : ZMod (2 ^ v)) (reducedUnit (2 ^ v) q) r = 0) :
    (p : ZMod (2 ^ v)) = 0 := by
  have hq : Odd (q : ℤ) := by
    rcases Int.units_eq_one_or q with h | h <;> rw [h] <;> norm_num
  have hd : (2 : ℤ) ^ v ∣ lucasVInt p q r := by
    rw [← map_integer_trace] at hr
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hr
  have hpdiv := (lucasVInt_exists_positive_zero_iff p q hp hq v hv).mp
    ⟨r, hrpos, hd⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
  exact_mod_cast hpdiv

private theorem dyadic_periods (p : ℤ) (q : ℤˣ) (v : ℕ) (hv : 2 ≤ v)
    (hp0 : (p : ZMod (2 ^ v)) = 0) :
    matrixPeriod (p : ZMod (2 ^ v)) (reducedUnit (2 ^ v) q) =
        (if q = 1 then 4 else 2) ∧
      companionPeriod (p : ZMod (2 ^ v)) (reducedUnit (2 ^ v) q) =
        (if q = 1 then (if v = 2 then 2 else 4) else 2) := by
  have h4le : 4 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 0 < 2) hv
  let : NeZero (2 ^ v) := ⟨by omega⟩
  let : Fact (1 < 2 ^ v) := ⟨by omega⟩
  have h2 : (2 : ZMod (2 ^ v)) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 (2 ^ v)).mp h
    have hl := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  rw [hp0]
  rcases Int.units_eq_one_or q with hq | hq
  · subst q
    simp only [reducedUnit, map_one, ↓reduceIte]
    have h := periods_plus_one h2
    by_cases hv2 : v = 2
    · subst v
      norm_num at h ⊢
      exact h
    · have h8le : 8 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ v)
      have h4 : (4 : ZMod (2 ^ v)) ≠ 0 := by
        intro h
        have hd := (ZMod.natCast_eq_zero_iff 4 (2 ^ v)).mp h
        have hl := Nat.le_of_dvd (by decide : 0 < 4) hd
        omega
      simpa only [if_neg h4, if_neg hv2] using h
  · subst q
    have h := periods_minus_one h2
    simpa [reducedUnit] using h

private theorem periods_mod_two (p : ℤ) (hp : Even p) (q : ℤˣ) :
    matrixPeriod (p : ZMod 2) (reducedUnit 2 q) = 2 ∧
      companionPeriod (p : ZMod 2) (reducedUnit 2 q) = 1 := by
  have hp0 : (p : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd p 2).mpr hp.two_dvd
  rw [hp0]
  have hsq : companion (0 : ZMod 2) (reducedUnit 2 q) ^ (2 : ℕ) = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, zero_companion_sq]
    rcases Int.units_eq_one_or q with h | h <;> rw [h] <;> norm_num [reducedUnit]
  refine ⟨orderOf_eq_prime hsq (companion_ne_one _ _), ?_⟩
  apply Nat.dvd_one.mp
  apply (companionPeriod_dvd_iff _ _ 1).mpr
  intro n
  simp only [lucasV_eq_lucasU, show (2 : ZMod 2) = 0 by decide, zero_mul, sub_zero]

/-- The two even-parameter open period questions of Fiebig--Mbirika--Spilker:
whenever a positive companion zero exists, the matrix and trace periods agree exactly
outside the stated exception `q = 1`, `m = 4`, `4 ∣ p`. Integer units encode `q = ±1`. -/
theorem even_lucas_periods (p : ℤ) (q : ℤˣ) (m : ℕ)
    (hp : Even p) (hmEven : Even m) (hm : 2 < m)
    (hz : ∃ r : ℕ, 0 < r ∧ lucasV (p : ZMod m)
      (Units.map (Int.castRingHom (ZMod m)).toMonoidHom q) r = 0) :
    let Q := Units.map (Int.castRingHom (ZMod m)).toMonoidHom q
    matrixPeriod (p : ZMod m) Q = companionPeriod (p : ZMod m) Q ↔
      ¬(q = 1 ∧ m = 4 ∧ (4 : ℤ) ∣ p) := by
  change matrixPeriod (p : ZMod m) (reducedUnit m q) =
    companionPeriod (p : ZMod m) (reducedUnit m q) ↔ _
  obtain ⟨r, hrpos, hr⟩ := hz
  obtain ⟨v, s, hs, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : m ≠ 0)
  have hspos : 0 < s := by
    by_contra h
    have hs0 : s = 0 := by omega
    simp only [hs0, mul_zero] at hm
    omega
  have hv1 : 1 ≤ v := by
    by_contra h
    have hv0 : v = 0 := by omega
    simp only [hv0, pow_zero, one_mul] at hmEven
    exact (Nat.not_even_iff_odd.mpr hs) hmEven
  have hsr := reduce_zero (dvd_mul_left s (2 ^ v)) p q r hr
  have hdr := reduce_zero (dvd_mul_right (2 ^ v) s) p q r hr
  have hodd := odd_part_period s hs p q ⟨r, hsr⟩
  have hcrt := crt_periods (2 ^ v) s (hs.coprime_two_left.pow_left v) p q
  by_cases hv : v = 1
  · subst v
    simp only [pow_one] at *
    change matrixPeriod (p : ZMod (2 * s)) (reducedUnit (2 * s) q) =
        Nat.lcm (matrixPeriod (p : ZMod 2) (reducedUnit 2 q))
          (matrixPeriod (p : ZMod s) (reducedUnit s q)) ∧
      companionPeriod (p : ZMod (2 * s)) (reducedUnit (2 * s) q) =
        Nat.lcm (companionPeriod (p : ZMod 2) (reducedUnit 2 q))
          (companionPeriod (p : ZMod s) (reducedUnit s q)) at hcrt
    have hs1 : 1 < s := by omega
    have hl := periods_mod_two p hp q
    have hd := (odd_part_order_divisibility s hs hs1 p q r hsr).1
    have heq : matrixPeriod (p : ZMod (2 * s)) (reducedUnit (2 * s) q) =
        companionPeriod (p : ZMod (2 * s)) (reducedUnit (2 * s) q) := by
      rw [hcrt.1, hcrt.2, hl.1, hl.2, hodd, Nat.lcm_eq_right hd, Nat.lcm_one_left]
    refine iff_of_true heq ?_
    rintro ⟨_, he, _⟩
    obtain ⟨j, hj⟩ := hs
    omega
  · have hv2 : 2 ≤ v := by omega
    have hp0 := dyadic_parameter_zero p hp q v hv2 r hrpos hdr
    have hlocal := dyadic_periods p q v hv2 hp0
    have h4le : 4 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 0 < 2) hv2
    by_cases hs1 : s = 1
    · subst s
      simp only [mul_one] at *
      have hmod := congrArg (fun n : ℕ =>
        matrixPeriod (p : ZMod n) (reducedUnit n q) =
          companionPeriod (p : ZMod n) (reducedUnit n q)) (Nat.mul_one (2 ^ v))
      rw [hmod]
      rw [hlocal.1, hlocal.2]
      by_cases hvEq : v = 2
      · subst v
        have hp4 : (4 : ℤ) ∣ p := (ZMod.intCast_zmod_eq_zero_iff_dvd p 4).mp hp0
        by_cases hq : q = 1 <;> simp [hq, hp4]
      · have h8le : 8 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide : 0 < 2)
          (by omega : 3 ≤ v)
        have hn4 : 2 ^ v ≠ 4 := by omega
        simp only [if_neg hvEq, hn4, false_and, and_false, not_false_eq_true, iff_true]
    · have hsGt : 1 < s := by omega
      have hro := dyadic_zero_index_odd p hp q v hv2 r hdr
      have hval := odd_part_valuation s hs hsGt p q r hrpos hro hsr
      have hPpos := matrixPeriod_zmod_pos s hspos (p : ZMod s) (reducedUnit s q)
      have hd2 : 2 ∣ matrixPeriod (p : ZMod s) (reducedUnit s q) := by
        apply dvd_of_one_le_padicValNat
        rw [hval]
        split_ifs <;> omega
      have hd4 (hq : q = 1) : 4 ∣ matrixPeriod (p : ZMod s) (reducedUnit s q) := by
        apply (padicValNat_dvd_iff_le (p := 2) (n := 2) (by omega :
          matrixPeriod (p : ZMod s) (reducedUnit s q) ≠ 0)).mpr
        rw [hval, if_pos hq]
      have hdu : (if q = 1 then 4 else 2) ∣
          matrixPeriod (p : ZMod s) (reducedUnit s q) := by
        split_ifs with hq
        · exact hd4 hq
        · exact hd2
      have hdv : (if q = 1 then (if v = 2 then 2 else 4) else 2) ∣
          matrixPeriod (p : ZMod s) (reducedUnit s q) := by
        split_ifs with hq hvEq
        · exact hd2
        · exact hd4 hq
        · exact hd2
      have heq : matrixPeriod (p : ZMod (2 ^ v * s)) (reducedUnit (2 ^ v * s) q) =
          companionPeriod (p : ZMod (2 ^ v * s)) (reducedUnit (2 ^ v * s) q) := by
        rw [hcrt.1, hcrt.2, hlocal.1, hlocal.2, hodd,
          Nat.lcm_eq_right hdu, Nat.lcm_eq_right hdv]
      refine iff_of_true heq ?_
      rintro ⟨_, he, _⟩
      have h8le : 8 ≤ 2 ^ v * s := Nat.mul_le_mul h4le (by omega : 2 ≤ s)
      omega

#print axioms even_lucas_periods

end D5.S1.Recurrence.LucasEvenPeriods
