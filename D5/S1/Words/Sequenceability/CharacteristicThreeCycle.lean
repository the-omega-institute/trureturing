/- GID: D5/S1/Words/Sequenceability/CharacteristicThreeCycle
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/CharacteristicThreeCycle
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite-field cycles have exact directed differences in characteristic three. -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! Finite-field reflection cycles and their exact directed differences. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.CharacteristicThreeCycle

open Function

variable {K : Type*} [Field K]

/-- Advance the multiplicative phase and reflect the row, charging only on wrap. -/
noncomputable def step (a : Kˣ) (z : Kˣ × ZMod 3) : Kˣ × ZMod 3 := by
  classical
  exact (a * z.1, -z.2 + if a * z.1 = 1 then 1 else 0)

/-- The ambient additive vertex represented by a unit and a row. -/
def vertex (z : Kˣ × ZMod 3) : K × ZMod 3 := (z.1, z.2)

/-- A nonzero first difference and the actual row difference. -/
noncomputable def label (a : Kˣ) (ha : (a : K) ≠ 1)
    (z : Kˣ × ZMod 3) : Kˣ × ZMod 3 := by
  classical
  exact (Units.mk0 ((a : K) - 1) (sub_ne_zero.mpr ha) * z.1,
    z.2 + if a * z.1 = 1 then 1 else 0)

private theorem partial_lap (a : Kˣ) {L : ℕ} (hord : orderOf a = L)
    (n : ZMod 3) {i : ℕ} (hi : i < L) :
    (step a)^[i] (1, n) = (a ^ i, (-1) ^ i * n) := by
  classical
  induction i with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply', ih (by omega)]
    have hn : a * a ^ i ≠ 1 := by
      intro h
      have hd : L ∣ i + 1 := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one (by simpa [pow_succ'] using h)
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hi) hd
    simp only [step, ite_eq_right hn, add_zero, pow_succ']
    congr 1
    ring

private theorem one_lap (a : Kˣ) {L : ℕ} (hord : orderOf a = L)
    (hpos : 0 < L) (heven : Even L) (n : ZMod 3) :
    (step a)^[L] (1, n) = (1, n + 1) := by
  classical
  have hpow : a * a ^ (L - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, ← hord, pow_orderOf_eq_one]
  have hsign : (-1 : ZMod 3) ^ (L - 1) = -1 := by
    apply Odd.neg_one_pow
    rw [Nat.odd_iff, Nat.even_iff] at *
    omega
  rw [← Nat.sub_add_cancel hpos, iterate_succ_apply',
    partial_lap a hord n (by omega)]
  simp [step, hpow, hsign]

private theorem block_laps (a : Kˣ) {L : ℕ} (hord : orderOf a = L)
    (hpos : 0 < L) (heven : Even L) (k : ℕ) (n : ZMod 3) :
    (step a)^[L * k] (1, n) = (1, n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (L * k) L, iterate_add_apply, ih,
      one_lap a hord hpos heven]
    simp [Nat.cast_add, add_assoc]

private theorem orbit_row (a : Kˣ) {L : ℕ} (hord : orderOf a = L)
    (hpos : 0 < L) (heven : Even L) (k i : ℕ) (hi : i < L) :
    (step a)^[L * k + i] (1, 0) = (a ^ i, (-1) ^ i * (k : ZMod 3)) := by
  rw [Nat.add_comm, iterate_add_apply, block_laps a hord hpos heven]
  simpa using partial_lap a hord (k : ZMod 3) hi

private theorem powers_bijective [Fintype K] [DecidableEq K] (a : Kˣ) {L : ℕ}
    (hord : orderOf a = L) (hcard : Fintype.card Kˣ = L) :
    Bijective (fun i : Fin L => a ^ (i : ℕ)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simpa using hcard.symm⟩
  intro i j h
  apply Fin.ext
  exact pow_injOn_Iio_orderOf (hord ▸ i.isLt) (hord ▸ j.isLt) h

private theorem orbit_bijective [Fintype K] [DecidableEq K] (a : Kˣ) {L : ℕ}
    (hord : orderOf a = L) (hcard : Fintype.card Kˣ = L)
    (hpos : 0 < L) (heven : Even L) :
    Bijective (fun i : Fin (3 * L) => (step a)^[i.val] (1, 0)) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp [Fintype.card_prod, hcard, mul_comm]⟩
  rintro ⟨b, t⟩
  obtain ⟨i, hi⟩ := (powers_bijective a hord hcard).surjective b
  let n : ZMod 3 := (-1) ^ (i : ℕ) * t
  have hn : (n.val : ZMod 3) = n := ZMod.natCast_zmod_val n
  refine ⟨⟨L * n.val + i.val, by
    have := ZMod.val_lt n
    have := i.isLt
    nlinarith⟩, ?_⟩
  change (step a)^[L * n.val + i.val] (1, 0) = (b, t)
  change a ^ i.val = b at hi
  rw [orbit_row a hord hpos heven n.val i.val i.isLt, hi, hn]
  congr 1
  dsimp [n]
  rw [← mul_assoc, ← pow_add]
  have hs : (-1 : ZMod 3) ^ (i.val + i.val) = 1 :=
    (show Even (i.val + i.val) from ⟨i.val, rfl⟩).neg_one_pow
  rw [hs, one_mul]

private theorem labels_bijective (a : Kˣ) (ha : (a : K) ≠ 1) :
    Bijective (label a ha) := by
  classical
  let c : Kˣ := Units.mk0 ((a : K) - 1) (sub_ne_zero.mpr ha)
  constructor
  · rintro ⟨b, t⟩ ⟨b', t'⟩ h
    have hb : b = b' := mul_left_cancel (congrArg Prod.fst h)
    subst b'
    have ht := congrArg Prod.snd h
    exact Prod.ext rfl (add_right_cancel ht)
  · rintro ⟨b, t⟩
    refine ⟨(c⁻¹ * b, t - if a * (c⁻¹ * b) = 1 then 1 else 0), ?_⟩
    simp [label, c]

private theorem label_difference (a : Kˣ) (ha : (a : K) ≠ 1)
    (z : Kˣ × ZMod 3) : vertex (step a z) - vertex z = vertex (label a ha z) := by
  classical
  rcases z with ⟨b, t⟩
  apply Prod.ext
  · simp [vertex, step, label, sub_mul]
  · change -t + (if a * b = 1 then 1 else 0) - t =
      t + (if a * b = 1 then 1 else 0)
    have ht : -t - t = t := by
      have : (3 : ZMod 3) = 0 := by decide
      linear_combination -t * this
    linear_combination ht

/-- A genuine single orbit with a bijective inventory of its directed differences. -/
theorem exists_cycle_inventory [Fintype K] [CharP K 3] :
    let L := Fintype.card K - 1
    ∃ (a : Kˣ) (ha : (a : K) ≠ 1),
      orderOf a = L ∧ 2 ≤ L ∧ Even L ∧
      ∃ e : Fin (3 * L) ≃ Kˣ × ZMod 3,
        (∀ i, e i = (step a)^[i.val] (1, 0)) ∧
        (step a)^[3 * L] (1, 0) = (1, 0) ∧
        Bijective (fun i => label a ha (e i)) ∧
        (∀ z, vertex (step a z) - vertex z = vertex (label a ha z)) := by
  classical
  dsimp only
  let L := Fintype.card K - 1
  obtain ⟨r, _, hr⟩ := FiniteField.card K 3
  have hodd : Odd (Fintype.card K) := by rw [hr]; exact (by decide : Odd 3).pow
  have hthree : 3 ≤ Fintype.card K := by
    rw [hr]
    exact Nat.le_pow r.pos
  have hL : 2 ≤ L := by dsimp [L]; omega
  have heven : Even L := by
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    dsimp [L]
    omega
  obtain ⟨a, haord⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Fintype.card Kˣ = L := Fintype.card_units K
  have hord : orderOf a = L := by simpa [Nat.card_eq_fintype_card, hcard] using haord
  have ha : (a : K) ≠ 1 := by
    intro h
    have hunit : a = 1 := Units.ext h
    rw [hunit, orderOf_one] at hord
    omega
  let e := Equiv.ofBijective _ (orbit_bijective a hord hcard (by omega) heven)
  refine ⟨a, ha, hord, hL, heven, e, (fun _ => rfl), ?_, ?_, label_difference a ha⟩
  · have h := block_laps a hord (by omega) heven 3 0
    have hz : (3 : ZMod 3) = 0 := by decide
    simpa only [Nat.cast_ofNat, zero_add, hz, mul_comm] using h
  · exact (labels_bijective a ha).comp e.bijective

#print axioms exists_cycle_inventory

end D5.S1.Words.Sequenceability.CharacteristicThreeCycle
