/- GID: D5/S0/Asymptotics/EscapeProbabilityMonotone
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbabilityMonotone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Escape probability is monotone in guarded address cardinality and has the one-address value. -/

import D5.S0.Asymptotics.FixedPointFreeEscapeProbability
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace D5.S0.Asymptotics.EscapeProbabilityMonotone

open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Diagonal.EscapeCount

private theorem fixed_points_le_power {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y → Y) {a : ℕ} (ha : 1 ≤ a) :
    Nat.card {y : Y // f y = y} ≤ Fintype.card Y ^ a := by
  classical
  letI : Fintype {y : Y // f y = y} := Fintype.ofFinite _
  have hk : Nat.card {y : Y // f y = y} ≤ Fintype.card Y := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hn : 0 < Fintype.card Y := Fintype.card_pos
  exact hk.trans (Nat.le_pow (a := Fintype.card Y) (b := a) (by omega))

private theorem escape_probability_formula {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y → Y) {a : ℕ} (ha : 1 ≤ a) :
    escapeProbability (A := Fin a) f =
      (1 - (Nat.card {y : Y // f y = y} : ℝ) /
        (Fintype.card Y : ℝ) ^ a) ^ a := by
  classical
  rw [escapeProbability, escaped_listing_card]
  have hk : Nat.card {y : Y // f y = y} ≤ Fintype.card Y ^ a :=
    fixed_points_le_power f ha
  have hksub : Fintype.card {y : Y // f y = y} ≤ Fintype.card Y ^ a := by
    simpa [Nat.card_eq_fintype_card] using hk
  have hn : 0 < Fintype.card Y := Fintype.card_pos
  have hden : (Fintype.card (Fin a → Fin a → Y) : ℝ) =
      (Fintype.card Y : ℝ) ^ (a * a) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    norm_num [Nat.cast_pow, pow_mul]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.cast_pow, Nat.cast_sub hksub, hden]
  have hpow : (Fintype.card Y : ℝ) ^ a ≠ 0 := by positivity
  have hbase :
      ((Fintype.card Y ^ a - Fintype.card {y : Y // f y = y} : ℕ) : ℝ) /
          (Fintype.card Y : ℝ) ^ a =
        1 - (Nat.card {y : Y // f y = y} : ℝ) /
          (Fintype.card Y : ℝ) ^ a := by
    rw [Nat.cast_sub hksub, Nat.cast_pow, Nat.card_eq_fintype_card]
    field_simp [hpow]
  rw [Nat.cast_pow]
  have hpow_div :
      (↑(Fintype.card Y) ^ a - ↑(Fintype.card {y : Y // f y = y})) ^ a /
          (↑(Fintype.card Y) ^ (a * a)) =
        (1 - (Nat.card {y : Y // f y = y} : ℝ) /
          (Fintype.card Y : ℝ) ^ a) ^ a := by
    calc
      _ = (((Fintype.card Y ^ a - Fintype.card {y : Y // f y = y} : ℕ) : ℝ) /
          (Fintype.card Y : ℝ) ^ a) ^ a := by
            rw [Nat.cast_sub hksub, Nat.cast_pow, div_pow, pow_mul]
      _ = _ := by
        rw [hbase]
  simpa only [Nat.card_eq_fintype_card] using hpow_div

private theorem step_inequality {n k a : ℕ} (hn : 2 ≤ n) (hk : k ≤ n)
    (ha : 1 ≤ a) :
    (1 - (k : ℝ) / (n : ℝ) ^ a) ^ a ≤
      (1 - (k : ℝ) / (n : ℝ) ^ (a + 1)) ^ (a + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
  have hk_le_n : (k : ℝ) ≤ n := by exact_mod_cast hk
  let x : ℝ := (k : ℝ) / (n : ℝ) ^ a
  let u : ℝ := 1 - x / n
  let v : ℝ := 1 - x
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one (by positivity)).mpr
    exact hk_le_n.trans (by
      exact_mod_cast (Nat.le_pow (a := n) (b := a) (by omega)))
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu0 : 0 ≤ u := by
    dsimp [u]
    apply sub_nonneg.mpr
    exact (div_le_one (by positivity)).mpr (by linarith [hx1])
  let q : ℝ := x * (n - 1) / (n - x)
  have hden : 0 < (n : ℝ) - x := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    apply (div_le_one hden).mpr
    have hxn : x * (n : ℝ) ≤ n := by
      simpa using (mul_le_mul_of_nonneg_right hx1 hn0.le)
    nlinarith [hxn]
  have hq_ge : x / n ≤ q := by
    dsimp [q]
    field_simp [ne_of_gt hn0, ne_of_gt hden]
    have hprod : 0 ≤ x * ((n : ℝ) - 1) := mul_nonneg hx0 (by linarith)
    nlinarith [sq_nonneg ((n : ℝ) - 2), hprod]
  have hpow : (1 - q) ^ a ≤ 1 - q := by
    apply pow_le_of_le_one
    · linarith
    · linarith
    · omega
  have hrel : v = u * (1 - q) := by
    dsimp [v, u, q]
    field_simp [ne_of_gt hn0, ne_of_gt hden]
    ring
  have hright : 1 - q ≤ u := by
    dsimp [u]
    linarith [hq_ge]
  calc
    (1 - (k : ℝ) / (n : ℝ) ^ a) ^ a = v ^ a := rfl
    _ = u ^ a * (1 - q) ^ a := by rw [hrel, mul_pow]
    _ ≤ u ^ a * (1 - q) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ u ^ a * u := mul_le_mul_of_nonneg_left hright (by positivity)
    _ = (1 - (k : ℝ) / (n : ℝ) ^ (a + 1)) ^ (a + 1) := by
      dsimp [u, x]
      rw [pow_succ]
      field_simp [ne_of_gt hn0]
      ring

private theorem step_inequality_of_positive {n k a : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (ha : 1 ≤ a) :
    (1 - (k : ℝ) / (n : ℝ) ^ a) ^ a ≤
      (1 - (k : ℝ) / (n : ℝ) ^ (a + 1)) ^ (a + 1) := by
  by_cases htwo : 2 ≤ n
  · exact step_inequality htwo hk ha
  · have hn1 : n = 1 := by omega
    subst n
    interval_cases k <;> simp [Nat.ne_zero_of_lt (by omega : 0 < a)]

theorem escape_probability_monotone_on_guarded_domain {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y → Y) :
    MonotoneOn (fun a : ℕ => escapeProbability (A := Fin a) f) {a | 1 ≤ a} := by
  intro a ha b hb hab
  have haNat : 1 ≤ a := ha
  have hbNat : 1 ≤ b := hb
  change escapeProbability (A := Fin a) f ≤ escapeProbability (A := Fin b) f
  rw [escape_probability_formula f haNat, escape_probability_formula f hbNat]
  apply Nat.le_induction (m := a) (P := fun b _ =>
    (1 - (Nat.card {y : Y // f y = y} : ℝ) /
      (Fintype.card Y : ℝ) ^ a) ^ a ≤
    (1 - (Nat.card {y : Y // f y = y} : ℝ) /
      (Fintype.card Y : ℝ) ^ b) ^ b)
  · rfl
  · intro b hab ih
    exact ih.trans (step_inequality_of_positive (Fintype.card_pos) (by
      classical
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_le _
    ) (by omega))
  · exact hab

theorem escape_probability_one_address {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y → Y) :
    escapeProbability (A := Fin 1) f =
      1 - (Nat.card {y : Y // f y = y} : ℝ) / Fintype.card Y := by
  rw [escape_probability_formula f (by decide)]
  norm_num

theorem escape_probability_monotone_and_one_address {Y : Type*} [Fintype Y] [Nonempty Y]
    (f : Y → Y) :
    (∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a ≤ b →
      escapeProbability (A := Fin a) f ≤ escapeProbability (A := Fin b) f) ∧
      escapeProbability (A := Fin 1) f =
        1 - (Nat.card {y : Y // f y = y} : ℝ) / Fintype.card Y := by
  constructor
  · intro a b ha hb hab
    exact escape_probability_monotone_on_guarded_domain f ha hb hab
  · exact escape_probability_one_address f

example : ∃ (Y : Type) (_ : Fintype Y) (_ : Nonempty Y),
    ∃ f : Y → Y, 2 ≤ Fintype.card Y := by
  let Y := Fin 2
  letI : Fintype Y := inferInstance
  letI : Nonempty Y := ⟨0⟩
  exact ⟨Y, inferInstance, inferInstance, id, by decide⟩

example : Nonempty (Fin 1) := inferInstance

example (Y : Type) [Fintype Y] [Nonempty Y] (f : Y → Y) :
    1 ≤ Fintype.card Y →
      escapeProbability (A := Fin 1) f =
        1 - (Nat.card {y : Y // f y = y} : ℝ) / Fintype.card Y := by
  intro _
  exact escape_probability_one_address f

end D5.S0.Asymptotics.EscapeProbabilityMonotone
