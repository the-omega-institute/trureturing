/- GID: D5/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/StrictAddressMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.SuccPred.Archimedean]
   digest: A fixed point makes escape probability strictly increase with positive address counts. -/

/- Library-search audit trail (2026-08-16):
   * Repository and all-local-ref searches found no strict comparison of the
     frozen escape probability at two different positive address counts.
   * Pinned Mathlib's `strictMonoOn_of_lt_succ` is the exact step-to-interval
     theorem applied below after proving the successor inequality.
   * Pinned Mathlib's `pow_le_of_le_one` controls the auxiliary power in that
     successor inequality. The frozen closed form is applied at both endpoints.
-/

import D5.S0.Asymptotics.EscapeProbabilityMonotone
import D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit
import Mathlib.Order.SuccPred.Archimedean

namespace D5.S0.Asymptotics.EscapeProbability.StrictAddressMonotonicity

open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Asymptotics.EscapeProbability.PoissonDomainLimit

/-- If the output alphabet has at least two symbols and the twist has a fixed
point, escape probability is strictly increasing on positive address counts. -/
theorem escape_probability_strictMonoOn_of_has_fixed_point
    {Y : Type*} [Fintype Y] [Nonempty Y] (f : Y -> Y)
    (hn : 2 <= Fintype.card Y)
    (hfix : 0 < Nat.card {y : Y // f y = y}) :
    StrictMonoOn (fun A : Nat => escapeProbability (A := Fin A) f) (Set.Ici 1) := by
  classical
  let n := Fintype.card Y
  let k := Nat.card {y : Y // f y = y}
  have hn_nat : 2 <= n := hn
  have hk_nat : k <= n := by
    dsimp [k, n]
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hk_pos_nat : 0 < k := hfix
  apply strictMonoOn_of_lt_succ Set.ordConnected_Ici
  intro a _ ha _
  have ha_nat : 1 <= a := ha
  change escapeProbability (A := Fin a) f <
    escapeProbability (A := Fin (a + 1)) f
  rw [escape_probability_closed_form f a,
    escape_probability_closed_form f (a + 1)]
  change (1 - (k : Real) / (n : Real) ^ a) ^ a <
    (1 - (k : Real) / (n : Real) ^ (a + 1)) ^ (a + 1)
  have hn0 : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : Real) <= n := by exact_mod_cast hn_nat
  have hk0 : (0 : Real) < k := by exact_mod_cast hk_pos_nat
  have hk_le_n : (k : Real) <= n := by exact_mod_cast hk_nat
  let x : Real := (k : Real) / (n : Real) ^ a
  let u : Real := 1 - x / n
  let v : Real := 1 - x
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : x <= 1 := by
    dsimp [x]
    apply (div_le_one (by positivity)).mpr
    exact hk_le_n.trans (by
      exact_mod_cast (Nat.le_pow (a := n) (b := a) (by omega)))
  have hu0 : 0 < u := by
    dsimp [u]
    apply sub_pos.mpr
    apply (div_lt_one hn0).mpr
    linarith
  let q : Real := x * (n - 1) / (n - x)
  have hden : 0 < (n : Real) - x := by linarith
  have hq0 : 0 <= q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg hx0.le (sub_nonneg.mpr (by linarith))) hden.le
  have hq1 : q <= 1 := by
    dsimp [q]
    apply (div_le_one hden).mpr
    have hxn : x * (n : Real) <= n := by
      simpa using (mul_le_mul_of_nonneg_right hx1 hn0.le)
    nlinarith [hxn]
  have hq_gt : x / n < q := by
    dsimp [q]
    field_simp [ne_of_gt hn0, ne_of_gt hden]
    have hinner : 0 < (n : Real) * (n - 2) + x := by
      have hn_sub : 0 <= (n : Real) - 2 := by linarith
      have hprod : 0 <= (n : Real) * (n - 2) :=
        mul_nonneg hn0.le hn_sub
      linarith
    have hstrict : 0 < x * ((n : Real) * (n - 2) + x) :=
      mul_pos hx0 hinner
    nlinarith
  have hpow : (1 - q) ^ a <= 1 - q := by
    apply pow_le_of_le_one
    · linarith
    · linarith
    · omega
  have hrel : v = u * (1 - q) := by
    dsimp [v, u, q]
    field_simp [ne_of_gt hn0, ne_of_gt hden]
    ring
  have hright : 1 - q < u := by
    dsimp [u]
    linarith
  calc
    (1 - (k : Real) / (n : Real) ^ a) ^ a = v ^ a := rfl
    _ = u ^ a * (1 - q) ^ a := by rw [hrel, mul_pow]
    _ <= u ^ a * (1 - q) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ < u ^ a * u := mul_lt_mul_of_pos_left hright (pow_pos hu0 a)
    _ = (1 - (k : Real) / (n : Real) ^ (a + 1)) ^ (a + 1) := by
      dsimp [u, x]
      rw [pow_succ]
      field_simp [ne_of_gt hn0]
      ring

example : Nonempty (Fin 2) := inferInstance

example : 0 < Nat.card {y : Fin 2 // (id : Fin 2 -> Fin 2) y = y} := by
  simp [Nat.card_eq_fintype_card]

example : StrictMonoOn
    (fun A : Nat => escapeProbability (A := Fin A) (id : Fin 2 -> Fin 2))
    (Set.Ici 1) := by
  exact escape_probability_strictMonoOn_of_has_fixed_point
    (id : Fin 2 -> Fin 2) (by decide) (by simp [Nat.card_eq_fintype_card])

#print axioms escape_probability_strictMonoOn_of_has_fixed_point

end D5.S0.Asymptotics.EscapeProbability.StrictAddressMonotonicity
