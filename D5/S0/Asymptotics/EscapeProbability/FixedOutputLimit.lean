/- GID: D5/S0/Asymptotics/EscapeProbability/FixedOutputLimit
   generality: G
   mirror-B: D5/B/S0/Asymptotics/EscapeProbability/FixedOutputLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Escape probability tends to one as addresses grow for a fixed output alphabet. -/

import D5.S0.Asymptotics.FixedPointFreeEscapeProbability
import D5.S0.Diagonal.EscapeAsymptotics

namespace D5.S0.Asymptotics.EscapeProbability.FixedOutputLimit

open Filter
open D5.S0.Asymptotics.FixedPointFreeEscapeProbability
open D5.S0.Diagonal.EscapeCount

/-- The frozen escape probability is exactly the uniform ratio of listings
satisfying `IsEscaped`. If the finite output alphabet has at least two symbols,
that probability tends to one as the address cardinality tends to infinity. -/
theorem fixed_output_large_address_escape_probability
    {Y : Type*} [Fintype Y] [Nonempty Y] (f : Y -> Y)
    (hn : 2 <= Fintype.card Y) :
    Tendsto (fun A : Nat => escapeProbability (A := Fin A) f)
      atTop (nhds 1) := by
  classical
  have hk : Nat.card {y : Y // f y = y} <= Fintype.card Y := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hratio := D5.S0.Diagonal.EscapeAsymptotics.escape_ratio_tendsto_one
    (Fintype.card Y) (Nat.card {y : Y // f y = y}) hn hk
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with A hA
  symm
  rw [escapeProbability, escaped_listing_card]
  have hkpow : Nat.card {y : Y // f y = y} <= Fintype.card Y ^ A :=
    hk.trans (Nat.le_pow (a := Fintype.card Y) (b := A) (by omega))
  have hksub :
      Fintype.card {y : Y // f y = y} <= Fintype.card Y ^ A := by
    simpa [Nat.card_eq_fintype_card] using hkpow
  have hden : (Fintype.card (Fin A -> Fin A -> Y) : Real) =
      (Fintype.card Y : Real) ^ (A * A) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    norm_num [Nat.cast_pow, pow_mul]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.cast_pow, Nat.cast_sub hksub, hden]
  have hpow : (Fintype.card Y : Real) ^ A ≠ 0 := by positivity
  have hbase :
      ((Fintype.card Y ^ A - Fintype.card {y : Y // f y = y} : Nat) : Real) /
          (Fintype.card Y : Real) ^ A =
        1 - (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A := by
    rw [Nat.cast_sub hksub, Nat.cast_pow, Nat.card_eq_fintype_card]
    field_simp [hpow]
  rw [Nat.cast_pow]
  have hpow_div :
      ((Fintype.card Y : Real) ^ A -
          Fintype.card {y : Y // f y = y}) ^ A /
          (Fintype.card Y : Real) ^ (A * A) =
        (1 - (Nat.card {y : Y // f y = y} : Real) /
          (Fintype.card Y : Real) ^ A) ^ A := by
    calc
      _ = (((Fintype.card Y ^ A -
          Fintype.card {y : Y // f y = y} : Nat) : Real) /
            (Fintype.card Y : Real) ^ A) ^ A := by
              rw [Nat.cast_sub hksub, Nat.cast_pow, div_pow, pow_mul]
      _ = _ := by rw [hbase]
  simpa only [Nat.card_eq_fintype_card] using hpow_div

/-- The finite output domain used by the hypothesis witness is inhabited. -/
example : Nonempty (Fin 2) := inferInstance

/-- The theorem's fixed-output hypothesis bundle is jointly satisfiable. -/
example : ∃ f : Fin 2 -> Fin 2, f = id ∧ 2 <= Fintype.card (Fin 2) := by
  exact ⟨id, rfl, by decide⟩

#print axioms fixed_output_large_address_escape_probability

end D5.S0.Asymptotics.EscapeProbability.FixedOutputLimit
