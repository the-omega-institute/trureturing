/- GID: D5/S0/Asymptotics/WeightedProbability/EscapeMassBridge
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: PMF escape mass equals the one-address weighted escape probability. -/

/- Library-search audit trail (2026-08-15, pinned at f55d621):
   * Repository searches for the final theorem name and for declarations mentioning both
     `escapeMass` and `escapeProbability` found no existing bridge.
   * Repository searches found the two complement laws
     `SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass` and
     `SkewedCaptureBounds.one_address_escape_probability`, together with
     `FiniteProductCapture.fixedMass_pmf_toReal` for their common fixed mass.
   * Pinned Mathlib searches found `ENNReal.toReal_sub_of_le`, `PMF.tsum_coe`, and
     `PMF.apply_ne_top`, which discharge the coercion and normalization side conditions.
-/

import D5.S0.Asymptotics.WeightedProbability.SkewedCaptureBounds

open scoped BigOperators

namespace D5.S0.Asymptotics.WeightedProbability.EscapeMassBridge

/-- The PMF-valued one-slot escape mass is the real weighted escape probability on one address. -/
theorem escapeMass_toReal_eq_one_address_escapeProbability
    {Y : Type*} [Fintype Y] (q : PMF Y) (f : Y -> Y) :
    (D5.S0.Asymptotics.SkewedEscapeMass.escapeMass q f).toReal =
      D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni.escapeProbability
        (A := Fin 1) (fun _ y => (q y).toReal) f := by
  classical
  have hfixed_le_one :
      D5.S0.Asymptotics.SkewedEscapeMass.fixedMass q f <= 1 := by
    rw [D5.S0.Asymptotics.SkewedEscapeMass.fixedMass]
    calc
      (∑ y ∈ Finset.univ.filter (fun y => f y = y), q y) <=
          ∑ y : Y, q y := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = 1 := by simpa using q.tsum_coe
  have hq_sum : forall _ : Fin 1, ∑ y : Y, (q y).toReal = 1 := by
    intro _
    have hq_enn : (∑ y : Y, q y) = 1 := by simpa using q.tsum_coe
    calc
      (∑ y : Y, (q y).toReal) = (∑ y : Y, q y).toReal := by
        symm
        exact ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top q y)
      _ = 1 := by rw [hq_enn]; simp
  calc
    (D5.S0.Asymptotics.SkewedEscapeMass.escapeMass q f).toReal =
        1 - (D5.S0.Asymptotics.SkewedEscapeMass.fixedMass q f).toReal := by
      rw [D5.S0.Asymptotics.SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass]
      exact ENNReal.toReal_sub_of_le hfixed_le_one (by simp)
    _ = 1 -
        D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture.fixedMass
          (A := Fin 1) (fun _ y => (q y).toReal) f 0 := by
      rw [D5.S0.Asymptotics.WeightedProbability.FiniteProductCapture.fixedMass_pmf_toReal]
    _ = D5.S0.Asymptotics.WeightedProbability.FiniteBonferroni.escapeProbability
        (A := Fin 1) (fun _ y => (q y).toReal) f := by
      symm
      exact
        D5.S0.Asymptotics.WeightedProbability.SkewedCaptureBounds.one_address_escape_probability
          (fun _ y => (q y).toReal) (by
            intro _ y
            exact ENNReal.toReal_nonneg) hq_sum f

#print axioms escapeMass_toReal_eq_one_address_escapeProbability

end D5.S0.Asymptotics.WeightedProbability.EscapeMassBridge
