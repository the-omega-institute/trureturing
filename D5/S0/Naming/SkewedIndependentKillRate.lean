/- GID: D5/S0/Naming/SkewedIndependentKillRate
   generality: G
   mirror-B: D5/B/S0/Naming/SkewedIndependentKillRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Biased behavior replaces the uniform fixed fraction by weighted fixed mass. -/

/- Library-search audit trail (2026-08-31):
   * The repository already has the exact weighted fixed-mass complement in
     `SkewedEscapeMass.escape_mass_eq_one_sub_fixed_mass`.
   * The repository also has the exact independent event product law in
     `IndependentKillRate.independent_kill_rate`.
   * These exact local owners compose directly, so no duplicate local or external proof
     was introduced.
-/

import D5.S0.Asymptotics.SkewedEscapeMass
import D5.S0.Naming.IndependentKillRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace D5.S0.Naming.SkewedIndependentKillRate

open D5.S0.Asymptotics.SkewedEscapeMass
open D5.S0.Naming.IndependentKillRate

noncomputable section

local instance (priority := low) (p : Prop) : Decidable p := Classical.propDecidable p

variable {Y Outcome : Type*} [Fintype Y] [MeasurableSpace Outcome]

/-- Under a finite behavior distribution, the invisible mass is the weighted fixed-point
mass, and independent coverage and visibility give the correspondingly skewed kill rate. -/
theorem skewed_independent_kill_rate
    (q : PMF Y) (f : Y -> Y)
    (measure : Measure Outcome) (covered visible : Set Outcome)
    (coverageRate : ENNReal)
    (independent : IndepSet covered visible measure)
    (coverage : measure covered = coverageRate)
    (visibility : measure visible = escapeMass q f) :
    escapeMass q f = 1 - fixedMass q f /\
      escapeMass q f = 1 - (∑ y ∈ Finset.univ.filter (fun y => f y = y), q y) /\
      measure (covered ∩ visible) = coverageRate * (1 - fixedMass q f) := by
  have fixed_mass_sum :
      fixedMass q f = ∑ y ∈ Finset.univ.filter (fun y => f y = y), q y := by
    simp only [fixedMass]
  constructor
  · fail_if_success rfl
    fail_if_success ((try intros); simp only [escapeMass, fixedMass]; assumption)
    exact escape_mass_eq_one_sub_fixed_mass q f
  constructor
  · fail_if_success rfl
    fail_if_success ((try intros); simp only [escapeMass, fixedMass]; assumption)
    calc
      escapeMass q f = 1 - fixedMass q f :=
        escape_mass_eq_one_sub_fixed_mass q f
      _ = 1 - (∑ y ∈ Finset.univ.filter (fun y => f y = y), q y) := by
        rw [fixed_mass_sum]
  · fail_if_success rfl
    fail_if_success ((try intros); simp only [fixedMass]; assumption)
    calc
      measure (covered ∩ visible) = coverageRate * escapeMass q f :=
        independent_kill_rate measure covered visible coverageRate (escapeMass q f)
          independent coverage visibility
      _ = coverageRate * (1 - fixedMass q f) := by
        rw [escape_mass_eq_one_sub_fixed_mass q f]

#print axioms skewed_independent_kill_rate

end

end D5.S0.Naming.SkewedIndependentKillRate
