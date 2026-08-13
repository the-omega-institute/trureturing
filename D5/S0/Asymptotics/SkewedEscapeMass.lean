/- GID: D5/S0/Asymptotics/SkewedEscapeMass
   generality: G
   mirror-B: D5/B/S0/Asymptotics/SkewedEscapeMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A one-slot skewed escape mass is one minus the fixed-output mass. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators

namespace D5.S0.Asymptotics.SkewedEscapeMass

open ENNReal

noncomputable section

variable {Y : Type*} [Fintype Y] (q : PMF Y) (f : Y → Y)

/-- The skewed one-slot mass of outputs changed by the output transformation. -/
noncomputable def escapeMass (q : PMF Y) (f : Y → Y) : ℝ≥0∞ :=
  by classical exact ∑ y ∈ Finset.univ.filter (fun y => f y ≠ y), q y

/-- The skewed one-slot mass of outputs fixed by the output transformation. -/
noncomputable def fixedMass (q : PMF Y) (f : Y → Y) : ℝ≥0∞ :=
  by classical exact ∑ y ∈ Finset.univ.filter (fun y => f y = y), q y

/-- The one-slot escape probability is the complement of the fixed-output mass.

This is the `A = 1` edge clause of the skewed candidate: the empty product is one,
while the two filtered output classes partition the finite PMF mass. -/
theorem escape_mass_eq_one_sub_fixed_mass :
    escapeMass q f = 1 - fixedMass q f := by
  classical
  rw [escapeMass, fixedMass]
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset Y))
      (p := fun y => f y ≠ y) (f := fun y => q y)
  have hsum :
      (∑ y ∈ Finset.univ.filter (fun y => f y ≠ y), q y) +
          ∑ y ∈ Finset.univ.filter (fun y => f y = y), q y = 1 := by
    calc
      (∑ y ∈ Finset.univ.filter (fun y => f y ≠ y), q y) +
            ∑ y ∈ Finset.univ.filter (fun y => f y = y), q y =
          (∑ y ∈ Finset.univ.filter (fun y => f y ≠ y), q y) +
            ∑ y ∈ Finset.univ.filter (fun y => ¬(f y ≠ y)), q y := by
              congr 1
              simp
      _ = ∑ y ∈ (Finset.univ : Finset Y), q y := hpartition
      _ = 1 := by simpa using q.tsum_coe
  exact ENNReal.eq_sub_of_add_eq' (by simp) hsum

example : Nonempty (Fin 1) := inferInstance

#print axioms escape_mass_eq_one_sub_fixed_mass

end

end D5.S0.Asymptotics.SkewedEscapeMass
