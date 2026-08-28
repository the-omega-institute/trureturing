/- GID: D5/S3/ConceptDynamics/Causal/PrincipalStrata
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PrincipalStrata
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Monotone Boolean potential outcomes have three strata fixed by their marginals. -/

import Mathlib

/- Library-search audit trail (2026-08-26):
   * Searches of `D5` and `Golden/Frozen/accepted` for `principal_strata`,
     `principal strata`, and the harmful/beneficial joint-mass body shapes
     returned no matching declaration.
   * Searches of the existing causal, attribution, and intervention families
     found Boolean structural-model marginals, but no probability law on
     potential-outcome pairs or principal-stratum theorem.
   * A pinned Mathlib search for principal strata, potential outcomes, benefit
     probability, Frechet bounds, and counterfactuals returned no exact hit.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PrincipalStrata

/-- A normalized nonnegative joint mass on Boolean potential outcomes, whose
positive-mass response types are monotone, excludes the harmful type. The
remaining three type masses are determined by the treatment-one and
treatment-zero marginals. -/
theorem principal_strata
    (mass : Bool × Bool -> Real)
    (mass_nonnegative : forall pair, 0 <= mass pair)
    (mass_total :
      mass (false, false) + mass (false, true) +
          mass (true, false) + mass (true, true) = 1)
    (monotonicity :
      forall pair, 0 < mass pair -> pair.1 = true -> pair.2 = true) :
    mass (true, false) = 0 /\
      mass (false, false) = 1 - (mass (false, true) + mass (true, true)) /\
      mass (false, true) =
        (mass (false, true) + mass (true, true)) -
          (mass (true, false) + mass (true, true)) /\
      mass (true, true) = mass (true, false) + mass (true, true) := by
  have excluded : mass (true, false) = 0 := by
    by_contra nonzero
    have positive : 0 < mass (true, false) :=
      lt_of_le_of_ne (mass_nonnegative _) (Ne.symm nonzero)
    have impossible := monotonicity (true, false) positive rfl
    simp at impossible
  constructor
  · exact excluded
  constructor
  · linarith [mass_total]
  constructor <;> linarith

#print axioms principal_strata

end D5.S3.ConceptDynamics.Causal.PrincipalStrata
