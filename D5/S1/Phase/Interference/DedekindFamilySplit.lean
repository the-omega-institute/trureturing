/- GID: D5/S1/Phase/Interference/DedekindFamilySplit
   generality: G
   mirror-B: D5/B/S1/Phase/Interference/DedekindFamilySplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Dedekind ledger splits into its alternating walk and endpoint translation. -/

import D5.S1.Phase.WalkFormula
import Mathlib.Tactic.Ring

namespace D5.S1.Phase.Interference.DedekindFamilySplit

open D5.S1.Phase.WalkFormula

/-- The endpoint-corrected phase formula and the relation `psi = phi - 3`
split the oriented Dedekind ledger into the alternating walk plus its integral
endpoint translation. -/
theorem dedekind_family_split
    (coefficients : List Int) (phi psi : Rat)
    (endpoint endpoint' c translation : Int) (hc : c ≠ 0)
    (hPhi : phi = 3 + (alternatingWalk coefficients : Rat) +
      ((endpoint - endpoint' : Int) : Rat) / (c : Rat))
    (hPsi : psi = phi - 3)
    (hTranslation : endpoint - endpoint' = c * translation) :
    psi = (alternatingWalk coefficients : Rat) + (translation : Rat) := by
  have hCorrection :=
    endpoint_correction_is_integer endpoint endpoint' c translation hc hTranslation
  rw [hPsi, hPhi, hCorrection]
  ring

example : Nonempty (List Int) := ⟨[]⟩

example : ∃ (coefficients : List Int) (phi psi : Rat)
    (endpoint endpoint' c translation : Int),
    c ≠ 0 ∧
      phi = 3 + (alternatingWalk coefficients : Rat) +
        ((endpoint - endpoint' : Int) : Rat) / (c : Rat) ∧
      psi = phi - 3 ∧ endpoint - endpoint' = c * translation := by
  refine ⟨[2, 1], 6, 3, 6, 0, 3, 2, by norm_num, ?_, by norm_num, by norm_num⟩
  norm_num [alternatingWalk]

example : ¬ ((0 : Rat) = (alternatingWalk [1] : Rat) + (1 : Rat)) := by
  norm_num [alternatingWalk]

#print axioms dedekind_family_split

end D5.S1.Phase.Interference.DedekindFamilySplit
