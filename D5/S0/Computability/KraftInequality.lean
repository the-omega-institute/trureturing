/- GID: D5/S0/Computability/KraftInequality
   generality: G
   mirror-B: D5/B/S0/Computability/KraftInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite uniquely decodable binary codes satisfy the Kraft inequality. -/

import Mathlib.InformationTheory.Coding.KraftMcMillan

namespace D5.S0.Computability.KraftInequality

/-- Finite binary uniquely decodable codes have Kraft sum at most one.

This is the finite-code partial closure of the source fact: pinned mathlib's
Kraft-McMillan theorem is applied without reproving its counting argument.
-/
theorem finite_binary_kraft_inequality {S : Finset (List (Fin 2))}
    (h : InformationTheory.UniquelyDecodable (S : Set (List (Fin 2)))) :
    ∑ w ∈ S, (1 / Fintype.card (Fin 2) : ℝ) ^ w.length ≤ 1 := by
  exact InformationTheory.kraft_mcmillan_inequality h

end D5.S0.Computability.KraftInequality
