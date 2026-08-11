/- GID: D5/S3/PrimeForms/QuadraticResidueCounterexample
   generality: I
   mirror-B: D5/B/S3/PrimeForms/QuadraticResidueCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The prime two refutes the unqualified quadratic-residue equivalence. -/

import D5.S3.PrimeForms.GoldenPrimeClassification

namespace D5.S3.PrimeForms.QuadraticResidueCounterexample

/-- The quadratic-residue equivalence without the odd-prime hypothesis fails
at the prime two: five is a square modulo two, but two is not congruent to plus
or minus one modulo five. -/
theorem two_refutes_unqualified_quadratic_residue_equivalence :
    ¬ (IsSquare (5 : ZMod 2) ↔ 2 % 5 = 1 ∨ 2 % 5 = 4) := by
  intro h
  have hsquare : IsSquare (5 : ZMod 2) := ⟨1, by decide⟩
  have hclass := h.mp hsquare
  norm_num at hclass

end D5.S3.PrimeForms.QuadraticResidueCounterexample
