/- GID: D5/S1/Words/AbelianBorders/AbelianBorderQuestion
   generality: G
   mirror-B: D5/B/S1/Words/AbelianBorders/AbelianBorderQuestion
   mirror-E: none(waiver:external-open-problem-refutation)
   anchors: []
   utility: none
   digest: A ternary infinite word refutes the abelian-border periodicity question. -/

/- proof_shape: result: bind-only
   admission_basis: open-problem-resolution
   claim: D5/S1/Words/AbelianBorders/AbelianBorderQuestionDefs.claim
   result: D5/S1/Words/AbelianBorders/AbelianBorderQuestion.result
   computational_content.kind: none
   The refutation depends on arbitrary-prefix induction, continuous supporting geometry,
   border exclusion for arbitrary lengths, and an infinite square-gap construction.
   Its block-state computations are local parts of these symbolic arguments. -/

import D5.S1.Words.AbelianBorders.AbelianBorderQuestionGeometry
import D5.S1.Words.AbelianBorders.AbelianBorderQuestionFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.AbelianBorders.AbelianBorderQuestion

/-- Question 2 of Charlier–Harju–Puzynina–Zamboni has a negative answer,
including when a border is allowed to use the whole word as its suffix. -/
theorem result : ¬ AbelianBorderQuestionDefs.claim := by
  intro h
  exact Counterexample.infinitely_many_unbordered
    (h 3 Counterexample.word Counterexample.word_structure.2.2 Counterexample.geometric)

end D5.S1.Words.AbelianBorders.AbelianBorderQuestion
