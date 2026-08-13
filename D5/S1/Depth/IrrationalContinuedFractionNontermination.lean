/- GID: D5/S1/Depth/IrrationalContinuedFractionNontermination
   generality: G
   mirror-B: D5/B/S1/Depth/IrrationalContinuedFractionNontermination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An irrational real has a nonterminating continued-fraction computation. -/

import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.NumberTheory.Real.Irrational

namespace D5.S1.Depth.IrrationalContinuedFractionNontermination

/- Provenance: Thin wrapper around Mathlib's rationality criterion. -/

theorem irrational_continued_fraction_nontermination {x : ℝ} (hx : Irrational x) :
    ¬(GenContFract.of x).Terminates := by
  intro hterm
  rcases (GenContFract.terminates_iff_rat x).mp hterm with ⟨q, hq⟩
  exact hx ⟨q, hq.symm⟩

end D5.S1.Depth.IrrationalContinuedFractionNontermination
