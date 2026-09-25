/- GID: D5/S3/Combinatorics/ArrowWilfEquivalence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfEquivalence
   mirror-E: none(waiver:arrow-wilf-equivalence-for-two-three-letter-patterns)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: The two arrow-pattern avoidance classes have equal cardinality in every positive degree. -/

import D5.S3.Combinatorics.ArrowWilfTwelveFormula
import D5.S3.Combinatorics.ArrowWilfTwentyThreeFormula

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfEquivalence

open D5.S3.Combinatorics.ArrowWilfDefs

theorem result : claim := by
  intro n hn
  have hF : D5.S3.Combinatorics.ArrowWilfSums.F1 n = D5.S3.Combinatorics.ArrowWilfSums.F2 n := by
    have h : (D5.S3.Combinatorics.ArrowWilfSums.F1 n : ℤ) =
        (D5.S3.Combinatorics.ArrowWilfSums.F2 n : ℤ) := by
      dsimp [D5.S3.Combinatorics.ArrowWilfSums.F1, D5.S3.Combinatorics.ArrowWilfSums.F2]
      rw [D5.S3.Combinatorics.ArrowWilfSums.f1_correction_eq_E n,
        ← D5.S3.Combinatorics.ArrowWilfSums.f2_correction_eq_E n hn]
      ring
    exact_mod_cast h
  exact (D5.S3.Combinatorics.ArrowWilfTwelveFormula.card_twelve_avoiders n hn).trans
    (hF.trans (D5.S3.Combinatorics.ArrowWilfTwentyThreeFormula.card_twentyThree_avoiders n hn).symm)

end D5.S3.Combinatorics.ArrowWilfEquivalence
