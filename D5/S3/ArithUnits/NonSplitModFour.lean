/- GID: D5/S3/ArithUnits/NonSplitModFour
   generality: I
   mirror-B: D5/B/S3/ArithUnits/NonSplitModFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The reduction from ZMod 4 to ZMod 2 has no additive section. -/

import Mathlib.Data.ZMod.Basic

/- Library-search audit trail (2026-08-17):
   * Repository searches found no D5 declaration that the reduction from `ZMod 4` to
     `ZMod 2` has no additive section.
   * Pinned Mathlib and the local smart-search script found `ZMod.castHom` and `ZMod.lift`,
     but no theorem asserting this concrete quotient is non-split.
   * The configured GitHub API credential was expired, so its code-search request failed.
     A NyxID-proxied Tavily search over GitHub, Loogle, and LeanSearch indexes found the same
     quotient-map infrastructure but no complete non-splitting theorem. -/

namespace D5.S3.ArithUnits.NonSplitModFour

/-- The additive quotient map from `ZMod 4` to `ZMod 2` has no additive right inverse. -/
theorem mod_four_quotient_has_no_additive_section :
    ¬ ∃ s : ZMod 2 →+ ZMod 4,
      Function.RightInverse s (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) := by
  rintro ⟨s, hs⟩
  have htwo : 2 • s (1 : ZMod 2) = 0 := by
    calc
      2 • s (1 : ZMod 2) = s (2 • (1 : ZMod 2)) :=
        (s.map_nsmul 2 (1 : ZMod 2)).symm
      _ = s 0 := congrArg s (by decide)
      _ = 0 := s.map_zero
  have hcast_zero : ZMod.cast (s (1 : ZMod 2)) = (0 : ZMod 2) := by
    exact (by decide : ∀ x : ZMod 4, 2 • x = 0 → ZMod.cast x = (0 : ZMod 2)) _ htwo
  have hcast_one : ZMod.cast (s (1 : ZMod 2)) = (1 : ZMod 2) := by
    simpa using hs (1 : ZMod 2)
  exact (by decide : (0 : ZMod 2) ≠ 1) (hcast_zero.symm.trans hcast_one)

#print axioms mod_four_quotient_has_no_additive_section

end D5.S3.ArithUnits.NonSplitModFour
