/- GID: D5/S3/Combinatorics/Graph/StarForming/ClosedHighCycle
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/ClosedHighCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: Original zero-hub and closed high-cycle two-hub score proofs. -/

import D5.S3.Combinatorics.Graph.StarForming.LongCoreUpper

/-! Local proof bodies from formal/StarForming/ClosedHighCycle.lean,
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The hypotheses must be extracted from the actual graph;
no numerical parameter wrapper replaces that extraction. -/


namespace D5.S3.Combinatorics.Graph.StarForming.ClosedHighCycle

open D5.S3.Combinatorics.Graph.StarForming.LongCoreUpper

theorem zero_hub_score (first middle last : Cell)
    (hfirst : Valid first 0 0) (hmiddle : Valid middle 0 0)
    (hlast : Valid last 0 0) :
    3 + first.weight + middle.weight + last.weight ≤ 12 := by
  have hcapFirst := cell_cap first 0 0 hfirst
  have hcapMiddle := cell_cap middle 0 0 hmiddle
  have hcapLast := cell_cap last 0 0 hlast
  omega

theorem closed_two_hub_score (first middle last : Cell)
    (hfirst : Valid first 1 1) (hmiddle : Valid middle 1 1)
    (hlast : Valid last 1 1) (hfirstAcross : Across first middle)
    (hlastAcross : Across middle last)
    (hclosedHigh : last.highRight + first.highLeft + first.highRight ≤ 2) :
    3 + first.weight + middle.weight + last.weight + 2 ≤ 12 := by
  obtain ⟨hupper, hequality⟩ :=
    two_hub_block first middle last hfirst hmiddle hlast hfirstAcross hlastAcross
  by_cases hequal : 3 + first.weight + middle.weight + last.weight + 2 = 13
  · obtain ⟨htightFirst, _, htightLast⟩ := hequality hequal
    have hshapeFirst := two_hub_tight first hfirst htightFirst
    have hshapeLast := two_hub_tight last hlast htightLast
    omega
  · omega

end D5.S3.Combinatorics.Graph.StarForming.ClosedHighCycle
