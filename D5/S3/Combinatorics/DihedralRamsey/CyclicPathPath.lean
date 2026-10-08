/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicPathPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicPathPath
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact cyclic Ramsey number of two alternating paths. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyPathPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicPathPath

open DihedralRamseyDefs CyclicRamseyDefs
open Finset

/-- Bašić–Damnjanović–Stevanović–Stošić Conjecture 4.8. -/
theorem result : CyclicRamseyDefs.claimCycPathPath := by
  intro a b ha hb
  apply path_pair_cyclic ha hb (altPath b)
  · intro n G h _
    exact extremal hb G h
  · rintro n G ⟨s, ψ, hψ, hadj⟩
    exact ⟨s, false, ψ, hψ, hadj⟩

end D5.S3.Combinatorics.DihedralRamsey.CyclicPathPath
