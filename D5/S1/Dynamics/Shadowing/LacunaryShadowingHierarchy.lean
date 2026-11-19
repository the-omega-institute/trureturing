/- GID: D5/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy
   generality: I
   mirror-B: D5/B/S1/Dynamics/Shadowing/LacunaryShadowingHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every positive finite strict neighborhood-shadowing level occurs in a binary subshift. -/

import D5.S1.Dynamics.Shadowing.LacunaryShadowingUpper
import D5.S1.Dynamics.Shadowing.LacunaryShadowingLower

open Function SymbolicDynamics.FullShift

namespace D5.S1.Dynamics.Shadowing

/-- The shift on the two-sided progression subshift is invertible. -/
theorem lacunary_shift_bijective (m : ℕ) : Bijective (lacunaryShift m) := by
  constructor
  · intro x y h
    apply Subtype.ext
    funext n
    have hn := congrArg (fun z : LacunaryPoint m => z.1 (n - 1)) h
    simpa [lacunaryShift, shift_apply] using hn
  · intro x
    refine ⟨⟨shift (-1) x.1, lacunary_legal_shift x.2 (-1)⟩, ?_⟩
    apply Subtype.ext
    funext n
    simp [lacunaryShift, shift_apply]

/-- Meddaugh--Stephens Questions 5.1 and 5.2, at every positive finite level:
the explicit binary two-sided subshift has a continuous invertible shift and
neighborhood N+1-shadowing, while neighborhood N-shadowing fails. -/
theorem lacunary_shadowing_hierarchy (N : ℕ) (hN : 1 ≤ N) :
    Nonempty (LacunaryPoint (N + 2)) ∧
      CompactSpace (LacunaryPoint (N + 2)) ∧
      Continuous (lacunaryShift (N + 2)) ∧
      Bijective (lacunaryShift (N + 2)) ∧
      NeighborhoodFiniteShadowing (N + 1) (lacunaryShift (N + 2)) ∧
      ¬ NeighborhoodFiniteShadowing N (lacunaryShift (N + 2)) := by
  have hm : 3 ≤ N + 2 := by omega
  refine ⟨inferInstance, inferInstance, lacunary_shift_continuous _,
    lacunary_shift_bijective _, ?_, ?_⟩
  · simpa using lacunary_neighborhood_upper (N + 2) hm
  · simpa using lacunary_not_neighborhood_smaller (N + 2) hm

end D5.S1.Dynamics.Shadowing
