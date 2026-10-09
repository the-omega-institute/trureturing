/- GID: D5/S3/Combinatorics/Permutation/KaselDisplacementLadder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/KaselDisplacementLadder
   mirror-E: none(waiver:open-problem-resolution)
   anchors: []
   utility: none
   digest: Kasel displacement ladder has the conjectured value m minus two
     at every horizon four to the m. -/

import D5.S3.Combinatorics.Permutation.KaselDisplacementLadderLower
import D5.S3.Combinatorics.Permutation.KaselDisplacementLadderUpper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.KaselDisplacementLadder

open D5.S3.Combinatorics.Permutation.KaselDisplacementLadderDefs

/-- Kasel's conjecture L(m) = m − 2: an attaining normalized valid scheme exists, and every
normalized valid scheme has a distinguished value with displacement at least m − 2. -/
def claim : Prop := ∀ m : ℕ, 2 ≤ m →
  (∃ s r : ℕ → ℕ, Valid (SA m) s r ∧ Normalized (SA m) s ∧
      ∀ v ∈ distinguished, s v ≤ block v / 2 + (m - 2)) ∧
  (∀ s r : ℕ → ℕ, Valid (SA m) s r → Normalized (SA m) s →
      ∃ v ∈ distinguished, block v / 2 + (m - 2) ≤ s v)

theorem result : claim := fun m hm =>
  ⟨D5.S3.Combinatorics.Permutation.KaselDisplacementLadderUpper.upper_bound m hm,
   D5.S3.Combinatorics.Permutation.KaselDisplacementLadderLower.lower_bound m hm⟩

end D5.S3.Combinatorics.Permutation.KaselDisplacementLadder
