/- GID: D5/S3/Combinatorics/DihedralRamsey/CyclicStarPath
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/CyclicStarPath
   mirror-E: none(waiver:cyclic-star-path-ramsey)
   anchors: []
   utility: none
   digest: The exact cyclic Ramsey number of a star versus an alternating path. -/

import D5.S3.Combinatorics.DihedralRamsey.PathStar
import D5.S3.Combinatorics.DihedralRamsey.CyclicCliquePath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey.CyclicStarPath

open DihedralRamseyDefs CyclicRamseyDefs

/-- Conjecture 4.17, with the star in the first colour. -/
theorem result : CyclicRamseyDefs.claimCycStarPath := by
  intro a b ha hb
  rw [CyclicCliquePath.cyclicRamsey_comm]
  obtain ⟨upper, smaller⟩ := PathStar.bounds b a (by omega) (by omega)
  let N := b + a - 2 - b * a % 2
  have he : N = a + b - 2 - a * b % 2 := by simp [N, Nat.add_comm, Nat.mul_comm]
  rw [← he]
  let S : Set ℕ := {l | ∀ G : SimpleGraph (Fin l),
    CyclicEmbeddable (altPath b) G ∨ CyclicEmbeddable (startStar a) Gᶜ}
  change sInf S = N
  apply le_antisymm
  · exact Nat.sInf_le (show N ∈ S from upper)
  · have hm := Nat.sInf_mem (show S.Nonempty from ⟨N, upper⟩)
    by_contra hlt
    apply smaller (sInf S)
    · change sInf S < N
      omega
    · intro G
      rcases hm G with ⟨s, ψ, hψ, hE⟩ | ⟨s, ψ, hψ, hE⟩
      · exact Or.inl ⟨s, false, ψ, hψ, hE⟩
      · exact Or.inr ⟨s, false, ψ, hψ, hE⟩

end D5.S3.Combinatorics.DihedralRamsey.CyclicStarPath
