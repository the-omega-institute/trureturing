/- GID: D5/S3/Combinatorics/CayleyHosts/DoubleStarHost
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CayleyHosts/DoubleStarHost
   mirror-E: none(waiver:abelian-cayley-host-minimum)
   anchors: []
   utility: none
   digest: The least finite abelian Cayley host order of the double star is five times q. -/

import D5.S3.Combinatorics.CayleyHosts.DoubleStarHostUpper
import D5.S3.Combinatorics.CayleyHosts.DoubleStarHostLower

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CayleyHosts.DoubleStarHost

open DoubleStarHostDefs

/-- Conjecture 27 of Fokam Souop and Bitjoka. -/
theorem result : DoubleStarHostDefs.claim := by
  classical
  intro q hq
  letI : NeZero (5 * q) := ⟨by omega⟩
  let orders : Set ℕ := {N | ∃ (Γ : Type) (_ : AddCommGroup Γ) (_ : Fintype Γ),
      Fintype.card Γ = N ∧ ∃ (s : Set Γ) (f : Bool × Option (Fin q) → Γ),
        IsInducedEmbedding (doubleStar q) s f}
  change sInf orders = 5 * q
  have hattained : 5 * q ∈ orders := by
    obtain ⟨s, f, hf⟩ := DoubleStarHostUpper.upper_attained q (by omega)
    exact ⟨ZMod (5 * q), inferInstance, inferInstance, ZMod.card (5 * q), s, f, hf⟩
  apply Nat.le_antisymm (Nat.sInf_le hattained)
  obtain ⟨Γ, instAdd, instFinite, hcard, s, f, hf⟩ :=
    Nat.sInf_mem (s := orders) ⟨5 * q, hattained⟩
  letI := instAdd
  letI := instFinite
  rw [← hcard]
  exact DoubleStarHostLower.lower_bound q (by omega) s f hf

end D5.S3.Combinatorics.CayleyHosts.DoubleStarHost
