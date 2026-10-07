/- GID: D5/S3/Factorization/Galois/ConditionalNikolovSegal
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ConditionalNikolovSegal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Strong completeness reduced to finite power width and exponent order bounds. -/
import D5.S3.Factorization.Galois.ProfiniteQuotientBound

set_option autoImplicit false

/-!
Strong completeness reduced to two uniform finite-group propositions.
Nikolov–Segal (2007) gives the unconditional mathematical theorem; their power-width
result (2011) and Zelmanov's restricted Burnside theorem are not proved here.
The compactness, continuous finite-quotient transfer, and normal-core arguments
are proved in this library. No continuity of an abstract finite-index quotient is used.
-/
open D5.S3.Factorization.Galois.NormalCorePower
  D5.S3.Factorization.Galois.ProfinitePowerTransfer
  D5.S3.Factorization.Galois.ProfiniteQuotientBound

namespace D5.S3.Factorization.Galois.ConditionalNikolovSegal

universe u

/-- The full official conclusion, under the two explicit finite-group inputs.
All compactness, finite-quotient transfers, and normal-core containments are proved
in the imported local modules. `G` is an arbitrary group, and `H` need not be normal. -/
theorem conditional_nikolov_segal
    (finiteWidth : ∀ d m : ℕ, 0 < m → ∃ w, FinitePowerWidth.{u} d m w)
    (finiteBound : ∀ d m : ℕ, 0 < m → ∃ B, FiniteExponentBound.{u} d m B)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : ∃ S : Finset G, (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (H : Subgroup G) [H.FiniteIndex] : IsOpen (H : Set G) := by
  obtain ⟨S, hS⟩ := hG
  have hm : 0 < H.normalCore.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨w, hw⟩ := finiteWidth S.card H.normalCore.index hm
  obtain ⟨B, hB⟩ := finiteBound S.card H.normalCore.index hm
  exact finiteIndex_isOpen_of_finite_inputs S hS H w B hw hB

end D5.S3.Factorization.Galois.ConditionalNikolovSegal
