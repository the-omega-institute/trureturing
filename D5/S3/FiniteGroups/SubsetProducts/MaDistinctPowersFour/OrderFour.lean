/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A transversal, equal columns or a prescribed motif at order four. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part17

namespace MaLatin

universe u

/-- The order-four classification for a row- and column-injective array of arbitrary labels. -/
theorem orderFour {α : Type u} (A : Fin 4 → Fin 4 → α) (h : Latin A) :
    Rainbow A ∨ EqualColumns A ∨ Motif A := by
  classical
  by_cases hR : Rainbow A
  · exact Or.inl hR
  · exact Or.inr (OrderFourChecker.initial_closed A h hR (OrderFourChecker.realizes_initial A))

end MaLatin
