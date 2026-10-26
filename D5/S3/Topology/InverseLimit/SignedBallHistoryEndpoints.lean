/- GID: D5/S3/Topology/InverseLimit/SignedBallHistoryEndpoints
   generality: G
   mirror-B: none(waiver:private-internal-step)
   mirror-E: none(waiver:private-internal-step)
   anchors: []
   utility: none
   digest: Infinite high and zero evaluations along one literal successor sequence. -/

import D5.S3.Topology.InverseLimit.SignedOrdinalSuccessor

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Function MeasureTheory
open scoped Ordinal

namespace D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints

open SignedOrdinalSuccessor

/-- The even and odd columns of one literal successor give infinitely many
high and zero evaluations of every whole sequence of original norm-one lifts. -/
private theorem quantitative_g_infinite
    {a : Ordinal.{0}} {H : SignedProperLimit.Prefix (Order.succ a)}
    {ha : ω ≤ a} {P : Predecessor H ha} {launch : Launch a}
    {Q : Prepared H ha P launch} {t : Treatment a}
    (R : Result H ha P launch Q t)
    (s : ℕ → SignedMeasure R.coordinates.carrier)
    (hmap : ∀ n, (s n).map (R.literalProjection t.row) = Q.measure t.row t.label n)
    (hmass : ∀ n, (s n).totalVariation univ = 1) :
    {n | (1 : ℝ) / 6 ≤ s n R.quantitativeClopen}.Infinite ∧
      {n | s n R.quantitativeClopen = 0}.Infinite := by
  have heven : Injective (fun m : ℕ => (R.column (2 * m)).n) :=
    R.k_mono.injective.comp (fun i j hij => by omega)
  have hodd : Injective (fun m : ℕ => (R.column (2 * m + 1)).n) :=
    R.k_mono.injective.comp (fun i j hij => by omega)
  constructor
  · apply (Set.infinite_range_of_injective heven).mono
    rintro _ ⟨m, rfl⟩
    exact ((R.quantitative_g (2 * m) (s _) (hmap _) (hmass _)).1 (by omega)).le
  · apply (Set.infinite_range_of_injective hodd).mono
    rintro _ ⟨m, rfl⟩
    exact (R.quantitative_g (2 * m + 1) (s _) (hmap _) (hmass _)).2 (by omega)

end D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints
