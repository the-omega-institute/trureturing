/- GID: D5/S3/Combinatorics/IntervalReconstruction/BottleneckCancellation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/IntervalReconstruction/BottleneckCancellation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [lake/module/OmegaMath.Combinatorics.BottleneckCancellation]
   utility: none
   digest: Prescribed finite occurrence deletion preserves a quantitative pseudometric matching. -/

import D5.S3.Combinatorics.IntervalReconstruction.Occurrences.BottleneckCancellation

/-! Book citation for quantitative cancellation of prescribed occurrence pairs. -/

namespace D5.S3.Combinatorics.IntervalReconstruction.BottleneckCancellation

/-- Both error bounds refer to the same labels and the same actual occurrence indices. -/
theorem result {X : Type*} {Y : Type*} {M : Type*} [PseudoMetricSpace M]
    (a : X → M) (b : Y → M) (e : X ≃ Y) (U : Finset X) (V : Finset Y)
    (d : U ≃ V) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (he : ∀ x, dist (a x) (b (e x)) ≤ ε)
    (hd : ∀ u : U, dist (a u) (b (d u)) ≤ η) :
    ∃ f : {x // x ∉ U} ≃ {y // y ∉ V},
      ∀ x : {x // x ∉ U}, dist (a x) (b (f x)) ≤
        (U.card + 1 : ℝ) * ε + U.card * η :=
  Omega.BottleneckCancellation.complement_bound a b e U V d ε η hε hη he hd

end D5.S3.Combinatorics.IntervalReconstruction.BottleneckCancellation
