/- GID: D5/S3/Combinatorics/Turnpike/ContainmentRankBounds
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Turnpike/ContainmentRankBounds
   mirror-E: none(waiver:general-containment-proof)
   anchors: []
   utility: none
   digest: Used distance rank blocks obey containment bounds. -/
module
public import D5.S3.Combinatorics.Turnpike.ContainmentRankBoundsProofs

/-! Known containment rank bounds with unused-label histogram support. -/
@[expose] public section
namespace D5.S3.Combinatorics.Turnpike.ContainmentRankBounds
open Omega.Turnpike
open scoped BigOperators

/-- Known containment rank theorem, including the original intersection-mask soundness. -/
theorem containment_rank_bounds {n d : ℕ} {y : Fin d → ℝ} {mu : Fin d → ℕ}
    {x : Fin n → ℝ} (hy : StrictAnti y) (hx : Realizes y mu x)
    (e : Interval n) (q : Fin d) (heq : x e.1.2 - x e.1.1 = y q) :
    (e.1.1.val + 1) * (n - e.1.2.val) ≤
        (∑ r ∈ Finset.univ.filter (· < q), mu r) + 1 ∧
    (∑ r ∈ Finset.univ.filter (· ≤ q), mu r) ≤
        n.choose 2 - (e.1.2.val - e.1.1.val + 1).choose 2 + 1 ∧
    RankAllowed mu e q :=
  Omega.Turnpike.containment_rank_bounds hy hx e q heq

end D5.S3.Combinatorics.Turnpike.ContainmentRankBounds
