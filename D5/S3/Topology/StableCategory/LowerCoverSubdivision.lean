/- GID: D5/S3/Topology/StableCategory/LowerCoverSubdivision
   generality: G
   mirror-B: none(waiver:consumed-by-weak-category-one-reduction)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Categorical lower covers persist at every later ordinary subdivision depth. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.OrderComplexNullhomotopy
import D5.S3.Topology.StableCategory.ProductStableLower

noncomputable section

open PartialOrder (NonemptyFiniteChains)
open D5.S3.Topology.ConnectedCategoryGraft (Categorical HasCategoricalCover)
open D5.S3.Topology.OrderComplexNullhomotopy (chainMaximum chainMaximum_spec)
open D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer (finiteSpaceSubdivision)

namespace D5.S3.Topology.LowerCoverSubdivision

open private orderComplexFace from D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
open private categorical_of_meeting from D5.S3.Topology.SubdivisionCategoricalCover

variable {P : Type} [PartialOrder P]

/-- A lower region lifts to the chains whose members all belong to it. -/
def liftedRegion (U : Set P) : Set (NonemptyFiniteChains P) :=
  {s | ∀ x ∈ s.finset, x ∈ U}

theorem liftedRegion_lower (U : Set P) : IsLowerSet (liftedRegion U) :=
  fun _ _ h hs x hx => hs x (h hx)

/-- A categorical lower cover persists under an ordinary subdivision with
exactly the same index set. The greatest member of each chain supplies a
covering region for the whole chain. -/
theorem subdivision_preserves_cover [Finite P] {k : ℕ} (h : HasCategoricalCover P k) :
    HasCategoricalCover (NonemptyFiniteChains P) k := by
  obtain ⟨U, hU, cover⟩ := h
  refine ⟨fun i => liftedRegion (U i), fun i => ⟨liftedRegion_lower _, ?_⟩, ?_⟩
  · exact categorical_of_meeting (hU i).2 fun s => by
      obtain ⟨a, ha⟩ := s.val.nonempty
      exact ⟨a, ha, s.property a ha⟩
  · intro s
    let t := (orderComplexFace P).symm s
    obtain ⟨i, hi⟩ := cover (chainMaximum t)
    exact ⟨i, fun x hx => (hU i).1 ((chainMaximum_spec t).2 x hx) hi⟩

open private depth_finite from D5.S3.Topology.StableCategory.ProductStableLower

/-- Categorical lower covers may be synchronized at any common larger
ordinary depth, without changing their piece count. -/
theorem persists_to_depth [Finite P] {k r s : ℕ} (hrs : r ≤ s)
    (h : letI : PartialOrder (finiteSpaceSubdivision P r).1 := (finiteSpaceSubdivision P r).2
      HasCategoricalCover (finiteSpaceSubdivision P r).1 k) :
    letI : PartialOrder (finiteSpaceSubdivision P s).1 := (finiteSpaceSubdivision P s).2
    HasCategoricalCover (finiteSpaceSubdivision P s).1 k := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ n h rn =>
    letI : PartialOrder (finiteSpaceSubdivision P n).1 := (finiteSpaceSubdivision P n).2
    letI : Finite (finiteSpaceSubdivision P n).1 := depth_finite P n
    exact subdivision_preserves_cover rn

end D5.S3.Topology.LowerCoverSubdivision
