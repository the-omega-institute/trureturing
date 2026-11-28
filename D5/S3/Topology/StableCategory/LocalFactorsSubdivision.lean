import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.LowerCoverSubdivision
import D5.S3.Topology.StableCategory.CategoricalCoverFactorization
import D5.S3.Topology.StableCategory.UnrestrictedFactorPowers

/-! Exact local factorizations are preserved by ordinary subdivision. -/

noncomputable section

open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open D5.S3.Topology.ConnectedCategoryGraft (HasCategoricalCover)
open D5.S3.Topology.LowerCoverSubdivision (liftedRegion liftedRegion_lower persists_to_depth)
open D5.S3.Topology.OrderComplexNullhomotopy (chainMaximum chainMaximum_spec)
open D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open D5.S3.Topology.StableCategory.CategoricalCoverFactorization (hasCategoricalCover_of_factorizations)

namespace D5.S3.Topology.LocalFactorsSubdivision

open private orderComplexFace from D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
open private restrictChains from D5.S3.Topology.SubdivisionCategoricalCover
open private chainMap_comp from D5.S3.Topology.StableCategory.UnrestrictedFactorPowers

/-- A lower cover with an exact factorization of each lower-region inclusion. -/
structure LocalFactors (P : Type) [PartialOrder P] {a : ℕ}
    (Q : Fin a → Type) [∀ i, PartialOrder (Q i)] where
  region : Fin a → Set P
  lower : ∀ i, IsLowerSet (region i)
  covers : ∀ x : P, ∃ i, x ∈ region i
  insert : ∀ i, region i →o Q i
  project : ∀ i, Q i →o P
  agrees : ∀ i (x : region i), project i (insert i x) = x.val

variable {P : Type} [PartialOrder P] {a : ℕ}
variable {Q : Fin a → Type} [∀ i, PartialOrder (Q i)]

private def restrictAll (U : Set P) : liftedRegion U →o NonemptyFiniteChains U :=
  restrictChains U fun s => by
    obtain ⟨x, hx⟩ := s.val.nonempty
    exact ⟨x, hx, s.property x hx⟩

private theorem forget_restrictAll (U : Set P) (s : liftedRegion U) :
    orderHomMap (OrderEmbedding.subtype U).toOrderHom (restrictAll U s) = s.val := by
  classical
  apply NonemptyFiniteChains.ext
  ext x
  change x ∈ ((restrictAll U s).map (OrderEmbedding.subtype U).toOrderHom).finset ↔
    x ∈ s.val.finset
  rw [NonemptyFiniteChains.mem_map_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact Finset.mem_subtype.mp hu
  · intro hx
    exact ⟨⟨x, s.property x hx⟩, Finset.mem_subtype.mpr hx, rfl⟩

/-- Lift every region, insertion and projection by taking nonempty finite
chains. The equality of insertion followed by projection is preserved. -/
def LocalFactors.subdivide (F : LocalFactors P Q) :
    LocalFactors (NonemptyFiniteChains P) (fun i => NonemptyFiniteChains (Q i)) where
  region := fun i => liftedRegion (F.region i)
  lower := fun i => liftedRegion_lower (F.region i)
  covers s := by
    let t := (orderComplexFace P).symm s
    obtain ⟨i, hi⟩ := F.covers (chainMaximum t)
    exact ⟨i, fun x hx => F.lower i ((chainMaximum_spec t).2 x hx) hi⟩
  insert i := (orderHomMap (F.insert i)).comp (restrictAll (F.region i))
  project i := orderHomMap (F.project i)
  agrees i s := by
    have hfactor : (F.project i).comp (F.insert i) = (OrderEmbedding.subtype (F.region i)).toOrderHom :=
      by
        apply OrderHom.ext
        funext x
        exact F.agrees i x
    calc
      orderHomMap (F.project i) ((orderHomMap (F.insert i)).comp (restrictAll (F.region i)) s) =
          orderHomMap ((F.project i).comp (F.insert i)) (restrictAll (F.region i) s) := by
        rw [chainMap_comp]
        rfl
      _ = s.val := by rw [hfactor, forget_restrictAll]

/-- One common subdivision depth transports the entire indexed family of
exact local factorizations. -/
def LocalFactors.atDepth (F : LocalFactors P Q) (r : ℕ) :
    letI : PartialOrder (finiteSpaceSubdivision P r).1 := (finiteSpaceSubdivision P r).2
    letI : ∀ i, PartialOrder (finiteSpaceSubdivision (Q i) r).1 :=
      fun i => (finiteSpaceSubdivision (Q i) r).2
    LocalFactors (finiteSpaceSubdivision P r).1 (fun i => (finiteSpaceSubdivision (Q i) r).1) := by
  induction r with
  | zero => exact F
  | succ r ih =>
    letI : PartialOrder (finiteSpaceSubdivision P r).1 := (finiteSpaceSubdivision P r).2
    letI : ∀ i, PartialOrder (finiteSpaceSubdivision (Q i) r).1 :=
      fun i => (finiteSpaceSubdivision (Q i) r).2
    exact ih.subdivide

/-- A finite family of factors whose lower covers occur at different depths
still yields the product bound at one ordinary depth in the ambient poset. -/
theorem LocalFactors.cover_at_some_depth {b : ℕ} (F : LocalFactors P Q)
    (finite : ∀ i, Finite (Q i))
    (hcovers : ∀ i, ∃ r : ℕ,
      letI : PartialOrder (finiteSpaceSubdivision (Q i) r).1 := (finiteSpaceSubdivision (Q i) r).2
      HasCategoricalCover (finiteSpaceSubdivision (Q i) r).1 b) :
    ∃ r : ℕ, letI : PartialOrder (finiteSpaceSubdivision P r).1 := (finiteSpaceSubdivision P r).2
      HasCategoricalCover (finiteSpaceSubdivision P r).1 (a * b) := by
  classical
  choose depth hd using hcovers
  let r := Finset.univ.sup depth
  letI : PartialOrder (finiteSpaceSubdivision P r).1 := (finiteSpaceSubdivision P r).2
  letI : ∀ i, PartialOrder (finiteSpaceSubdivision (Q i) r).1 :=
    fun i => (finiteSpaceSubdivision (Q i) r).2
  let G := F.atDepth r
  refine ⟨r, hasCategoricalCover_of_factorizations G.region G.lower G.covers G.insert G.project G.agrees ?_⟩
  intro i
  haveI : Finite (Q i) := finite i
  exact persists_to_depth (Finset.le_sup (f := depth) (Finset.mem_univ i)) (hd i)

end D5.S3.Topology.LocalFactorsSubdivision
