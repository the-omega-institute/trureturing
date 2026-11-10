/- GID: D5/S3/Geometry/OriginalLabelTwoSum/Certificates
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/Certificates
   mirror-E: none(waiver:original-label-two-sum-certificates)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Collapse-only main certificates and separate collar/core sequences retain literal critical boundaries. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Native

/-! UNCOMPILED. These are the ORIGINAL certificate hypotheses. In particular the
core collapse is on the core ALONE. No sphere equivalence is a field. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite union of raw simplices, with the empty index family equal to VOID. -/
def facets (F : Finset (Finset V)) : Family V where
  carrier := {s | ∃ a ∈ F, s ⊆ a}
  lower' := by
    rintro s t h ⟨a,ha,hs⟩
    exact ⟨a,ha,h.trans hs⟩

def endpoint (B : Family V) (critical : Finset (Finset V)) : Family V :=
  B ⊔ facets critical

/-- Exact ordinary critical-cell conditions, including ALL proper subfaces. -/
structure CriticalData (B : Family V) (critical : Finset (Finset V)) : Prop where
  nonempty : ∀ s ∈ critical, s.Nonempty
  absent : ∀ s ∈ critical, s ∉ B
  boundary : ∀ s ∈ critical, ∀ t, t ⊂ s → t ∈ B
  antichain : ∀ s ∈ critical, ∀ t ∈ critical, s ⊆ t → s = t

/-- A local filling need not have a contractible collar. -/
structure Filling (W : Finset V) (A : Family V) where
  empty_mem : (∅ : Finset V) ∈ A
  collar : Family V
  critical : Finset (Finset V)
  contains : A ≤ collar
  supported : Supported W collar
  critical_supported : ∀ s ∈ critical, s ⊆ W
  cells : CriticalData collar critical
  main : Sequence (project (delta W)) (project (endpoint collar critical))
  separate : Sequence (project collar) (project A)

/-- A left input carries an actual vertex and ordinary main/core lists. -/
structure Certificate (W : Finset V) (K : Family V) where
  supported : Supported W K
  core : Family V
  critical : Finset (Finset V)
  vertex : V
  vertex_mem : ({vertex} : Finset V) ∈ core
  core_supported : Supported W core
  critical_supported : ∀ s ∈ critical, s ⊆ W
  cells : CriticalData core critical
  main : Sequence (project K) (project (endpoint core critical))
  separate : Sequence (project core) (project (delta {vertex}))

/-- Actual literal simplex/core intersection, with the empty face retained. -/
theorem critical_intersection (B : Family V) (C : Finset (Finset V))
    (h : CriticalData B C) {s : Finset V} (hs : s ∈ C) :
    delta s ⊓ B =
      (⟨{t | t ⊂ s}, fun a b hba has => lt_of_le_of_lt hba has⟩ : Family V) := by
  apply SetLike.ext
  intro t
  change t ⊆ s ∧ t ∈ B ↔ t ⊂ s
  constructor
  · rintro ⟨ht,hB⟩
    refine Finset.ssubset_iff_subset_ne.mpr ⟨ht,?_⟩
    intro he
    exact h.absent s hs (he ▸ hB)
  · intro ht
    exact ⟨ht.1,h.boundary s hs t ht⟩

/-- Distinct retained cells meet only in proper boundary faces. -/
theorem critical_overlap (B : Family V) (C : Finset (Finset V))
    (h : CriticalData B C) {s t u : Finset V} (hs : s ∈ C) (ht : t ∈ C)
    (hne : s ≠ t) (hus : u ⊆ s) (hut : u ⊆ t) : u ∈ B := by
  apply h.boundary s hs u
  refine Finset.ssubset_iff_subset_ne.mpr ⟨hus,?_⟩
  intro he
  subst u
  exact hne (h.antichain s hs t ht hut)

end D5.S3.Geometry.OriginalLabelTwoSum
