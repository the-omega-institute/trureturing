/- GID: D5/S3/ConceptDynamics/InformationEscapeCounting/Fused
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscapeCounting/Fused
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: One strict catalog-wide fold counts every information-escape field. -/
import D5.S3.ConceptDynamics.InformationEscape.RoleHistogram

/- Library-search audit trail (2026-09-05):
   * Repository search found the frozen agreement and exact-count APIs reused here.
   * Pinned Mathlib supplies `List.finRange`, `Function.update`, and bit operations.
   * No catalog-wide saturated disagreement scan was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq
attribute [local instance] Catalog.indexFintype Catalog.indexDecidableEq

namespace Arena

/-- An ordered, duplicate-free list containing every state of an arena. -/
structure StateEnumeration (arena : Arena.{u}) where
  states : List arena.State
  nodup : states.Nodup
  complete : states.toFinset = Finset.univ

end Arena

namespace Catalog

/-- An ordered, duplicate-free list containing every index of a catalog. -/
structure IndexEnumeration (Index : Type w) [DecidableEq Index] where
  indices : List Index
  nodup : indices.Nodup
  complete : forall index, index ∈ indices

/-- The canonical ascending enumeration of `Fin n`. -/
def finIndexEnumeration (n : Nat) : IndexEnumeration (Fin n) where
  indices := List.finRange n
  nodup := List.nodup_finRange n
  complete := by intro index; simp

/-- Catalog-wide counts produced by one scan of each ordered state pair. -/
structure FusedCounts (Index : Type w) where
  full : Nat
  unique : Index -> Nat
  roleBins : Index -> Fin 15 -> Nat

/-- The leave-one-out count derived without a second scan. -/
def FusedCounts.without {Index : Type w}
    (counts : FusedCounts Index) (index : Index) : Nat :=
  counts.full + counts.unique index

def FusedCounts.zero {Index : Type w} : FusedCounts Index where
  full := 0
  unique := fun _ => 0
  roleBins := fun _ _ => 0

def maskSignature (mask : Fin 16) : Fin 4 -> Bool := fun coordinate =>
  match coordinate.1 with
  | 0 => mask.1.testBit 3
  | 1 => mask.1.testBit 2
  | 2 => mask.1.testBit 1
  | _ => mask.1.testBit 0

def bucketMask (bucket : Fin 15) : Fin 16 :=
  ⟨bucket.1 + 1, by omega⟩

/-- Convert a mask to its zero-based bucket; zero is unreachable for a disagreement. -/
def bucketOfMask (mask : Fin 16) : Fin 15 :=
  ⟨if mask.1 = 0 then 0 else mask.1 - 1, by
    by_cases zero : mask.1 = 0
    · simp [zero]
    · simp [zero]
      omega⟩

/-- The nonzero high-first role signature belonging to one reflected bucket. -/
def roleSignatureOfBucket (bucket : Fin 15) : Fin 4 -> Bool :=
  maskSignature (bucketMask bucket)

def selectedMask {arena : Arena.{u}}
    (bundle : PrimitiveBundle arena.State) (left right : arena.State) : Fin 16 :=
  let cut := bundle.separatesOnAxis .cut left right
  let flow := bundle.separatesOnAxis .flow left right
  let admit := bundle.separatesOnAxis .admit left right
  let anchor := bundle.separatesOnAxis .anchor left right
  ⟨(if cut then 8 else 0) + (if flow then 4 else 0) +
      (if admit then 2 else 0) + (if anchor then 1 else 0), by
    cases cut <;> cases flow <;> cases admit <;> cases anchor <;> decide⟩

/-- Saturated result of scanning one theorem family for one state pair. -/
inductive PairScan (Index : Type w) where
  | none
  | one (index : Index) (mask : Fin 16)
  | many
  deriving DecidableEq

def scanAfterOne {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : arena.State)
    (first : catalog.Index) (mask : Fin 16) : List catalog.Index -> PairScan catalog.Index
  | [] => .one first mask
  | candidate :: rest =>
      if (catalog.theoremAt candidate).primitives.agreesB left right then
        scanAfterOne catalog left right first mask rest
      else
        .many

def scanIndices {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (left right : arena.State) :
    List catalog.Index -> PairScan catalog.Index
  | [] => .none
  | candidate :: rest =>
      if (catalog.theoremAt candidate).primitives.agreesB left right then
        scanIndices catalog left right rest
      else
        scanAfterOne catalog left right candidate
          (selectedMask (catalog.theoremAt candidate).primitives left right) rest

/-- Scan the catalog indices once, ceasing agreement evaluation at disagreement two. -/
def pairScan {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (indices : IndexEnumeration catalog.Index) (left right : arena.State) :
    PairScan catalog.Index :=
  scanIndices catalog left right indices.indices

def FusedCounts.bump {Index : Type w}
    (counts : FusedCounts Index) [DecidableEq Index]
    (index : Index) (bucket : Fin 15) : FusedCounts Index where
  full := counts.full
  unique := Function.update counts.unique index (counts.unique index + 1)
  roleBins := Function.update counts.roleBins index
    (Function.update (counts.roleBins index) bucket
      (counts.roleBins index bucket + 1))

def pairStep {arena : Arena.{u}}
    (catalog : Catalog.{u, v, w} arena) (indices : IndexEnumeration catalog.Index)
    (counts : FusedCounts catalog.Index) (left right : arena.State) :
    FusedCounts catalog.Index :=
  if left == right then
    counts
  else
    match catalog.pairScan indices left right with
    | .none => { counts with full := counts.full + 1 }
    | .many => counts
    | .one index mask => counts.bump index (bucketOfMask mask)

/-- Compute all catalog counts in one strict nested fold over ordered states. -/
def fusedCounts {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (states : Arena.StateEnumeration arena)
    (indices : IndexEnumeration catalog.Index) : FusedCounts catalog.Index :=
  states.states.foldl (fun counts left =>
    states.states.foldl (fun counts right =>
      pairStep catalog indices counts left right) counts) FusedCounts.zero

end Catalog
end D5.S3.ConceptDynamics.InformationEscape
