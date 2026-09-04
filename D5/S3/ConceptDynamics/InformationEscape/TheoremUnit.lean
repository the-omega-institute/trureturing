/- GID: D5/S3/ConceptDynamics/InformationEscape/TheoremUnit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/TheoremUnit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed primitive realizations bind theorem laws to finite executable catalogs. -/

import D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle
import D5.S3.ConceptDynamics.InformationEscape.Arena
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

/- Library-search audit trail (2026-09-04):
   * Repository searches for `PrimitiveSignature`, `PrimitiveRealization`,
     `TheoremUnit`, and `Catalog` found no existing declarations under `D5`.
   * Exact current-tree hits `CIRPT.PrimitiveBundle`, `PrimitiveAtom`,
     `cutKernel`, and `anchorKernel` are reused rather than repackaged.
   * Pinned Mathlib supplies the `Fintype` and `DecidableEq` instances for
     sums and `Fin`, `Finset.mem_erase`, `Finset.card_erase_of_mem`, and the
     standard `decide` reflection simplifier used below.
   * No existing typed dependent-output realization layer or theorem-bound
     catalog constructor was found in the repository or pinned Mathlib. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

open D5.S3.ConceptDynamics.CIRPT

universe u v w

/-- A typed inventory of readout roles and separately represented point anchors.

This is the finite engine's typed-signature deviation from the legacy field shape in
specification section 19.6. The seal observes only the resulting primitive kernels. -/
structure PrimitiveSignature (X : Type u) where
  Index : Type v
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  Output : Index -> Type w
  outputDecidableEq : forall i, DecidableEq (Output i)
  axis : Index -> PrimitiveAxis
  AnchorIndex : Type v
  anchorFintype : Fintype AnchorIndex
  anchorDecidableEq : DecidableEq AnchorIndex

/-- Concrete readouts and anchor points realizing a typed primitive signature. -/
structure PrimitiveRealization {X : Type u} (sig : PrimitiveSignature.{u, v, w} X) where
  readout : forall i, X -> sig.Output i
  anchor : sig.AnchorIndex -> X

namespace PrimitiveRealization

/-- Compile typed readouts and point anchors into the canonical CIRPT bundle. -/
def toPrimitiveBundle {X : Type u} {sig : PrimitiveSignature.{u, v, w} X}
    [DecidableEq X] (realization : PrimitiveRealization sig) : PrimitiveBundle X := by
  letI := sig.indexFintype
  letI := sig.indexDecidableEq
  letI := sig.anchorFintype
  letI := sig.anchorDecidableEq
  refine
    { Index := sig.Index ⊕ sig.AnchorIndex
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      atom := ?_ }
  intro index
  cases index with
  | inl i =>
      letI := sig.outputDecidableEq i
      exact ⟨sig.axis i, cutKernel (realization.readout i)⟩
  | inr j =>
      exact ⟨.anchor, anchorKernel (realization.anchor j)⟩

/-- Compiled bundle agreement is exactly equality of every readout together with
agreement on membership in every point anchor. -/
theorem toPrimitiveBundle_agrees_iff
    {X : Type u} {sig : PrimitiveSignature.{u, v, w} X} [DecidableEq X]
    (realization : PrimitiveRealization sig) (x y : X) :
    realization.toPrimitiveBundle.agrees x y <->
      (forall i, realization.readout i x = realization.readout i y) /\
        (forall j, (x = realization.anchor j <-> y = realization.anchor j)) := by
  constructor
  · intro agreement
    constructor
    · intro i
      have readoutAgreement := agreement (Sum.inl i)
      simpa [PrimitiveBundle.agrees, toPrimitiveBundle] using readoutAgreement
    · intro j
      have anchorAgreement := agreement (Sum.inr j)
      simpa [PrimitiveBundle.agrees, toPrimitiveBundle] using anchorAgreement
  · rintro ⟨readoutAgreement, anchorAgreement⟩ index
    cases index with
    | inl i =>
        simpa [PrimitiveBundle.agrees, toPrimitiveBundle] using readoutAgreement i
    | inr j =>
        simpa [PrimitiveBundle.agrees, toPrimitiveBundle] using anchorAgreement j

end PrimitiveRealization

/-- A Boolean ADMIT readout is true exactly on admitted states. -/
theorem admit_readout_eq_true_iff {X : Type u} (A : X -> Prop) [DecidablePred A] (a : X) :
    (fun x => decide (A x)) a = true <-> A a := by
  simp

/-- A proved statement equipped with the primitive bundle carrying its object content. -/
structure TheoremUnit (arena : Arena.{u}) where
  primitives : PrimitiveBundle.{u, v} arena.State
  Statement : Prop
  proof : Statement

/-- An arena whose laws range over typed realizations of one primitive signature. -/
structure PrimitiveLawArena extends Arena.{u} where
  signature : PrimitiveSignature.{u, v, w} toArena.State
  Law : PrimitiveRealization signature -> Prop

/-- A theorem stated natively as a law of its primitive realization. -/
structure NativeTheoremUnit (arena : PrimitiveLawArena.{u, v, w}) where
  realization : PrimitiveRealization arena.signature
  proof : arena.Law realization

/-- A legacy statement connected mathematically to the law of a concrete realization. -/
structure LegacyPrimitiveRealization (arena : PrimitiveLawArena.{u, v, w})
    (statement : Prop) (realization : PrimitiveRealization arena.signature) where
  equivalence : statement <-> arena.Law realization

namespace NativeTheoremUnit

/-- Forget the typed presentation while retaining its compiled primitive bundle and law. -/
def toTheoremUnit {arena : PrimitiveLawArena.{u, v, w}}
    (unit : NativeTheoremUnit arena) : TheoremUnit.{u, v} arena.toArena := by
  letI := arena.toArena.stateDecidableEq
  exact
    { primitives := unit.realization.toPrimitiveBundle
      Statement := arena.Law unit.realization
      proof := unit.proof }

end NativeTheoremUnit

namespace LegacyPrimitiveRealization

/-- Package a proved legacy statement with the bundle from its law-equivalent realization. -/
def toTheoremUnit {arena : PrimitiveLawArena.{u, v, w}} {statement : Prop}
    {realization : PrimitiveRealization arena.signature}
    (_legacy : LegacyPrimitiveRealization arena statement realization)
    (proof : statement) : TheoremUnit.{u, v} arena.toArena := by
  letI := arena.toArena.stateDecidableEq
  exact
    { primitives := realization.toPrimitiveBundle
      Statement := statement
      proof := proof }

end LegacyPrimitiveRealization

/-- A finite indexed collection of theorem units over one arena. -/
structure Catalog (arena : Arena.{u}) where
  Index : Type w
  indexFintype : Fintype Index
  indexDecidableEq : DecidableEq Index
  theoremAt : Index -> TheoremUnit.{u, v} arena

namespace Catalog

/-- Construct a catalog from a finite vector of theorem units. -/
def ofVector {arena : Arena.{u}} {n : Nat}
    (units : Fin n -> TheoremUnit.{u, v} arena) : Catalog.{u, v, 0} arena where
  Index := Fin n
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  theoremAt := units

/-- The complete finite set of catalog indices. -/
def fullIndexSet {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena) :
    Finset catalog.Index := by
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  exact Finset.univ

/-- The complete index set with one specified theorem removed. -/
def without {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) : Finset catalog.Index := by
  letI := catalog.indexDecidableEq
  exact catalog.fullIndexSet.erase index

/-- Membership in a leave-one-out set is precisely inequality with the removed index. -/
theorem mem_without_iff {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (removed candidate : catalog.Index) :
    candidate ∈ catalog.without removed <-> candidate ≠ removed := by
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  simp [without, fullIndexSet]

/-- Removing one index decreases the full catalog cardinality by exactly one. -/
theorem without_card {arena : Arena.{u}} (catalog : Catalog.{u, v, w} arena)
    (index : catalog.Index) :
    (catalog.without index).card =
      @Fintype.card catalog.Index catalog.indexFintype - 1 := by
  letI := catalog.indexFintype
  letI := catalog.indexDecidableEq
  simp [without, fullIndexSet, Finset.card_erase_of_mem]

/-- Vector-backed catalog lookup computes to the supplied theorem unit. -/
theorem theoremAt_ofVector {arena : Arena.{u}} {n : Nat}
    (units : Fin n -> TheoremUnit.{u, v} arena) (index : Fin n) :
    (Catalog.ofVector units).theoremAt index = units index :=
  rfl

end Catalog

private abbrev fixtureArena : Arena :=
  Arena.ofFintype (Bool × Bool)

private abbrev fixtureSignature : PrimitiveSignature fixtureArena.State where
  Index := Fin 2
  indexFintype := inferInstance
  indexDecidableEq := inferInstance
  Output := fun _ => Bool
  outputDecidableEq := fun _ => inferInstance
  axis := fun _ => .cut
  AnchorIndex := Fin 0
  anchorFintype := inferInstance
  anchorDecidableEq := inferInstance

private def fixtureLawArena : PrimitiveLawArena where
  toArena := fixtureArena
  signature := fixtureSignature
  Law := fun realization =>
    forall x y,
      (forall i, realization.readout i x = realization.readout i y) -> x = y

private def fixtureRealization : PrimitiveRealization fixtureSignature where
  readout := fun i x => if i = 0 then x.1 else x.2
  anchor := fun i => Fin.elim0 i

/- A two-CUT realization on `Bool × Bool` is jointly faithful. -/
example : NativeTheoremUnit fixtureLawArena where
  realization := fixtureRealization
  proof := by
    change forall x y : Bool × Bool,
      (forall i : Fin 2,
        (if i = 0 then x.1 else x.2) = (if i = 0 then y.1 else y.2)) -> x = y
    decide

end D5.S3.ConceptDynamics.InformationEscape
