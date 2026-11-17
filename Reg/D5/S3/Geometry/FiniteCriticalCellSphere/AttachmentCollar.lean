import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SourceSelection
import D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar

/-! Exact original telescopes and literal source operands for the attachment collar.

These proof terms establish agreement with the source theorems. They are not
four-slot registrations. A lawful source layout, enrolled readout application,
whole-family variation, sensitivity and observational dependence remain missing.
-/

noncomputable section
open Set
open scoped unitInterval
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteCriticalCellSphere

namespace Reg.D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar
universe u

namespace DiskInRestrict
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V)
    (x : A.diskSet), A.diskIn (A.diskRestrict x) = x.1

theorem source : Telescope.{u} := @Attachment.diskIn_restrict.{u}

theorem source_bridge :
    (type_of% (@Attachment.diskIn_restrict.{u})) ↔ Telescope.{u} := Iff.rfl

def observation {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) (x : A.diskSet) : Space A.X :=
  A.diskIn (A.diskRestrict x)

/- Candidate actual point observation: observation A, state x : A.diskSet.
   Its state and output depend on the original A and its ambient dictionaries.
   Selecting those dictionaries as Params is rejected by the inspected resolve
   contract; packing them and A into a new SourceState would not match a source
   operand. No dependency-closed lawful source layout is supplied here. -/
end DiskInRestrict

namespace RestrictDiskIn
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V)
    (x : A.Disk),
    A.diskRestrict ⟨A.diskIn x,
      (_root_.D5.S3.Geometry.FiniteSimplexBoundarySphere.faceCoordinateHomeomorph A.face x).2⟩ = x

theorem source : Telescope.{u} := @Attachment.restrict_diskIn.{u}

theorem source_bridge :
    (type_of% (@Attachment.restrict_diskIn.{u})) ↔ Telescope.{u} := Iff.rfl

def observation {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) (x : A.Disk) : A.Disk :=
  A.diskRestrict ⟨A.diskIn x,
    (_root_.D5.S3.Geometry.FiniteSimplexBoundarySphere.faceCoordinateHomeomorph A.face x).2⟩

/- Candidate actual point observation: observation A, state x : A.Disk.
   The dictionary-dependent state/output and explicit A must be reconstructed
   in their original scope. Neither a new pair state nor a truth-valued equality
   readout repairs that obligation. No source layout or four-slot family is
   asserted. -/
end RestrictDiskIn

namespace Cover
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V)
    (x : Space A.X), x ∈ A.coreSet ∨ x ∈ A.diskSet

theorem source : Telescope.{u} := @Attachment.cover.{u}

theorem source_bridge :
    (type_of% (@Attachment.cover.{u})) ↔ Telescope.{u} := Iff.rfl

def coreOperand {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) : Set (Space A.X) := A.coreSet

def diskOperand {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) : Set (Space A.X) := A.diskSet

/- These are the two actual set operands, not decisions of the proved cover.
   Treating x as state leaves both set readouts constant within that state fiber,
   so it supplies no actual observational-dependence witness. Treating A as
   state makes the output carrier Space A.X depend on state; Signature.Output
   depends only on role and Params. A lawful alternative layout and its source
   reconstruction remain missing. -/
end Cover

namespace CoreClosed
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V),
    IsClosed A.coreSet

theorem source : Telescope.{u} := @Attachment.core_closed.{u}

theorem source_bridge :
    (type_of% (@Attachment.core_closed.{u})) ↔ Telescope.{u} := Iff.rfl

def observation {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) : Set (Space A.X) := A.coreSet

/- The source has no point-state binder. Its actual set operand depends on the
   explicit attachment, including the state-dependent ambient carrier if A is
   chosen as state. Choosing a dummy state gives a constant actual readout.
   Neither layout supplies a faithful dependent-family registration. -/
end CoreClosed

namespace DiskClosed
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V),
    IsClosed A.diskSet

theorem source : Telescope.{u} := @Attachment.disk_closed.{u}

theorem source_bridge :
    (type_of% (@Attachment.disk_closed.{u})) ↔ Telescope.{u} := Iff.rfl

def observation {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) : Set (Space A.X) := A.diskSet

/- The same concrete layout obstruction as CoreClosed applies to this actual
   attached-simplex set. A Boolean IsClosed readout would replace the original
   set operand by a proved property and is not submitted. -/
end DiskClosed

namespace DiskInMemCoreIff
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V)
    (x : A.Disk),
    A.diskIn x ∈ A.coreSet ↔ _root_.D5.S3.Geometry.FiniteSimplexBoundarySphere.boundary x

theorem source : Telescope.{u} := @Attachment.diskIn_mem_core_iff.{u}

theorem source_bridge :
    (type_of% (@Attachment.diskIn_mem_core_iff.{u})) ↔ Telescope.{u} := Iff.rfl

def observation {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) (x : A.Disk) : Space A.X := A.diskIn x

def coreOperand {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) : Set (Space A.X) := A.coreSet

/- The actual point observation diskIn x is preserved. A family must still
   reconstruct membership in this very core and the full face-only boundary,
   with the original dependent state, output and dictionaries. An arbitrary
   equality/iff template with a Boolean readout does not establish that match.
   No native source selection, intervention law or dependence witness has been
   supplied. Singleton face fibers remain in the complete Telescope. -/
end DiskInMemCoreIff

namespace CutPos
abbrev Telescope : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (A : Attachment V)
    (s : I), 0 < A.cut s

theorem source : Telescope.{u} := @Attachment.cut_pos.{u}

theorem source_bridge :
    (type_of% (@Attachment.cut_pos.{u})) ↔ Telescope.{u} := Iff.rfl

def observation {V : Type u} [Fintype V] [DecidableEq V]
    (A : Attachment V) (s : I) : ℝ := A.cut s

/- This actual real observation, unlike decide (0 < A.cut s), varies in s.
   A possible one-role family uses State=I and real Output, with Law retaining
   the entire Telescope and replacing only cut(s). However the raw occurrence
   A.cut s still contains the source A/dictionary arguments; the inspected
   transport follows raw source dependencies rather than just mathematical
   independence after unfolding cut. Its lawful Params projection, exact
   native occurrence and reconstruction have not been established. Whole-law
   rejection also needs a genuine attachment instance, not an assumed desired
   law or a discarded empty source fiber. No selector or completed family is
   invented here. -/
end CutPos

/- Enrollment is available for the generic realize template, not evidence that
   any of the layouts above is accepted. These named source/observation proof
   terms can be compiled independently of a later registration decision. -/
#check @Reg.Support.DependentFamily.enrollment_1

end Reg.D5.S3.Geometry.FiniteCriticalCellSphere.AttachmentCollar
