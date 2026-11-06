/- Source operand preparation only: UNCOMPILED. Source selection, four-slot
   families, enrollment, readouts, audits and registration remain OPEN.
   Observed native audit counts: 0. No selector or validated receipt is invented. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.OriginalLabelTwoSum.Graph
import D5.S3.Geometry.OriginalLabelTwoSum.Replay
import D5.S3.Geometry.OriginalLabelTwoSum.Cone
import D5.S3.Geometry.OriginalLabelTwoSum.ParentCells
import D5.S3.Geometry.OriginalLabelTwoSum.CellLabels
import D5.S3.Geometry.OriginalLabelTwoSum.WheelSupplier
import D5.S3.Geometry.OriginalLabelTwoSum.RowIteration

noncomputable section
open Finset
open _root_.D5.S3.Geometry.OriginalLabelTwoSum
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
namespace Reg.D5.S3.Geometry.OriginalLabelTwoSum.DirectOperands
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev rowTransportSource := type_of% (@row_transport.{u})
def rowFaces (r : Rows V) (s : Finset V) : Prop := s ∈ r.root

abbrev rectangleOrderSource := type_of% (@rectangle_order.{u})
def fibreSchedule (F : Finset (Finset V)) : List (Finset V) := fibres F

abbrev replaySource := type_of% (@replaySequence.{u})
def replayInputPairs {M N : PreAbstractSimplicialComplex V} (S : Sequence M N) :=
  S.pairs.map (fun P => (P.lower,P.upper))

abbrev gammaPairsSource := type_of% (@Wheel.gamma_pairs)
def gammaPairs : List (Finset Wheel.Label × Finset Wheel.Label) :=
  Wheel.gamma.pairs.map (fun P => (P.lower,P.upper))

def localMainPairs : List (Finset Wheel.Label × Finset Wheel.Label) :=
  Wheel.fill1.main.pairs.map (fun P => (P.lower,P.upper))
def separateCollarPairs : List (Finset Wheel.Label × Finset Wheel.Label) :=
  Wheel.fill1.separate.pairs.map (fun P => (P.lower,P.upper))

abbrev collarFailureSource := type_of% (@Wheel.collar_not_free_in_main)
def collarOnly : Family Wheel.Label := Wheel.fill1.collar
def fullRetained : Family Wheel.Label := endpoint Wheel.fill1.collar Wheel.fill1.critical

abbrev parentCellsSource := type_of% (@parentCellData.{u})
def computedParentCore (X Y Z : Finset V) (e : V) (E C : Family V)
    (critical : Finset (Finset V)) (B0 B1 : Family V) : Family V :=
  parentCore X Y Z e E C critical B0 B1
def computedParentCritical (e : V) (C A B : Finset (Finset V)) : Finset (Finset V) :=
  parentCritical e C A B

abbrev criticalSizeSource := type_of% (@wheelCell_card.{u})
def transformedCritical (e a c d : V) (s : Finset V) : Finset V := wheelCell e a c d s

abbrev closedRecurrenceSource := type_of% (@ClosedChain.critical_recurrence)
def closedCritical (n : Nat) : Finset ClosedChain.Label × Finset ClosedChain.Label :=
  (ClosedChain.first n,ClosedChain.second n)

abbrev wheelGraphSource := type_of% (@Wheel.wheelOriginalRoot)
abbrev seedGraphSource := type_of% (@K4.seedOriginalRoot)

abbrev batchSource := type_of% (@batchFibre.{u,u})
abbrev criticalFibreSource := type_of% (@parent_fibre_cross.{u})
abbrev compilerSource := type_of% (@compileParent.{u})
abbrev renameSequenceSource := type_of% (@renameSequence.{u,u})
abbrev wheelSupplierSource := type_of% (@WheelSupplier.oneStep.{u})
abbrev rowIterationSource := type_of% (@rowHistory_statistics.{u})
abbrev wheelStatisticsSource := type_of% (@WheelSupplier.oneStep_statistics.{u})

def suppliedMainPairs {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hd : Disjoint X (Wheel.Y.image f)) :=
  (WheelSupplier.oneStep c f hf0 heX hd).main.pairs.map (fun P => (P.lower,P.upper))

def suppliedCorePairs {X : Finset V} {e : V} {K : Family V}
    (c : Certificate (insert e X) K) (f : Wheel.Label ↪ V)
    (hf0 : f 0 = e) (heX : e ∉ X) (hd : Disjoint X (Wheel.Y.image f)) :=
  (WheelSupplier.oneStep c f hf0 heX hd).separate.pairs.map (fun P => (P.lower,P.upper))


end Reg.D5.S3.Geometry.OriginalLabelTwoSum.DirectOperands
