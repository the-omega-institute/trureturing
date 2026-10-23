import D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.Observer
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformPatterns
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open ActualCutPartitionRecovery (LiteralRow CutSet)
open NativeDepthPatterns (History)
open LeanInformationAudit

abbrev codecSignature : Signature where
  Params := Unit
  State := fun _ => CommonCode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option CommonData
  Anchor := Empty
  finiteAnchor := inferInstance

def codecActual : Realization codecSignature := realize codecSignature
  (fun _ _ w => parseCommon w) (fun e => nomatch e)

def codecRejected : Realization codecSignature := realize codecSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev codecArena : Arena where
  signature := codecSignature
  Law R := Primrec (R.readout () ()) ∧ ∀ C Q H N,
    R.readout () () (codeCommon C Q H N) = some (C,Q.sort (· ≤ ·),H,N)

private theorem codec_rejected : ¬ codecArena.Law codecRejected := by
  intro h
  have bad := h.2 (FreeMagma.of (.inl false)) ∅ [] 0
  cases bad

def codecEvidence : Registration codecArena (codecArena.Law codecActual) where
  actual := codecActual
  bridge := Iff.rfl
  variation := ⟨uniform_common_codec,codecRejected,codec_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨codecRejected,?_,rfl,codec_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),codeCommon (FreeMagma.of (.inl false)) ∅ [] 0,
      codeCommon (FreeMagma.of (.inl true)) ∅ [] 0,?_⟩
    change parseCommon _ ≠ parseCommon _
    rw [uniform_common_codec.2, uniform_common_codec.2]
    intro h
    have hr := congrArg (fun s : CommonData => s.1) (Option.some.inj h)
    cases hr

abbrev cellSignature : Signature where
  Params := Unit
  State := fun _ => CommonCode
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Option CellCode
  Anchor := Empty
  finiteAnchor := inferInstance

def cellActual : Realization cellSignature := realize cellSignature
  (fun _ _ w => materializeCells w) (fun e => nomatch e)

def cellRejected : Realization cellSignature := realize cellSignature
  (fun _ _ _ => none) (fun e => nomatch e)

abbrev cellArena : Arena where
  signature := cellSignature
  Law R := Primrec (R.readout () ()) ∧ ∀ C Q H N,
    R.readout () () (codeCommon C Q H N) =
      some (NativeHistoryCells.requiredDepth Q H,
        (NativeWholeRowService.classList C).map Subtype.val,
        (NativeWholeRowService.allPatterns C (NativeHistoryCells.requiredDepth Q H)).map familyWord)

private theorem cell_rejected : ¬ cellArena.Law cellRejected := by
  intro h
  have bad := h.2 (FreeMagma.of (.inl false)) ∅ [] 0
  cases bad

def cellEvidence : Registration cellArena (cellArena.Law cellActual) where
  actual := cellActual
  bridge := Iff.rfl
  variation := ⟨uniform_cell_materializer,cellRejected,cell_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cellRejected,?_,rfl,cell_rejected⟩
      intro j ne
      exact (ne (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(),codeCommon (FreeMagma.of (.inl false)) ∅ [] 0,
      codeCommon (FreeMagma.of (.inl false)) {[false]} [] 0,?_⟩
    dsimp only [cellActual, realize]
    change materializeCells (codeCommon (FreeMagma.of (.inl false)) ∅ [] 0) ≠
      materializeCells (codeCommon (FreeMagma.of (.inl false)) {[false]} [] 0)
    rw [uniform_cell_materializer.2, uniform_cell_materializer.2]
    intro h
    have hd := congrArg (fun s : CellCode => s.1) (Option.some.inj h)
    simp [NativeHistoryCells.requiredDepth, ActualCutPartitionRecovery.cutDepth] at hd

/- The typed whole-family proofs preserve each complete infinite input claim.
   Contract source-selection coordinates and raw occurrence ties remain
   unregistered; these proof records claim no declared_validated status. -/

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformInput
