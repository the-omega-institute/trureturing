/- GID: D5/S0/Computability/PhysicalDivider/FiniteControl
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite control carrier for the concrete framed physical divider. -/

import D5.S0.Computability.PhysicalDivider.PhysicalTape

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S0.Computability.PhysicalDivider

open Turing Lax51Proofs.RamToTM

/-- Only substatements of the actual fixed divider are admitted as continuations. -/
noncomputable def sourceCode : Finset (TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl) := by
  classical
  exact Finset.univ.biUnion (fun label : DivLabel => TM2.stmts₁ (divMachine.m label))

abbrev SourceNode := {q // q ∈ sourceCode}

noncomputable instance : Fintype SourceNode := by
  classical
  exact Fintype.ofFinset sourceCode (fun _ => Iff.rfl)

/-- Enter a specific source label; the membership proof is not machine data. -/
def sourceEntry (label : DivLabel) : SourceNode :=
  ⟨divMachine.m label, by
    classical
    change divMachine.m label ∈
      Finset.univ.biUnion (fun l : DivLabel => TM2.stmts₁ (divMachine.m l))
    exact Finset.mem_biUnion.mpr ⟨label, Finset.mem_univ _, TM2.stmts₁_self⟩⟩

/-- Select an actual remaining substatement, retaining its finite-code membership. -/
def sourceChild (parent : SourceNode)
    (child : TM2.Stmt (fun _ : DivStack => Bool) DivLabel DivControl)
    (h : child ∈ TM2.stmts₁ parent.val) : SourceNode :=
  ⟨child, by
    classical
    have hp := parent.property
    change parent.val ∈
      Finset.univ.biUnion (fun l : DivLabel => TM2.stmts₁ (divMachine.m l)) at hp
    change child ∈ Finset.univ.biUnion (fun l : DivLabel => TM2.stmts₁ (divMachine.m l))
    obtain ⟨label, hlabel, hparent⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr
      ⟨label, hlabel, TM2.stmts₁_trans hparent h⟩⟩

/-- Fixed preparation, copy-out, clearing and parking phases. -/
inductive FrameLabel
  | seekA | seekD | seekCapacity | seekQ | clearQ | clearQRead
  | seekR | clearR | clearRRead
  | loadA | loadARead | loadAPush | loadABackup
  | restoreA | restoreARead | restoreAPush
  | padD | loadD | loadDRead | loadDPush
  | restoreD | restoreDRead | restoreDPush | restoreDCopy
  | padR | loadCapacity | loadCapacityRead | loadCapacityPush | loadCapacityZero
  | restoreCapacity | restoreCapacityRead | restoreCapacityPush | enterSource
  | copyQ | copyQRead | copyQReverse | emitQ | emitQRead | emitQPush
  | copyR | copyRRead | copyRReverse | emitR | emitRRead | emitRPush
  | clearDivisor | clearDivisorRead
  | parkDividend | parkDivisor | parkRemainder | parkQuotient
  | parkDivisorBackup | parkRemainderBackup | parkDifference | parkShift
  | parkA | parkD | parkCapacity | parkCapacityBackup | parkQ | parkR | signalReturn
  deriving DecidableEq, Fintype, Inhabited

/-- The result of a block operation has only these finite destinations. -/
inductive Continuation
  | frame (label : FrameLabel) (saved : Option Bool) (replace : Bool)
  | sourcePush (parent : SourceNode) (state : DivControl)
  | sourceRead (parent : SourceNode) (state : DivControl)

noncomputable instance : Fintype Continuation := derive_fintype% _

inductive Control
  | frame (label : FrameLabel) (held : Option Bool)
  | sourceLabel (label : DivLabel) (state : DivControl)
  | sourceStmt (node : SourceNode) (state : DivControl)
  | block (tape : ActiveTape) (pc : BlockControl) (next : Continuation)
  | returned

noncomputable instance : Fintype Control := derive_fintype% _

/-- There are exactly three elementary actions. Signalling uses a counted read. -/
inductive Instruction
  | read (tape : ActiveTape) (next : Bool → Control)
  | write (tape : ActiveTape) (bit : Bool) (next : Control)
  | move (tape : ActiveTape) (direction : Dir) (next : Control)

structure PhysicalCfg where
  control : Control
  tapes : ActiveTape → Tape Bool

/-- Lift one elementary block action to its statically selected physical tape. -/
def liftBlockAction (tape : ActiveTape) (next : Continuation) : BlockAction → Instruction
  | .read f => .read tape (fun b => .block tape (f b) next)
  | .write b pc => .write tape b (.block tape pc next)
  | .move d pc => .move tape d (.block tape pc next)

/-- Administrative transitions also execute a physical read. -/
def controlRead (next : Control) : Instruction :=
  .read (.inl .dividend) (fun _ => next)

def startBlock (tape : ActiveTape) (pc : BlockControl) (next : Continuation) : Instruction :=
  match blockAction pc with
  | some action => liftBlockAction tape next action
  | none => controlRead (.block tape pc next)

/-- Returning from push/pop/peek evaluates only the original finite Boolean control map. -/
def continueBlock : Continuation → Option Bool → Control
  | .frame label saved replace, result => .frame label (if replace then result else saved)
  | .sourcePush parent state, _ =>
      match h : parent.val with
      | .push _ _ child => .sourceStmt (sourceChild parent child (by
          classical
          rw [h]
          exact Finset.mem_insert_of_mem TM2.stmts₁_self)) state
      | _ => .returned
  | .sourceRead parent state, result =>
      match h : parent.val with
      | .pop _ f child | .peek _ f child => .sourceStmt (sourceChild parent child (by
          classical
          rw [h]
          exact Finset.mem_insert_of_mem TM2.stmts₁_self)) (f state result)
      | _ => .returned

end D5.S0.Computability.PhysicalDivider
