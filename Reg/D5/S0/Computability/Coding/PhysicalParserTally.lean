import D5.S0.Computability.Coding.PhysicalParserTally
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.Coding.PhysicalParserTally

open _root_.D5.S0.Computability.Coding PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open Reg.Support.PhysicalParserCells LeanInformationAudit

/- The Law retains every source premise, conclusion and prefix bound. Its only
intervention replaces the specified Boolean cell observations. At the identity
readout it is the complete original statement; erasure contradicts a required
true cell and the retained frame. The further residual remains open. -/
open PhysicalParserTally

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (u n : ℕ) (c : Continuation),
    ∃ T : ℕ, T ≤ 8 * n.bits.length + 14 ∧
      run (configuration m h u n.bits 0 (.count c 0)) T =
        observeCells r (configuration m h (u + 1) (n + 1).bits 0 (resume c)) ∧
      ∀ t ≤ T, Frame m h u n.bits.length
        (run (configuration m h u n.bits 0 (.count c 0)) t)

def cellRealization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def erased_fails : ¬ arena.Law erased := by
  intro bad
  obtain ⟨T, _, result, frame⟩ := bad (fun _ _ => true) (fun _ => 0) 0 0 .finish
  have cells := ((frame T (by omega)).1 (0, true) (by decide) (by decide)).2
  have contradiction := congrFun cells 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def cellVariation : FiniteLawVariation arena :=
  ⟨cellRealization, erased, count_one, erased_fails⟩

def cellSensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := cellVariation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i


/-- The actual observation distinguishes the two physical Boolean cell values. -/
def dependence : ∃ b b' : Bool, cellRealization.readout () b ≠ cellRealization.readout () b' :=
  ⟨false, true, Bool.false_ne_true⟩

register_information_theorem _root_.D5.S0.Computability.Coding.PhysicalParserTally.count_one in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives cellRealization.toPrimitiveBundle
  realization inline (cellRealization) := by exact ⟨Iff.rfl⟩
  variation cellVariation sensitivity cellSensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.Coding.PhysicalParserTally
