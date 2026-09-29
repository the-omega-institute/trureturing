import D5.S0.Computability.Coding.PhysicalParserExecution
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.Coding.PhysicalParserExecution

open _root_.D5.S0.Computability.Coding PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open Reg.Support.PhysicalParserCells LeanInformationAudit

/- The Law retains every source premise, conclusion and prefix bound. Its only
intervention replaces the specified Boolean cell observations. At the identity
readout it is the complete original statement; erasure contradicts a required
true cell and the retained frame. The further residual remains open. -/
open PhysicalParserExecution

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := Contract ∧ (∀ x y : ℤ, headDescription x <+: headDescription y → x = y) ∧
    (∀ q : List Bool, ∀ n : ℕ,
      (run (initial q) n).head (0,true) = 0 ∧
      (run (initial q) n).cell (0,false) = fun z => r.readout () (rawCell q z))

def cellRealization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def erased_fails : ¬ arena.Law erased := by
  intro bad
  have contradiction := congrFun (bad.2.2 [true] 0).2 1
  exact Bool.false_ne_true contradiction.symm

def cellVariation : FiniteLawVariation arena :=
  ⟨cellRealization, erased, parser_frame_resources, erased_fails⟩

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

register_information_theorem _root_.D5.S0.Computability.Coding.PhysicalParserExecution.parser_frame_resources in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives cellRealization.toPrimitiveBundle
  realization inline (cellRealization) := by exact ⟨Iff.rfl⟩
  variation cellVariation sensitivity cellSensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.Coding.PhysicalParserExecution
