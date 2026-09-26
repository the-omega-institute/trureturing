import D5.S0.Computability.Coding.PhysicalSixParser
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.Coding.PhysicalSixParser

open _root_.D5.S0.Computability.Coding PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open Reg.Support.PhysicalParserCells LeanInformationAudit

/- The Law retains every source premise, conclusion and prefix bound. Its only
intervention replaces the specified Boolean cell observations. At the identity
readout it is the complete original statement; erasure contradicts a required
true cell and the retained frame. The further residual remains open. -/

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (W B k : ℕ)
    (hhome : m (7, false) 0 = false ∧ m (7, true) 0 = true)
    (hmarks : ∀ j : ℕ, 0 < j → j ≤ W → m (7, false) j = true ∧ m (7, true) j = true)
    (hk : k ≤ W) (hB : k ≤ B),
    run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ (5 * k + 2) =
        observeCells r ⟨.pad 0 0, rewindHeads h 0 0 0, m⟩ ∧
      ∀ n ≤ 5 * k + 2, RewindFrame m h B
        (run ⟨.sourceRewind 0, rewindHeads h k k k, m⟩ n)

def cellRealization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def erased_fails : ¬ arena.Law erased := by
  intro bad
  obtain ⟨result, frame⟩ := bad (fun t _ => t.2) (fun _ => 0) 0 0 0
    ⟨rfl, rfl⟩ (by intro j hj hj0; omega) (by omega) (by omega)
  obtain ⟨a, b, c, _, _, _, _, _, _, cells⟩ := frame 2 (by omega)
  have contradiction := congrFun (congrFun cells (0, true)) 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def cellVariation : FiniteLawVariation arena :=
  ⟨cellRealization, erased, coupled_source_rewind, erased_fails⟩

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

register_information_theorem _root_.D5.S0.Computability.Coding.PhysicalSixParser.coupled_source_rewind in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))
  primitives cellRealization.toPrimitiveBundle
  realization inline (cellRealization) := by exact ⟨Iff.rfl⟩
  variation cellVariation sensitivity cellSensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.Coding.PhysicalSixParser
