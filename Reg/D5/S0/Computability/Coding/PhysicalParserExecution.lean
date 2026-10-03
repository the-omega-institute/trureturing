import LeanInformationAuditInterface.Contract.Registration
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

theorem _root_._private.Reg.D5.S0.Computability.Coding.PhysicalParserExecution.0.D5.S0.Computability.Coding.PhysicalParserExecution.parser_frame_resources.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.Coding.PhysicalParserExecution.arena (And D5.S0.Computability.Coding.PhysicalSixParser.Contract (And (∀ (x y : Int), @List.IsPrefix.{0} Bool (D5.S0.Computability.Coding.PhysicalSixParser.headDescription x) (D5.S0.Computability.Coding.PhysicalSixParser.headDescription y) → @Eq.{1} Int x y) (∀ (q : List.{0} Bool) (n : Nat), And (@Eq.{1} Int (D5.S0.Computability.Coding.PhysicalSixParser.Configuration.head (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalSixParser.initial q) n) (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 0))) Bool.true)) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))) (@Eq.{1} (Int → Bool) (D5.S0.Computability.Coding.PhysicalSixParser.Configuration.cell (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalSixParser.initial q) n) (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 0))) Bool.false)) (D5.S0.Computability.Coding.PhysicalSixParser.rawCell q))))) Reg.D5.S0.Computability.Coding.PhysicalParserExecution.cellRealization := by exact ⟨Iff.rfl⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Computability.Coding.PhysicalParserExecution.parser_frame_resources) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))) (type_of% (cellVariation)) (type_of% (cellSensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalParserExecution") 0) "D5") "S0") "Computability") "Coding") "PhysicalParserExecution") "parser_frame_resources") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalParserExecution") 0) "D5") "S0") "Computability") "Coding") "PhysicalParserExecution") "parser_frame_resources") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((cellRealization)) (cellRealization.toPrimitiveBundle) ⟨(D5.S0.Computability.Coding.PhysicalParserExecution.parser_frame_resources.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)),
  variation := some ⟨(cellVariation)⟩,
  sensitivity := some ⟨(cellSensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.Coding.PhysicalParserExecution
