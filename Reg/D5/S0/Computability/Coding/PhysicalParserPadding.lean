import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.PhysicalParserPadding
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.Coding.PhysicalParserPadding

open _root_.D5.S0.Computability.Coding PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open Reg.Support.PhysicalParserCells LeanInformationAudit

/- The Law retains every source premise, conclusion and prefix bound. Its only
intervention replaces the specified Boolean cell observations. At the identity
readout it is the complete original statement; erasure contradicts a required
true cell and the retained frame. The further residual remains open. -/
open PhysicalParserPadding

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6) (W : ℕ)
    (bs : List Bool) (hlen : bs.length ≤ W),
    ∃ T : ℕ, T ≤ 14 * W + 11 ∧
      run (configuration m h i W bs 0 (.pad i 0)) T =
        observeCells r
          (configuration m h i W (bs ++ List.replicate (W - bs.length) false) 0 (next i)) ∧
      ∀ t ≤ T, Frame m h i W (run (configuration m h i W bs 0 (.pad i 0)) t)

def cellRealization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def erased_fails : ¬ arena.Law erased := by
  intro bad
  obtain ⟨T, _, result, frame⟩ := bad (fun _ _ => true) (fun _ => 0) 0 0 [] (by simp)
  have cells := ((frame T (by omega)).1 (0, true) (by decide) (by decide)).2
  have contradiction := congrFun cells 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def cellVariation : FiniteLawVariation arena :=
  ⟨cellRealization, erased, pad_one, erased_fails⟩

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

theorem _root_._private.Reg.D5.S0.Computability.Coding.PhysicalParserPadding.0.D5.S0.Computability.Coding.PhysicalParserPadding.pad_one.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.Coding.PhysicalParserPadding.arena (∀ (m : D5.S0.Computability.Coding.PhysicalSixParser.Track → Int → Bool) (h : D5.S0.Computability.Coding.PhysicalSixParser.Track → Int) (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (W : Nat) (bs : List.{0} Bool) (hlen : @LE.le.{0} Nat instLENat (@List.length.{0} Bool bs) W), @Exists.{1} Nat fun (T : Nat) => And (@LE.le.{0} Nat instLENat T (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) W) (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))) (And (@Eq.{1} D5.S0.Computability.Coding.PhysicalSixParser.Configuration (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalParserPadding.configuration m h i W bs (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (D5.S0.Computability.Coding.PhysicalSixParser.Control.pad i (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))) (nat_lit 0))))) T) (D5.S0.Computability.Coding.PhysicalParserPadding.configuration m h i W (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool) (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) bs (@List.replicate.{0} Bool (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) W (@List.length.{0} Bool bs)) Bool.false)) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (D5.S0.Computability.Coding.PhysicalParserPadding.next i))) (∀ (t : Nat), @LE.le.{0} Nat instLENat t T → D5.S0.Computability.Coding.PhysicalParserPadding.Frame m h i W (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalParserPadding.configuration m h i W bs (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (D5.S0.Computability.Coding.PhysicalSixParser.Control.pad i (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))) (nat_lit 0))))) t)))) Reg.D5.S0.Computability.Coding.PhysicalParserPadding.cellRealization := by exact ⟨Iff.rfl⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S0.Computability.Coding.PhysicalParserPadding.pad_one) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))) (type_of% (cellVariation)) (type_of% (cellSensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalParserPadding") 0) "D5") "S0") "Computability") "Coding") "PhysicalParserPadding") "pad_one") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalParserPadding") 0) "D5") "S0") "Computability") "Coding") "PhysicalParserPadding") "pad_one") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((cellRealization)) (cellRealization.toPrimitiveBundle) ⟨(D5.S0.Computability.Coding.PhysicalParserPadding.pad_one.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)),
  variation := some ⟨(cellVariation)⟩,
  sensitivity := some ⟨(cellSensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.Coding.PhysicalParserPadding
