import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.PhysicalParserField
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S0.Computability.Coding.PhysicalParserField

open _root_.D5.S0.Computability.Coding PhysicalSixParser
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open Reg.Support.PhysicalParserCells LeanInformationAudit

/- The Law retains every source premise, conclusion and prefix bound. Its only
intervention replaces the specified Boolean cell observations. At the identity
readout it is the complete original statement; erasure contradicts a required
true cell and the retained frame. The further residual remains open. -/
open PhysicalParserField

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ (m : Track → ℤ → Bool) (h : Track → ℤ) (i : Fin 6)
    (n N : ℕ) (payload : List Bool) (hN : n + 2 * payload.length + 1 ≤ N)
    (hraw : ∀ k < 2 * payload.length + 1, m (0,false) (n + k + 1) =
      (List.replicate payload.length true ++ false :: payload)[k]?.getD false),
    ∃ T : ℕ, T ≤ (2 * payload.length + 1) * (8 * N + 20) + 2 ∧
      run (configuration m h i n [] 0 (.header i 0)) T =
        observeCells r
          (configuration m h i (n + 2 * payload.length + 1) payload.reverse 0 (next i)) ∧
      ∀ t ≤ T, Frame m h i N (run (configuration m h i n [] 0 (.header i 0)) t)

def cellRealization : PrimitiveRealization (cutSignature Bool Bool) :=
  @cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)

def erased_fails : ¬ arena.Law erased := by
  intro bad
  obtain ⟨T, _, result, frame⟩ := bad (fun t _ => t.2) (fun _ => 0) 0 0 1 [] (by simp)
    (by
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst k
      rfl)
  have cells := (frame T (by omega)).1 (0, true) (by decide) (by decide) (by decide)
  have contradiction := congrFun cells 0
  rw [result] at contradiction
  exact Bool.false_ne_true contradiction

def cellVariation : FiniteLawVariation arena :=
  ⟨cellRealization, erased, parse_field, erased_fails⟩

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

private theorem _root_.D5.S0.Computability.Coding.PhysicalParserField.parse_field.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.Coding.PhysicalParserField.arena (∀ (m : D5.S0.Computability.Coding.PhysicalSixParser.Track → Int → Bool) (h : D5.S0.Computability.Coding.PhysicalSixParser.Track → Int) (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (n N : Nat) (payload : List.{0} Bool) (hN : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Bool payload))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) N) (hraw : ∀ (k : Nat), @LT.lt.{0} Nat instLTNat k (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Bool payload)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) → @Eq.{1} Bool (m (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) Bool (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) (nat_lit 0))) Bool.false) (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt n) (@Nat.cast.{0} Int instNatCastInt k)) (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) (@Option.getD.{0} Bool (@GetElem?.getElem?.{0, 0, 0} (List.{0} Bool) Nat Bool (fun (as : List.{0} Bool) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Bool as)) (@List.instGetElem?NatLtLength.{0} Bool) (@HAppend.hAppend.{0, 0, 0} (List.{0} Bool) (List.{0} Bool) (List.{0} Bool) (@instHAppendOfAppend.{0} (List.{0} Bool) (@List.instAppend.{0} Bool)) (@List.replicate.{0} Bool (@List.length.{0} Bool payload) Bool.true) (@List.cons.{0} Bool Bool.false payload)) k) Bool.false)), @Exists.{1} Nat fun (T : Nat) => And (@LE.le.{0} Nat instLENat T (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Bool payload)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N) (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (And (@Eq.{1} D5.S0.Computability.Coding.PhysicalSixParser.Configuration (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalParserField.configuration m h i n (@List.nil.{0} Bool) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (D5.S0.Computability.Coding.PhysicalSixParser.Control.header i (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0))))) T) (D5.S0.Computability.Coding.PhysicalParserField.configuration m h i (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@List.length.{0} Bool payload))) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@List.reverse.{0} Bool payload) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (D5.S0.Computability.Coding.PhysicalParserField.next i))) (∀ (t : Nat), @LE.le.{0} Nat instLENat t T → D5.S0.Computability.Coding.PhysicalParserField.Frame m h i N (D5.S0.Computability.Coding.PhysicalSixParser.run (D5.S0.Computability.Coding.PhysicalParserField.configuration m h i n (@List.nil.{0} Bool) (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))) (D5.S0.Computability.Coding.PhysicalSixParser.Control.header i (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (nat_lit 0) (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0))))) t)))) Reg.D5.S0.Computability.Coding.PhysicalParserField.cellRealization := by exact ⟨Iff.rfl⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S0.Computability.Coding.PhysicalParserField.parse_field) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x))) (type_of% (Bool)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalParserField") 0) "D5") "S0") "Computability") "Coding") "PhysicalParserField") "parse_field") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "Coding") "PhysicalParserField") 0) "D5") "S0") "Computability") "Coding") "PhysicalParserField") "parse_field") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := .law ⟨(arena)⟩,
  objectArena := .law ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((cellRealization)) (cellRealization.toPrimitiveBundle) ⟨(D5.S0.Computability.Coding.PhysicalParserField.parse_field.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (D5.S0.Computability.Coding.PhysicalParserField.parse_field.__primitive_realization) (@_root_.D5.S0.Computability.Coding.PhysicalParserField.parse_field))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((cellRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)),
  variation := .evidence ⟨(cellVariation)⟩ (by first | exact (cellVariation) | exact ⟨_, _, (cellVariation)⟩),
  sensitivity := .evidence ⟨(cellSensitivity)⟩ (by exact (cellSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.Coding.PhysicalParserField, declaration := `D5.S0.Computability.Coding.PhysicalParserField.parse_field, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S0.Computability.Coding.PhysicalParserField


noncomputable def Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.Coding.PhysicalParserField.arena
noncomputable def Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"PhysicalParserField\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"PhysicalParserField\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.Coding.PhysicalParserField.arena
noncomputable def Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"PhysicalParserField\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"Coding\",\"PhysicalParserField\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.Coding.PhysicalParserField, declaration := `Reg.D5.S0.Computability.Coding.PhysicalParserField.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
