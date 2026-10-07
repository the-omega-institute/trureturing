import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.ClauseWordCodec
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ClauseWordCodec

open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.ClauseCodec
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ physical w n (F : UnaryFormula n),
    readWord physical (w.map (r.readout ())) = some ⟨n, F⟩ ↔
      w = encodeWord physical F ∧ ∀ c ∈ F, c.length ≤ 3

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro physical w n F
  change readWord physical (w.map (fun b => b)) = some ⟨n, F⟩ ↔ _
  rw [List.map_id']
  exact codec_exact physical w n F

def erased_fails : ¬ arena.Law erased := by
  intro h
  have bad := (h false (encodeWord false (n := 1) []) 1 []).mpr ⟨rfl, by simp⟩
  change readWord false ((encodeWord false (n := 1) []).map (fun _ => false)) =
    some ⟨1, []⟩ at bad
  have impossible : (0 : Nat) = 1 := by
    have p := congrArg (fun x : Option (Σ n, UnaryFormula n) => x.map Sigma.fst) bad
    simpa [encodeWord, bodyWord, readWord, readFixed, readUnary, readBody, bind, Option.bind] using p
  contradiction

def variation : FiniteLawVariation arena := ⟨symbols, erased, sourceLaw, erased_fails⟩

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def dependence : ∃ b b' : Bool, symbols.readout () b ≠ symbols.readout () b' :=
  ⟨false, true, Bool.false_ne_true⟩

private theorem _root_.PredictiveThermodynamic.ClauseCodec.codec_exact.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.ClauseWordCodec.arena (∀ (physical : Bool) (w : List.{0} Bool) (n : Nat) (F : PredictiveThermodynamic.UnaryFormula n), Iff (@Eq.{1} (Option.{0} (@Sigma.{0, 0} Nat fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n)) (PredictiveThermodynamic.ClauseCodec.readWord physical w) (@Option.some.{0} (@Sigma.{0, 0} Nat fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (@Sigma.mk.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) n F))) (And (@Eq.{1} (List.{0} Bool) w (@PredictiveThermodynamic.ClauseCodec.encodeWord n physical F)) (∀ (c : Std.Sat.CNF.Clause.{0} (Fin n)), @Membership.mem.{0, 0} (Std.Sat.CNF.Clause.{0} (Fin n)) (PredictiveThermodynamic.UnaryFormula n) (@List.instMembership.{0} (Std.Sat.CNF.Clause.{0} (Fin n))) F c → @LE.le.{0} Nat instLENat (@List.length.{0} (Std.Sat.Literal.{0} (Fin n)) c) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) Reg.D5.S0.Computability.ClauseWordCodec.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => codec_exact⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.PredictiveThermodynamic.ClauseCodec.codec_exact) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% (Bool)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClauseWordCodec") 0) "PredictiveThermodynamic") "ClauseCodec") "codec_exact") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClauseWordCodec") 0) "PredictiveThermodynamic") "ClauseCodec") "codec_exact") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := .law ⟨(arena)⟩,
  objectArena := .law ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.ClauseCodec.codec_exact.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (PredictiveThermodynamic.ClauseCodec.codec_exact.__primitive_realization) (@_root_.PredictiveThermodynamic.ClauseCodec.codec_exact))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((symbols.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b => b)),
  variation := .evidence ⟨(variation)⟩ (by first | exact (variation) | exact ⟨_, _, (variation)⟩),
  sensitivity := .evidence ⟨(sensitivity)⟩ (by exact (sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.ClauseWordCodec, declaration := `PredictiveThermodynamic.ClauseCodec.codec_exact, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S0.Computability.ClauseWordCodec


noncomputable def Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.ClauseWordCodec.arena
noncomputable def Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseWordCodec\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseWordCodec\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.ClauseWordCodec.arena
noncomputable def Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseWordCodec\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseWordCodec\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ClauseWordCodec, declaration := `Reg.D5.S0.Computability.ClauseWordCodec.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
