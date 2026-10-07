import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.RationalMalformedCleanup
import Reg.D5.S0.Computability.RationalPostprocessor
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.RationalMalformedCleanup
open _root_.PredictiveThermodynamic _root_.Lax51Proofs.RamToTM Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype ResponseSymbol
  signature := cutSignature ResponseSymbol ResponseSymbol
  Law r := ∀ st input quotient shifts,
    Nonempty (EvalsToInTime postMachine.step
      (postCfg .badInput st input quotient shifts [])
      (some (haltList postMachine ([ResponseSymbol.zero].map (r.readout ()))))
      (input.length+quotient.length+shifts.length+3))

def symbols : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun _ => ResponseSymbol.one)

def sourceLaw : arena.Law symbols := by
  intro st input quotient shifts
  exact post_error_cleanup st input quotient shifts

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨bad⟩ := law default [] [] []
  obtain ⟨good⟩ := post_error_cleanup default [] [] []
  have same := RationalPostprocessor.terminal_unique postMachine.step good bad (by rfl) (by rfl)
  have output := congrArg (fun c : postMachine.Cfg => c.stk .output) same
  have impossible : ([ResponseSymbol.zero] : List ResponseSymbol) = [.one] := output
  cases impossible

def variation : FiniteLawVariation arena := ⟨symbols,erased,sourceLaw,erased_fails⟩

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r,r',hr,hr'⟩ := variation
    refine ⟨r,r',?_,?_,⟨fun _ => hr',fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def dependence : ∃ b b' : ResponseSymbol, symbols.readout () b ≠ symbols.readout () b' :=
  ⟨.zero,.one,by change ResponseSymbol.zero ≠ .one; decide⟩

private theorem _root_.PredictiveThermodynamic.post_error_cleanup.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.RationalMalformedCleanup.arena (∀ (st : PredictiveThermodynamic.PostControl) (input quotient shifts : List.{0} PredictiveThermodynamic.ResponseSymbol), Nonempty.{1} (@StateTransition.EvalsToInTime.{0} (Turing.FinTM2.Cfg PredictiveThermodynamic.postMachine) (Turing.FinTM2.step PredictiveThermodynamic.postMachine) (PredictiveThermodynamic.postCfg PredictiveThermodynamic.PostLabel.badInput st input quotient shifts (@List.nil.{0} PredictiveThermodynamic.ResponseSymbol)) (@Option.some.{0} (Turing.FinTM2.Cfg PredictiveThermodynamic.postMachine) (Turing.haltList PredictiveThermodynamic.postMachine (@List.cons.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.postMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.postMachine)) PredictiveThermodynamic.ResponseSymbol.zero (@List.nil.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.postMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.postMachine)))))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} PredictiveThermodynamic.ResponseSymbol input) (@List.length.{0} PredictiveThermodynamic.ResponseSymbol quotient)) (@List.length.{0} PredictiveThermodynamic.ResponseSymbol shifts)) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) Reg.D5.S0.Computability.RationalMalformedCleanup.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw,fun _ => post_error_cleanup⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.PredictiveThermodynamic.post_error_cleanup) (type_of% (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b))) (type_of% (ResponseSymbol)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "RationalMalformedCleanup") 0) "PredictiveThermodynamic") "post_error_cleanup") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "RationalMalformedCleanup") 0) "PredictiveThermodynamic") "post_error_cleanup") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := .law ⟨(arena)⟩,
  objectArena := .law ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.post_error_cleanup.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (PredictiveThermodynamic.post_error_cleanup.__primitive_realization) (@_root_.PredictiveThermodynamic.post_error_cleanup))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((symbols.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b)),
  variation := .evidence ⟨(variation)⟩ (by first | exact (variation) | exact ⟨_, _, (variation)⟩),
  sensitivity := .evidence ⟨(sensitivity)⟩ (by exact (sensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ResponseSymbol),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.RationalMalformedCleanup, declaration := `PredictiveThermodynamic.post_error_cleanup, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S0.Computability.RationalMalformedCleanup


noncomputable def Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.RationalMalformedCleanup.arena
noncomputable def Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"RationalMalformedCleanup\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"RationalMalformedCleanup\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.RationalMalformedCleanup.arena
noncomputable def Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"RationalMalformedCleanup\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"RationalMalformedCleanup\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.RationalMalformedCleanup, declaration := `Reg.D5.S0.Computability.RationalMalformedCleanup.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
