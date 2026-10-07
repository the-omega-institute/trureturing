import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.BinaryNameDictionary
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.BinaryNameDictionary
open _root_.PredictiveThermodynamic.BinaryNames Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law observer := ∀ query names frame,
    Nonempty (EvalsToInTime dictionaryMachine.step
      (lookupCfg .start query [] [] [] frame (dictionaryStream names) [] [])
      (some (dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
        (compareStacks query [] [] [] [] frame) (dictionaryStream names) []
        (observer.readout () (decide (query ∈ names)) ::
          List.replicate (names.idxOf query) true)))
      ((2 * query.length + 12) * names.length +
        4 * (dictionaryStream names).length + 3))

def symbols : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)
def erased : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := dictionary_lookup_run

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨bad⟩ := law [true] [[true]] []
  obtain ⟨good⟩ := dictionary_lookup_run [true] [[true]] []
  have traceReaches : ∀ (f : dictionaryMachine.Cfg → Option dictionaryMachine.Cfg) k a b,
      (flip bind f)^[k] (some a) = some b → Reaches f a b := by
    intro f
    have noneStable : ∀ k, (flip bind f)^[k] none = none := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => simpa [Function.iterate_succ_apply, flip] using ih
    intro k
    induction k with
    | zero =>
      intro a b trace
      have he : a = b := Option.some.inj trace
      subst b
      exact Relation.ReflTransGen.refl
    | succ k ih =>
      intro a b trace
      simp only [Function.iterate_succ_apply, flip, Option.bind_some] at trace
      change (flip bind f)^[k] (f a) = some b at trace
      cases he : f a with
      | none => rw [he, noneStable] at trace; cases trace
      | some a' =>
        rw [he] at trace
        exact Relation.ReflTransGen.head he (ih a' b trace)
  have same : dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
      (compareStacks [true] [] [] [] [] []) (dictionaryStream [[true]]) [] [true] =
      dictionaryCfg none ⟨⟨none, none, true⟩, none, false⟩
      (compareStacks [true] [] [] [] [] []) (dictionaryStream [[true]]) [] [false] := by
    apply Part.mem_unique
    · exact mem_eval.mpr ⟨traceReaches _ good.steps _ _ good.evals_in_steps, rfl⟩
    · exact mem_eval.mpr ⟨traceReaches _ bad.steps _ _ bad.evals_in_steps, rfl⟩
  have flag := congrArg (fun c : dictionaryMachine.Cfg => (c.stk .index).head?) same
  change some true = some false at flag
  cases flag

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

private theorem sourceBridge : LegacyPrimitiveRealization arena
    (type_of% (@_root_.PredictiveThermodynamic.BinaryNames.dictionary_lookup_run)) symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => dictionary_lookup_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.PredictiveThermodynamic.BinaryNames.dictionary_lookup_run) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% Bool) Unit := {
  unitName := `Reg.D5.S0.Computability.BinaryNameDictionary.informationUnit,
  realizationName := `Reg.D5.S0.Computability.BinaryNameDictionary.sourceBridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨arena⟩,
  objectArena := .law ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy arena symbols symbols.toPrimitiveBundle ⟨sourceBridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit sourceBridge (@_root_.PredictiveThermodynamic.BinaryNames.dictionary_lookup_run))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change (symbols.toPrimitiveBundle).Nonempty; decide),
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b => b)),
  variation := .evidence ⟨variation⟩ (by first | exact variation | exact ⟨_, _, variation⟩),
  sensitivity := .evidence ⟨sensitivity⟩ (by exact sensitivity),
  partialSensitivity := none,
  escapeFrom := some Bool,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `backward.isDefEq.respectTransparency, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.BinaryNameDictionary, declaration := `PredictiveThermodynamic.BinaryNames.dictionary_lookup_run, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }

end Reg.D5.S0.Computability.BinaryNameDictionary


noncomputable def Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.BinaryNameDictionary.arena
noncomputable def Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"BinaryNameDictionary\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"BinaryNameDictionary\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.BinaryNameDictionary.arena
noncomputable def Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"BinaryNameDictionary\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"BinaryNameDictionary\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.BinaryNameDictionary, declaration := `Reg.D5.S0.Computability.BinaryNameDictionary.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
