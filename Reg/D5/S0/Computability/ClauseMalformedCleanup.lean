import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.ClauseMalformedCleanup
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ClauseMalformedCleanup

open _root_.PredictiveThermodynamic Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ st input header scratch query,
    Nonempty (EvalsToInTime preMachine.step
      (preCfg .badInput st input header scratch query [])
      (some (haltList preMachine (dummyQuery.map (r.readout ()))))
      (input.length + header.length + scratch.length + query.length + 5))

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro st input header scratch query
  exact pre_error_cleanup st input header scratch query

def erased_fails : ¬ arena.Law erased := by
  intro h
  obtain ⟨bad⟩ := h ⟨none, none, 0⟩ [] [] [] []
  obtain ⟨good⟩ := pre_error_cleanup ⟨none, none, 0⟩ [] [] [] []
  have traceReaches : ∀ (f : preMachine.Cfg → Option preMachine.Cfg) k a b,
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
  have same : haltList preMachine dummyQuery =
      haltList preMachine (dummyQuery.map (fun _ => false)) := by
    apply Part.mem_unique
    · exact mem_eval.mpr ⟨traceReaches _ good.steps _ _ good.evals_in_steps, rfl⟩
    · exact mem_eval.mpr ⟨traceReaches _ bad.steps _ _ bad.evals_in_steps, rfl⟩
  have output := congrArg (fun c : preMachine.Cfg => c.stk .output) same
  have head := congrArg List.head? output
  change some true = some false at head
  cases head

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

private theorem _root_.PredictiveThermodynamic.pre_error_cleanup.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.ClauseMalformedCleanup.arena (∀ (st : PredictiveThermodynamic.PreControl) (input header scratch query : List.{0} Bool), Nonempty.{1} (@StateTransition.EvalsToInTime.{0} (Turing.FinTM2.Cfg PredictiveThermodynamic.preMachine) (Turing.FinTM2.step PredictiveThermodynamic.preMachine) (PredictiveThermodynamic.preCfg PredictiveThermodynamic.PreLabel.badInput st input header scratch query (@List.nil.{0} Bool)) (@Option.some.{0} (Turing.FinTM2.Cfg PredictiveThermodynamic.preMachine) (Turing.haltList PredictiveThermodynamic.preMachine PredictiveThermodynamic.dummyQuery)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool input) (@List.length.{0} Bool header)) (@List.length.{0} Bool scratch)) (@List.length.{0} Bool query)) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))) Reg.D5.S0.Computability.ClauseMalformedCleanup.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => pre_error_cleanup⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.PredictiveThermodynamic.pre_error_cleanup) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% (Bool)) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClauseMalformedCleanup") 0) "PredictiveThermodynamic") "pre_error_cleanup") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClauseMalformedCleanup") 0) "PredictiveThermodynamic") "pre_error_cleanup") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := .law ⟨(arena)⟩,
  objectArena := .law ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.pre_error_cleanup.__primitive_realization)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (PredictiveThermodynamic.pre_error_cleanup.__primitive_realization) (@_root_.PredictiveThermodynamic.pre_error_cleanup))⟩, statement := .evidence, bundle := .evidence },
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
    { owner := `D5.S0.Computability.ClauseMalformedCleanup, declaration := `PredictiveThermodynamic.pre_error_cleanup, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalArenaFact, `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S0.Computability.ClauseMalformedCleanup


noncomputable def Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.ClauseMalformedCleanup.arena
noncomputable def Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseMalformedCleanup\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseMalformedCleanup\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena.{0, 0, 0} :=
  Reg.D5.S0.Computability.ClauseMalformedCleanup.arena
noncomputable def Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseMalformedCleanup\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S0\",\"Computability\",\"ClauseMalformedCleanup\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S0.Computability.ClauseMalformedCleanup, declaration := `Reg.D5.S0.Computability.ClauseMalformedCleanup.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
