import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.BinaryNameComparison
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.BinaryNameComparison
open _root_.PredictiveThermodynamic.BinaryNames Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law observer := ∀ a b output frame,
    Nonempty (EvalsToInTime compareMachine.step
      (compareCfg (some .compare) ⟨none, none, true⟩ a b [] [] output frame)
      (some (compareCfg none ⟨none, none, true⟩ a b [] []
        (observer.readout () (decide (a = b)) :: output) frame))
      (2 * (a.length + b.length) + 4))

def symbols : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)
def erased : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := name_compare_run

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨bad⟩ := law [] [] [] []
  obtain ⟨good⟩ := name_compare_run [] [] [] []
  have traceReaches : ∀ (f : compareMachine.Cfg → Option compareMachine.Cfg) k a b,
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
  have same : compareCfg none ⟨none, none, true⟩ [] [] [] [] [true] [] =
      compareCfg none ⟨none, none, true⟩ [] [] [] [] [false] [] := by
    apply Part.mem_unique
    · exact mem_eval.mpr ⟨traceReaches _ good.steps _ _ good.evals_in_steps, rfl⟩
    · exact mem_eval.mpr ⟨traceReaches _ bad.steps _ _ bad.evals_in_steps, rfl⟩
  have flag := congrArg (fun c : compareMachine.Cfg => (c.stk .output).head?) same
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
    (type_of% (@_root_.PredictiveThermodynamic.BinaryNames.name_compare_run)) symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => name_compare_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.PredictiveThermodynamic.BinaryNames.name_compare_run) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% Bool) Unit := {
  unitName := `Reg.D5.S0.Computability.BinaryNameComparison.informationUnit,
  realizationName := `Reg.D5.S0.Computability.BinaryNameComparison.sourceBridge,
  realizationSource := none,
  generated := false,
  arena := .law ⟨arena⟩,
  objectArena := .law ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy arena symbols symbols.toPrimitiveBundle ⟨sourceBridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit sourceBridge (@_root_.PredictiveThermodynamic.BinaryNames.name_compare_run))⟩, statement := .evidence, bundle := .evidence },
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
    { name := `backward.isDefEq.respectTransparency, value := .bool false }] }

end Reg.D5.S0.Computability.BinaryNameComparison
