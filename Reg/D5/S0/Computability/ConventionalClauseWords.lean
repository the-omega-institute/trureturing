import D5.S0.Computability.ConventionalClauseWords
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ConventionalClauseWords
open _root_.PredictiveThermodynamic.Conventional Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law observer := ∀ w frame,
    Nonempty (EvalsToInTime parseMachine.step
      (parseCfg (some .scan) .bodyFirst 0 w [] [] [] frame)
      (some (parseCfg none .bodyFirst 0 w [] (decodedOccurrences w)
        [observer.readout () (readWord w).isSome] frame)) (4 * w.length + 5))

def symbols : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)
def erased : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := conventional_word_run

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨bad⟩ := law comparisonSource []
  obtain ⟨good⟩ := conventional_word_run comparisonSource []
  have traceReaches : ∀ (f : parseMachine.Cfg → Option parseMachine.Cfg) k a b,
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
  have same : parseCfg none .bodyFirst 0 comparisonSource []
      (decodedOccurrences comparisonSource) [true] [] =
      parseCfg none .bodyFirst 0 comparisonSource []
      (decodedOccurrences comparisonSource) [false] [] := by
    apply Part.mem_unique
    · exact mem_eval.mpr ⟨traceReaches _ good.steps _ _ good.evals_in_steps, rfl⟩
    · exact mem_eval.mpr ⟨traceReaches _ bad.steps _ _ bad.evals_in_steps, rfl⟩
  have flag := congrArg (fun c : parseMachine.Cfg => (c.stk .result).head?) same
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

register_information_theorem _root_.PredictiveThermodynamic.Conventional.conventional_word_run in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => conventional_word_run⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.ConventionalClauseWords
