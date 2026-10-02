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

register_information_theorem _root_.PredictiveThermodynamic.pre_error_cleanup in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => pre_error_cleanup⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.ClauseMalformedCleanup
