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

register_information_theorem _root_.PredictiveThermodynamic.BinaryNames.dictionary_lookup_run in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => dictionary_lookup_run⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.BinaryNameDictionary
