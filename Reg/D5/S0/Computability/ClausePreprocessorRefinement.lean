import D5.S0.Computability.ClausePreprocessorRefinement
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ClausePreprocessorRefinement

open _root_.PredictiveThermodynamic
open Turing StateTransition ClauseCodec
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ w : List Bool,
    Nonempty (TM2OutputsInTime preMachine w (some ((preparedQuery w).map (r.readout ())))
      ((4*w.length+20)*w.length+13)) ∧
    readWord true ((preparedQuery w).map (r.readout ())) = some (preparedFormula w) ∧
    (preparedQuery w).map (r.readout ()) = encodeWord true (preparedFormula w).2 ∧
    (∀ c ∈ (preparedFormula w).2, c.length ≤ 3) ∧
    ((preparedQuery w).map (r.readout ())).length ≤ ((4*w.length+20)*w.length+13) *
      (@Lax51Proofs.RamToTM.programPushBound PreStack PreLabel PreControl
        (fun _ => Bool) inferInstance preMachine.m) ∧
    (readWord false w = none → ∃ (st : PreControl) (input header scratch query : List Bool),
      Nonempty (EvalsToInTime preMachine.step (initList preMachine w)
        (some (preCfg .badInput st input header scratch query []))
        ((4*w.length+20)*w.length+13)))

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro w
  change
    Nonempty (TM2OutputsInTime preMachine w (some ((preparedQuery w).map (fun b => b)))
      ((4*w.length+20)*w.length+13)) ∧
    readWord true ((preparedQuery w).map (fun b => b)) = some (preparedFormula w) ∧
    (preparedQuery w).map (fun b => b) = encodeWord true (preparedFormula w).2 ∧
    (∀ c ∈ (preparedFormula w).2, c.length ≤ 3) ∧
    ((preparedQuery w).map (fun b => b)).length ≤ ((4*w.length+20)*w.length+13) *
      (@Lax51Proofs.RamToTM.programPushBound PreStack PreLabel PreControl
        (fun _ => Bool) inferInstance preMachine.m) ∧
    (readWord false w = none → ∃ (st : PreControl) (input header scratch query : List Bool),
      Nonempty (EvalsToInTime preMachine.step (initList preMachine w)
        (some (preCfg .badInput st input header scratch query []))
        ((4*w.length+20)*w.length+13)))
  simpa only [List.map_id'] using pre_word_run w

def erased_fails : ¬arena.Law erased := by
  intro all
  have bad := (all []).2.1
  change ClauseCodec.readWord true
    ((preparedQuery []).map (fun _ => false)) = some (preparedFormula []) at bad
  have impossible : ClauseCodec.readWord true
      ((preparedQuery []).map (fun _ => false)) = none := by decide
  rw [impossible] at bad
  cases bad

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
  ⟨false, true, by change false ≠ true; decide⟩

register_information_theorem _root_.PredictiveThermodynamic.pre_word_run in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => pre_word_run⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.ClausePreprocessorRefinement
