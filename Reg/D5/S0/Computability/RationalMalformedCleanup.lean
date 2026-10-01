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

register_information_theorem _root_.PredictiveThermodynamic.post_error_cleanup in arena
  readout via (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw,fun _ => post_error_cleanup⟩
  variation variation sensitivity sensitivity
  escape from (ResponseSymbol) escape continues (open)

end Reg.D5.S0.Computability.RationalMalformedCleanup
