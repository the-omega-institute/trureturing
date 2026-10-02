import D5.S0.Computability.RationalResponseRefinement
import Reg.D5.S0.Computability.RationalPostprocessor
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.RationalResponseRefinement
open _root_.PredictiveThermodynamic _root_.Lax51Proofs.RamToTM Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype ResponseSymbol
  signature := cutSignature ResponseSymbol ResponseSymbol
  Law r := ∀ w,
    Nonempty (TM2OutputsInTime postMachine w
      (some ((binaryWord (totalPostOutput w)).map (r.readout ()))) (3*w.length+10)) ∧
    (∀ (xs : List Bool) (e : Nat), w = responseWord xs e →
      3 ∣ msbValue (true::xs) → (0 < e → Odd (msbValue (true::xs))) →
      msbValue (totalPostOutput w) =
        if e=0 then 2*(msbValue (true::xs)/3)
        else (msbValue (true::xs)/3)/2^(e-1)) ∧
    (¬ suitableResponse w → totalPostOutput w = [false]) ∧
    (totalPostOutput w = [false] ∨ ∃ xs : List Bool, totalPostOutput w = true::xs)

def symbols : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun _ => ResponseSymbol.one)

def sourceLaw : arena.Law symbols := by
  intro w
  change Nonempty (TM2OutputsInTime postMachine w
    (some ((binaryWord (totalPostOutput w)).map (fun b => b))) (3*w.length+10)) ∧ _
  rw [List.map_id']
  exact post_word_run w

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨bad⟩ := (law []).1
  obtain ⟨good⟩ := (post_word_run []).1
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

register_information_theorem _root_.PredictiveThermodynamic.post_word_run in arena
  readout via (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw,fun _ => post_word_run⟩
  variation variation sensitivity sensitivity
  escape from (ResponseSymbol) escape continues (open)

end Reg.D5.S0.Computability.RationalResponseRefinement
