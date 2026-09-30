import D5.S0.Computability.ClauseOracleProtocol
import Reg.Support.BoundedRunSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ClauseOracleProtocol
open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.Physical
open _root_.Lax51Proofs.RamToTM Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law observer := ∀ w : List Bool, ∃ r : List ResponseSymbol,
    queryReply (preparedQuery w) r ∧
    r.length ≤ 2*(w.length+1)^2+w.length+5 ∧
    msbValue ((totalPostOutput r).map (observer.readout ())) =
      satisfyingCount (preparedFormula w).2 ∧
    (∃ t ≤ 16*w.length^2+50*w.length+71,
      ProtocolRun (.pre (initList preMachine w))
        (.halt (haltList postMachine (binaryWord (totalPostOutput r)))) t 1) ∧
    (∀ output t asks, ProtocolRun (.pre (initList preMachine w))
      (.halt output) t asks → asks = 1)

def symbols : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun b => b)
def erased : PrimitiveRealization (cutSignature Bool Bool) := cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro w
  obtain ⟨r,reply,bound,count,run,asks⟩ := one_query_run w
  refine ⟨r,reply,bound,?_,run,asks⟩
  change msbValue ((totalPostOutput r).map (fun b => b)) = _
  rw [List.map_id']
  exact count

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨r,_,_,count,_,_⟩ := law [false,false,false]
  change msbValue ((totalPostOutput r).map (fun _ => false)) = _ at count
  have allZero : ∀ bs : List Bool, msbValue (bs.map (fun _ => false)) = 0 := by
    intro bs
    change msbValueFrom 0 (bs.map (fun _ => false)) = 0
    induction bs with
    | nil => rfl
    | cons b bs ih => simpa [msbValueFrom] using ih
  rw [allZero] at count
  have form : preparedFormula [false,false,false] = ⟨0,[]⟩ := rfl
  rw [form] at count
  have oneCount : satisfyingCount ([] : Formula 0) = 1 := by
    simp [satisfyingCount,standardFormula,Std.Sat.CNF.eval,Assignment]
  change (0 : Nat) = satisfyingCount ([] : Formula 0) at count
  rw [oneCount] at count
  exact Nat.zero_ne_one count

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
  ⟨false,true,by change false ≠ true; decide⟩

register_information_theorem _root_.PredictiveThermodynamic.one_query_run in arena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => one_query_run⟩
  variation variation sensitivity sensitivity
  escape from (Bool) escape continues (open)

end Reg.D5.S0.Computability.ClauseOracleProtocol
