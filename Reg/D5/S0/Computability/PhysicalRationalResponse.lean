import D5.S0.Computability.PhysicalRationalResponse
import Reg.D5.S0.Computability.RationalPostprocessor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.PhysicalRationalResponse

open _root_.PredictiveThermodynamic _root_.PredictiveThermodynamic.Physical
open _root_.Lax51Proofs.RamToTM Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype ResponseSymbol
  signature := cutSignature ResponseSymbol ResponseSymbol
  Law r := ∀ (n : Nat) (F : Formula n),
    ∃ w : List ResponseSymbol, PhysicalReply F w ∧
      (∀ w', PhysicalReply F w' → w' = w) ∧
      w.length ≤ n + 2*((n+1)*F.length) + 5 ∧
      suitableResponse w ∧
      Nonempty (TM2OutputsInTime postMachine w
        (some ((binaryWord (totalPostOutput w)).map (r.readout ())))
        (3*w.length+10)) ∧
      msbValue (totalPostOutput w) = satisfyingCount F

def symbols : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature ResponseSymbol ResponseSymbol) :=
  cutRealization (fun _ => ResponseSymbol.zero)

def sourceLaw : arena.Law symbols := by
  intro n F
  obtain ⟨w,reply,unique,bound,suitable,run,count⟩ := physical_reply_run F
  refine ⟨w,reply,unique,bound,suitable,?_,count⟩
  change Nonempty (TM2OutputsInTime postMachine w
    (some ((binaryWord (totalPostOutput w)).map (fun b => b))) (3*w.length+10))
  rw [List.map_id']
  exact run

def erased_fails : ¬ arena.Law erased := by
  intro law
  obtain ⟨w,reply,unique,_,_,⟨good⟩,count⟩ := physical_reply_run ([] : Formula 0)
  obtain ⟨v,reply',_,_,_,⟨bad⟩,_⟩ := law 0 []
  have sameWord := unique v reply'
  subst v
  have same := _root_.Reg.D5.S0.Computability.RationalPostprocessor.terminal_unique
    postMachine.step good bad (by rfl) (by rfl)
  have output := congrArg (fun c : postMachine.Cfg => c.stk .output) same
  change binaryWord (totalPostOutput w) =
    (binaryWord (totalPostOutput w)).map (fun _ => ResponseSymbol.zero) at output
  let parse : ResponseSymbol → Bool := fun s => isSymbol .one (some s)
  have roundtrip : ∀ b, parse (bitSymbol b) = b := by
    intro b; cases b <;> rfl
  have bits := congrArg (List.map parse) output
  have composed : (fun b => parse (bitSymbol b)) = id := funext roundtrip
  simp only [binaryWord, List.map_map, Function.comp_def, composed, List.map_id,
    List.map_id', roundtrip, show parse ResponseSymbol.zero = false from rfl] at bits
  have allZero : ∀ bs : List Bool, msbValue (bs.map (fun _ => false)) = 0 := by
    intro bs
    change msbValueFrom 0 (bs.map (fun _ => false)) = 0
    induction bs with
    | nil => rfl
    | cons b bs ih => simpa [msbValueFrom] using ih
  have zeroValue : msbValue (totalPostOutput w) = 0 := by
    rw [bits]
    exact allZero _
  have oneCount : satisfyingCount ([] : Formula 0) = 1 := by
    simp [satisfyingCount,standardFormula,Std.Sat.CNF.eval,Assignment]
  omega

def variation : FiniteLawVariation arena := ⟨symbols, erased, sourceLaw, erased_fails⟩

def sensitivity : FiniteSlotSensitivity arena := by
  constructor
  · intro i
    obtain ⟨r, r', hr, hr'⟩ := variation
    refine ⟨r, r', ?_, ?_, ⟨fun _ => hr', fun _ => hr⟩⟩
    · intro j hj; cases i; cases j; exact (hj rfl).elim
    · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def dependence : ∃ b b' : ResponseSymbol, symbols.readout () b ≠ symbols.readout () b' :=
  ⟨.zero, .one, by change ResponseSymbol.zero ≠ ResponseSymbol.one; decide⟩

register_information_theorem _root_.PredictiveThermodynamic.physical_reply_run in arena
  readout via (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b))
  primitives symbols.toPrimitiveBundle
  realization inline (symbols) := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => @physical_reply_run⟩
  variation variation sensitivity sensitivity
  escape from (ResponseSymbol) escape continues (open)

end Reg.D5.S0.Computability.PhysicalRationalResponse
