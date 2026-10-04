import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.PhysicalProtocol.PhysicalRationalResponse
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

private theorem _root_.PredictiveThermodynamic.physical_reply_run.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.PhysicalRationalResponse.arena (∀ {n : Nat} (F : PredictiveThermodynamic.Physical.Formula n), @Exists.{1} (List.{0} PredictiveThermodynamic.ResponseSymbol) fun (w : List.{0} PredictiveThermodynamic.ResponseSymbol) => And (@PredictiveThermodynamic.PhysicalReply n F w) (And (∀ (w' : List.{0} PredictiveThermodynamic.ResponseSymbol), @PredictiveThermodynamic.PhysicalReply n F w' → @Eq.{1} (List.{0} PredictiveThermodynamic.ResponseSymbol) w' w) (And (@LE.le.{0} Nat instLENat (@List.length.{0} PredictiveThermodynamic.ResponseSymbol w) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@List.length.{0} (Std.Sat.CNF.Clause.{0} (Fin n)) F)))) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) (And (PredictiveThermodynamic.suitableResponse w) (And (Nonempty.{1} (Turing.TM2OutputsInTime PredictiveThermodynamic.postMachine w (@Option.some.{0} (List.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.postMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.postMachine))) (PredictiveThermodynamic.binaryWord (PredictiveThermodynamic.totalPostOutput w))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@List.length.{0} PredictiveThermodynamic.ResponseSymbol w)) (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))) (@Eq.{1} Nat (Lax51Proofs.RamToTM.msbValue (PredictiveThermodynamic.totalPostOutput w)) (@PredictiveThermodynamic.Physical.satisfyingCount n F))))))) Reg.D5.S0.Computability.PhysicalRationalResponse.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => @physical_reply_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.PredictiveThermodynamic.physical_reply_run) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (ResponseSymbol)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Quantum") "Dynamics") "PhysicalProtocol") "PhysicalRationalResponse") 0) "PredictiveThermodynamic") "physical_reply_run") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Quantum") "Dynamics") "PhysicalProtocol") "PhysicalRationalResponse") 0) "PredictiveThermodynamic") "physical_reply_run") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.physical_reply_run.__primitive_realization)⟩,
  readout := some (@cutRealization ResponseSymbol ResponseSymbol
    (fun a b => instDecidableEqResponseSymbol a b) (fun b => b)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (ResponseSymbol),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.PhysicalRationalResponse
