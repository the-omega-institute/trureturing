import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.PhysicalProtocol.ClauseOracleProtocol
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

theorem _root_._private.Reg.D5.S3.Quantum.Dynamics.PhysicalProtocol.ClauseOracleProtocol.0.PredictiveThermodynamic.one_query_run.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.ClauseOracleProtocol.arena (∀ (w : List.{0} Bool), @Exists.{1} (List.{0} PredictiveThermodynamic.ResponseSymbol) fun (r : List.{0} PredictiveThermodynamic.ResponseSymbol) => And (PredictiveThermodynamic.queryReply (PredictiveThermodynamic.preparedQuery w) r) (And (@LE.le.{0} Nat instLENat (@List.length.{0} PredictiveThermodynamic.ResponseSymbol r) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool w) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) (And (@Eq.{1} Nat (Lax51Proofs.RamToTM.msbValue (PredictiveThermodynamic.totalPostOutput r)) (@PredictiveThermodynamic.Physical.satisfyingCount (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)) (@Sigma.snd.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)))) (And (@Exists.{1} Nat fun (t : Nat) => And (@LE.le.{0} Nat instLENat t (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (@List.length.{0} Bool w) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) (@List.length.{0} Bool w))) (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71))))) (PredictiveThermodynamic.ProtocolRun (PredictiveThermodynamic.ProtocolCfg.pre (Turing.initList PredictiveThermodynamic.preMachine w)) (PredictiveThermodynamic.ProtocolCfg.halt (Turing.haltList PredictiveThermodynamic.postMachine (PredictiveThermodynamic.binaryWord (PredictiveThermodynamic.totalPostOutput r)))) t (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) (∀ (output : Turing.FinTM2.Cfg PredictiveThermodynamic.postMachine) (t asks : Nat), PredictiveThermodynamic.ProtocolRun (PredictiveThermodynamic.ProtocolCfg.pre (Turing.initList PredictiveThermodynamic.preMachine w)) (PredictiveThermodynamic.ProtocolCfg.halt output) t asks → @Eq.{1} Nat asks (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) Reg.D5.S0.Computability.ClauseOracleProtocol.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => one_query_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.PredictiveThermodynamic.one_query_run) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Quantum") "Dynamics") "PhysicalProtocol") "ClauseOracleProtocol") 0) "PredictiveThermodynamic") "one_query_run") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Quantum") "Dynamics") "PhysicalProtocol") "ClauseOracleProtocol") 0) "PredictiveThermodynamic") "one_query_run") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.one_query_run.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b => b)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.ClauseOracleProtocol
