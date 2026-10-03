import LeanInformationAuditInterface.Contract.Registration
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

theorem _root_._private.Reg.D5.S0.Computability.ClausePreprocessorRefinement.0.PredictiveThermodynamic.pre_word_run.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.ClausePreprocessorRefinement.arena (∀ (w : List.{0} Bool), And (Nonempty.{1} (Turing.TM2OutputsInTime PredictiveThermodynamic.preMachine w (@Option.some.{0} (List.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.preMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.preMachine))) (PredictiveThermodynamic.preparedQuery w)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))))) (And (@Eq.{1} (Option.{0} (@Sigma.{0, 0} Nat fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n)) (PredictiveThermodynamic.ClauseCodec.readWord Bool.true (PredictiveThermodynamic.preparedQuery w)) (@Option.some.{0} (@Sigma.{0, 0} Nat fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w))) (And (@Eq.{1} (List.{0} Bool) (PredictiveThermodynamic.preparedQuery w) (@PredictiveThermodynamic.ClauseCodec.encodeWord (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)) Bool.true (@Sigma.snd.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)))) (And (∀ (c : Std.Sat.CNF.Clause.{0} (Fin (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)))), @Membership.mem.{0, 0} (Std.Sat.CNF.Clause.{0} (Fin (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)))) (PredictiveThermodynamic.UnaryFormula (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w))) (@List.instMembership.{0} (Std.Sat.CNF.Clause.{0} (Fin (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w))))) (@Sigma.snd.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)) c → @LE.le.{0} Nat instLENat (@List.length.{0} (Std.Sat.Literal.{0} (Fin (@Sigma.fst.{0, 0} Nat (fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n) (PredictiveThermodynamic.preparedFormula w)))) c) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (And (@LE.le.{0} Nat instLENat (@List.length.{0} Bool (PredictiveThermodynamic.preparedQuery w)) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))) (@Lax51Proofs.RamToTM.programPushBound PredictiveThermodynamic.PreStack PredictiveThermodynamic.PreLabel PredictiveThermodynamic.PreControl (fun (x : PredictiveThermodynamic.PreStack) => Bool) (@inferInstance.{1} (Fintype.{0} PredictiveThermodynamic.PreLabel) PredictiveThermodynamic.instFintypePreLabel) (Turing.FinTM2.m PredictiveThermodynamic.preMachine)))) (@Eq.{1} (Option.{0} (@Sigma.{0, 0} Nat fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n)) (PredictiveThermodynamic.ClauseCodec.readWord Bool.false w) (@Option.none.{0} (@Sigma.{0, 0} Nat fun (n : Nat) => PredictiveThermodynamic.UnaryFormula n)) → @Exists.{1} PredictiveThermodynamic.PreControl fun (st : PredictiveThermodynamic.PreControl) => @Exists.{1} (List.{0} Bool) fun (input : List.{0} Bool) => @Exists.{1} (List.{0} Bool) fun (header : List.{0} Bool) => @Exists.{1} (List.{0} Bool) fun (scratch : List.{0} Bool) => @Exists.{1} (List.{0} Bool) fun (query : List.{0} Bool) => Nonempty.{1} (@StateTransition.EvalsToInTime.{0} (Turing.FinTM2.Cfg PredictiveThermodynamic.preMachine) (Turing.FinTM2.step PredictiveThermodynamic.preMachine) (Turing.initList PredictiveThermodynamic.preMachine w) (@Option.some.{0} (Turing.FinTM2.Cfg PredictiveThermodynamic.preMachine) (PredictiveThermodynamic.preCfg PredictiveThermodynamic.PreLabel.badInput st input header scratch query (@List.nil.{0} Bool))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) (@List.length.{0} Bool w)) (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))))))))))) Reg.D5.S0.Computability.ClausePreprocessorRefinement.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => pre_word_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.PredictiveThermodynamic.pre_word_run) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClausePreprocessorRefinement") 0) "PredictiveThermodynamic") "pre_word_run") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClausePreprocessorRefinement") 0) "PredictiveThermodynamic") "pre_word_run") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.pre_word_run.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b => b)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.ClausePreprocessorRefinement
