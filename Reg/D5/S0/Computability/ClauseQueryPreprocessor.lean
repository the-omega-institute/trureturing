import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.ClauseQueryPreprocessor
import Reg.Support.PhysicalParserCells

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Reg.D5.S0.Computability.ClauseQueryPreprocessor

open _root_.PredictiveThermodynamic
open Turing StateTransition
open _root_.D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open LeanInformationAudit

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ {n : Nat} (F : UnaryFormula n) (width : ∀ c ∈ F, c.length ≤ 3),
    Nonempty (TM2OutputsInTime preMachine (sourceWord F)
      (some ((queryWord F).map (r.readout ())))
      (3 * ((sourceWord F).length + 3) ^ 2 + 7)) ∧
    (queryWord F).length = (sourceWord F).length + 6 + F.length * (n + 2)

def symbols : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => b)

def erased : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => false)

def sourceLaw : arena.Law symbols := by
  intro n F width
  change Nonempty (TM2OutputsInTime preMachine (sourceWord F)
    (some ((queryWord F).map (fun b => b)))
    (3 * ((sourceWord F).length + 3) ^ 2 + 7)) ∧ _
  rw [List.map_id']
  exact pre_query_run F width

def erased_fails : ¬arena.Law erased := by
  intro all
  obtain ⟨bad⟩ := (all (n := 0) [] (by simp)).1
  obtain ⟨good⟩ := (pre_query_run (n := 0) [] (by simp)).1
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
  have same : haltList preMachine (queryWord (n := 0) []) =
      haltList preMachine ((queryWord (n := 0) []).map (fun _ => false)) := by
    apply Part.mem_unique
    · exact mem_eval.mpr ⟨traceReaches _ good.steps _ _ good.evals_in_steps, rfl⟩
    · exact mem_eval.mpr ⟨traceReaches _ bad.steps _ _ bad.evals_in_steps, rfl⟩
  have output := congrArg (fun c : preMachine.Cfg => c.stk .output) same
  change queryWord (n := 0) [] =
    (queryWord (n := 0) []).map (fun _ => false) at output
  have impossible := congrArg List.head? output
  change some true = some false at impossible
  cases impossible

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

theorem _root_._private.Reg.D5.S0.Computability.ClauseQueryPreprocessor.0.PredictiveThermodynamic.pre_query_run.__primitive_realization : D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.{0, 0, 0} Reg.D5.S0.Computability.ClauseQueryPreprocessor.arena (∀ {n : Nat} (F : PredictiveThermodynamic.UnaryFormula n) (width : ∀ (c : Std.Sat.CNF.Clause.{0} (Fin n)), @Membership.mem.{0, 0} (Std.Sat.CNF.Clause.{0} (Fin n)) (PredictiveThermodynamic.UnaryFormula n) (@List.instMembership.{0} (Std.Sat.CNF.Clause.{0} (Fin n))) F c → @LE.le.{0} Nat instLENat (@List.length.{0} (Std.Sat.Literal.{0} (Fin n)) c) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))), And (Nonempty.{1} (Turing.TM2OutputsInTime PredictiveThermodynamic.preMachine (@PredictiveThermodynamic.sourceWord n F) (@Option.some.{0} (List.{0} (Turing.FinTM2.Γ PredictiveThermodynamic.preMachine (Turing.FinTM2.k₁ PredictiveThermodynamic.preMachine))) (@PredictiveThermodynamic.queryWord n F)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool (@PredictiveThermodynamic.sourceWord n F)) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) (@Eq.{1} Nat (@List.length.{0} Bool (@PredictiveThermodynamic.queryWord n F)) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} Bool (@PredictiveThermodynamic.sourceWord n F)) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} (Std.Sat.CNF.Clause.{0} (Fin n)) F) (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) Reg.D5.S0.Computability.ClauseQueryPreprocessor.symbols := by
    constructor
    exact ⟨fun _ => sourceLaw, fun _ => @pre_query_run⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.PredictiveThermodynamic.pre_query_run) (type_of% (arena)) (type_of% (arena)) (type_of% (@cutRealization Bool Bool instDecidableEqBool (fun b => b))) (type_of% (variation)) (type_of% (sensitivity)) (type_of% (Bool)) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClauseQueryPreprocessor") 0) "PredictiveThermodynamic") "pre_query_run") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S0") "Computability") "ClauseQueryPreprocessor") 0) "PredictiveThermodynamic") "pre_query_run") "__primitive_realization"),
  realizationSource := none,
  generated := false,
  arena := ⟨(arena)⟩,
  objectArena := ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (arena) ((symbols)) (symbols.toPrimitiveBundle) ⟨(PredictiveThermodynamic.pre_query_run.__primitive_realization)⟩,
  readout := some (@cutRealization Bool Bool instDecidableEqBool (fun b => b)),
  variation := some ⟨(variation)⟩,
  sensitivity := some ⟨(sensitivity)⟩,
  escapeFrom := some (Bool),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `backward.isDefEq.respectTransparency, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S0.Computability.ClauseQueryPreprocessor
