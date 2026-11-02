import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket
import Reg.Support.DependentFamily

/-! # The original K2 innovation readout on arbitrary sample spaces -/

namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket
noncomputable section

abbrev Query := Σ _Ω : Type, Σ _u : Bool, ℕ

def signature : Signature where
  Params := Query
  State p := (c : Coord Bool) → p.1 → Value K2 c
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → Fin (p.2.2 + 2) → Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => innovations x p.2.1 p.2.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => false) (fun e => nomatch e)

theorem neighbor (u : Bool) : ∃ v, K2.Adj u v := by
  exact ⟨!u, by cases u <;> decide⟩

def observedNative (R : Realization signature) (ε : unitInterval) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
    (x : (c : Coord Bool) → Ω → Value K2 c)
    (_h : @OriginalLaw Bool Ω K2 inferInstance m P ε neighbor x) (u : Bool),
    (∀ (n : ℕ) (z : Fin (n + 2) → Bool) (b : Bool),
      0 < P.real {ω | bits x u (n + 1) ω = z} →
      P.real {ω | bits x u (n + 1) ω = z ∧ nvm x (n + 2) u ω = b} /
          P.real {ω | bits x u (n + 1) ω = z} =
        (1-(1-(ε : ℝ)) ^ 2) / 2 + (1-(ε : ℝ)) ^ 2 *
          (if b = z ⟨n, by omega⟩ then 1 else 0)) ∧
    (∀ N : ℕ, @HasLaw Ω (Fin (N + 2) → Bool) m _
      (R.readout () ⟨Ω, u, N⟩ x) (innovationLaw ε N) P) ∧
    (∀ t : ℕ, @HasLaw Ω ℝ m _ (W x u 2 t)
        ((binomial t (successProbability ε)).map (Nat.cast : ℕ → ℝ)) P ∧
      variance (W x u 2 t) P = (t : ℝ) * (1-(1-(ε : ℝ)) ^ 4) / 4)

def observedResult (R : Realization signature) (ε : unitInterval) (hε : 0 < (ε : ℝ)) (hε' : (ε : ℝ) < 1) : Prop :=
    ((1-(1-(ε : ℝ)) ^ 2) / 4 ≤ cOpt ε ∧ cOpt ε ≤ (1-(1-(ε : ℝ)) ^ 4) / 4 ∧
      (1-(1-(ε : ℝ)) ^ 4) / (1-(1-(ε : ℝ)) ^ 2) = 1 + (1-(ε : ℝ)) ^ 2 ∧
      1 + (1-(ε : ℝ)) ^ 2 < 2 ∧
      (2 * (ε : ℝ)-(ε : ℝ) ^ 2) / 4 ≤ cOpt ε ∧
      cOpt ε ≤ (4 * (ε : ℝ)-6 * (ε : ℝ) ^ 2 + 4 * (ε : ℝ) ^ 3-(ε : ℝ) ^ 4) / 4 ∧
      (ε : ℝ) / 4 ≤ cOpt ε ∧ cOpt ε ≤ (ε : ℝ)) ∧
    (Asymptotics.IsTheta (𝓝[>] (0 : ℝ)) cOpt (fun e => e) ∧
      (1 / 2 : ℝ) ≤ liminf (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ∧
      liminf (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ≤
        limsup (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ∧
      limsup (fun e : ℝ => cOpt e / e) (𝓝[>] 0) ≤ 1) ∧
    observedNative R ε

def arena : Arena where
  signature := signature
  Law R := ∀ ε hε hε', observedResult R ε hε hε'

private theorem bridge : (type_of% (@_root_.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket.result)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let e : unitInterval := ⟨1/2, by norm_num, by norm_num⟩
  let Ω := (c : Coord Bool) → Value K2 c
  let Q : Measure Ω := Measure.infinitePi (coordinateLaw K2 e neighbor)
  let x (c : Coord Bool) (ω : Ω) := ω c
  have hx : OriginalLaw K2 Q e neighbor x := {
    probability := inferInstance
    measurable := fun c _ => measurable_pi_apply c
    independent := (iIndepFun_infinitePi (X := fun _ a => a)
      (fun _ => measurable_id)).precomp Subtype.val_injective
    laws := fun c => (measurePreserving_eval_infinitePi
      (coordinateLaw K2 e neighbor) c.val).hasLaw }
  have hi := (((h e (by norm_num [e]) (by norm_num [e])).2.2
    Ω inferInstance Q x hx false).2.1 0)
  have heval : HasLaw (fun z : Fin 2 → Bool => z 0)
      (bernoulliMeasure true false fair) (innovationLaw e 0) := by
    simpa [innovationLaw, innovationParameter] using
      (measurePreserving_eval
        (fun i : Fin 2 => bernoulliMeasure true false (innovationParameter e i)) 0).hasLaw
  have he := (heval.comp hi).measureReal_eq (p := fun b => b = true)
    (measurableSet_singleton true)
  norm_num [actual, rejected, realize, Function.comp_def, fair,
    bernoulliMeasure_real_apply] at he

private def testAssignment (b : Bool) : (c : Coord Bool) → Unit → Value K2 c
  | .initial _, _ | .fresh _ _, _ => b
  | .refresh _ _, _ => false
  | .choice _ v, _ => ⟨!v, by cases v <;> decide⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨Unit, false, 0⟩, testAssignment true, testAssignment false, ?_⟩
  intro he
  have hb := congrArg (fun f => f () 0) he
  change true = false at hb
  cases hb

def source_registration : Registration arena (type_of% (@_root_.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket.result)) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @_root_.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket.result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (show j = i by cases i; cases j; rfl)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket.result) (Realization signature) Unit Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket.result.__information_unit
  realizationName := ``source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => innovations x p.2.1 p.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket
    definition := none
    coordinates := #[3, 8, 9]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.LagTwoOptimalBracket
