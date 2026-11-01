import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
import Reg.Support.DependentFamily

/-! # Source-bound finite causal reconstruction -/

namespace Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.RepetitionVarianceLinear
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.AncestralSources
open _root_.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs

noncomputable section

structure Query where
  V : Type
  Ω : Type
  G : SimpleGraph V
  locallyFinite : G.LocallyFinite
  base : (c : Coord V) → Value G c
  u : V
  N : ℕ
  ω : Ω

attribute [instance] Query.locallyFinite

abbrev assignment (p : Query) := (c : Coord p.V) → p.Ω → Value p.G c

def signature : Signature where
  Params := Query
  State := assignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.N+1) → Bool × Label p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => history x p.u p.N p.ω) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p x n => (!(nvm x n.val p.u p.ω), source x n.val p.u p.ω))
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (V Ω : Type) (G : SimpleGraph V) [hG : G.LocallyFinite]
    (base : (c : Coord V) → Value G c) (u : V) (N : ℕ),
    (∀ c ∈ historyInputs (G := G) u N, positive c) ∧
      ∀ (x : (c : Coord V) → Ω → Value G c) (ω : Ω),
        R.readout () ⟨V, Ω, G, hG, base, u, N, ω⟩ x =
          decode base u N (restrictInputs x u N ω)

def testAssignment (b : Bool) : (c : Coord Bool) → Unit → Value (⊤ : SimpleGraph Bool) c
  | .initial _, _ | .fresh _ _, _ | .refresh _ _, _ => b
  | .choice _ v, _ => ⟨!v, by cases v <;> decide⟩

def testBase : (c : Coord Bool) → Value (⊤ : SimpleGraph Bool) c :=
  fun c => testAssignment false c ()

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h Bool Unit ⊤ testBase true 0).2 (testAssignment true) ()
  have hg := (finite_history_factorization testBase true 0).2 (testAssignment true) ()
  have he := congrArg (fun f => (f 0).1) (hb.trans hg.symm)
  change false = true at he
  exact Bool.false_ne_true he

def factorization_family : Registration arena (type_of% (@finite_history_factorization)) where
  actual := actual
  bridge := by
    constructor
    · intro h V Ω G hG base u N
      exact @h V Ω G hG base u N
    · intro h V Ω G hG base u N
      exact @h V Ω G hG base u N
  variation := ⟨@finite_history_factorization, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i by cases i; cases j; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨⟨Bool, Unit, ⊤, inferInstance, testBase, true, 0, ()⟩,
      testAssignment true, testAssignment false, ?_⟩
    intro h
    have he := congrArg (fun f => (f 0).1) h
    change true = false at he
    exact Bool.true_ne_false he

def factorization_registration : Contract.Registration
    (@finite_history_factorization) (Realization signature) (type_of% (@history)) Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs.finite_history_factorization.__information_unit
  realizationName := ``factorization_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨factorization_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => history x p.u p.N p.ω) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@history)
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

structure LawQuery where
  V : Type
  Ω : Type
  Ω' : Type
  G : SimpleGraph V
  locallyFinite : G.LocallyFinite
  measurableΩ : MeasurableSpace Ω
  measurableΩ' : MeasurableSpace Ω'
  P : @MeasureTheory.Measure Ω measurableΩ
  Q : @MeasureTheory.Measure Ω' measurableΩ'
  y : (c : Coord V) → Ω' → Value G c
  μ : (c : {c : Coord V // positive c}) → MeasureTheory.Measure (Value G c.val)
  u : V
  N : ℕ

abbrev lawAssignment (p : LawQuery) := (c : Coord p.V) → p.Ω → Value p.G c

def lawSignature : Signature where
  Params := LawQuery
  State := lawAssignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MeasureTheory.Measure (Fin (p.N+1) → Bool × Label p.V)
  Anchor := Empty
  finiteAnchor := inferInstance

def lawActual : Realization lawSignature :=
  realize lawSignature (fun _ p x => by
    letI := p.locallyFinite
    letI := p.measurableΩ
    exact p.P.map (history x p.u p.N)) (fun e => nomatch e)

def lawRejected : Realization lawSignature :=
  realize lawSignature (fun _ _ _ => 0) (fun e => nomatch e)

def lawArena : Arena where
  signature := lawSignature
  Law R := ∀ (V Ω Ω' : Type) (G : SimpleGraph V) [hG : G.LocallyFinite]
    [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    (P : MeasureTheory.Measure Ω) (Q : MeasureTheory.Measure Ω')
    (x : (c : Coord V) → Ω → Value G c) (y : (c : Coord V) → Ω' → Value G c)
    (μ : (c : {c : Coord V // positive c}) → MeasureTheory.Measure (Value G c.val))
    (hx : ∀ c, positive c → Measurable (x c))
    (hy : ∀ c, positive c → Measurable (y c))
    (hix : ProbabilityTheory.iIndepFun (fun c : {c : Coord V // positive c} => x c.val) P)
    (hiy : ProbabilityTheory.iIndepFun (fun c : {c : Coord V // positive c} => y c.val) Q)
    (hlx : ∀ c : {c : Coord V // positive c}, ProbabilityTheory.HasLaw (x c.val) (μ c) P)
    (hly : ∀ c : {c : Coord V // positive c}, ProbabilityTheory.HasLaw (y c.val) (μ c) Q)
    (u : V) (N : ℕ),
      R.readout () ⟨V, Ω, Ω', G, hG, mΩ, mΩ', P, Q, y, μ, u, N⟩ x =
        Q.map (history y u N)

theorem law_bridge : (type_of% (@history_law_of_positive_coordinate_laws)) ↔
    lawArena.Law lawActual := by
  constructor
  · intro h V Ω Ω' G hG mΩ mΩ' P Q x y μ hx hy hix hiy hlx hly u N
    exact @h V Ω Ω' G hG mΩ mΩ' P Q x y μ hx hy hix hiy hlx hly u N
  · intro h V Ω Ω' G hG mΩ mΩ' P Q x y μ hx hy hix hiy hlx hly u N
    exact @h V Ω Ω' G hG mΩ mΩ' P Q x y μ hx hy hix hiy hlx hly u N

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
