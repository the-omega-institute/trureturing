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
open scoped BigOperators

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

private theorem test_independent : ProbabilityTheory.iIndepFun
    (fun c : {c : Coord Bool // positive c} => testAssignment true c.val)
    (MeasureTheory.Measure.dirac ()) := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets _
  let f (c : {c : Coord Bool // positive c}) : Set Unit :=
    testAssignment true c.val ⁻¹' sets c
  change (MeasureTheory.Measure.dirac ()) (⋂ c ∈ s, f c) =
    ∏ c ∈ s, (MeasureTheory.Measure.dirac ()) (f c)
  have hd (A : Set Unit) : (MeasureTheory.Measure.dirac ()) A =
      if () ∈ A then 1 else 0 := by
    rw [MeasureTheory.Measure.dirac_apply' () (Set.toFinite A).measurableSet]
    simp only [Set.indicator_apply, Pi.one_apply]
  by_cases h : ∀ c ∈ s, () ∈ f c
  · have hi : () ∈ ⋂ c ∈ s, f c := by simpa using h
    rw [hd, if_pos hi]
    symm
    apply Finset.prod_eq_one
    intro c hc
    rw [hd, if_pos (h c hc)]
  · push_neg at h
    obtain ⟨c, hc, hn⟩ := h
    have hi : () ∉ ⋂ c ∈ s, f c := by
      intro h
      exact hn ((Set.mem_iInter.mp (Set.mem_iInter.mp h c)) hc)
    rw [hd, if_neg hi]
    symm
    apply Finset.prod_eq_zero hc
    rw [hd, if_neg hn]

private theorem test_laws (c : {c : Coord Bool // positive c}) :
    ProbabilityTheory.HasLaw (testAssignment true c.val)
      (MeasureTheory.Measure.dirac (testAssignment true c.val ()))
      (MeasureTheory.Measure.dirac ()) where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := MeasureTheory.Measure.map_dirac' (measurable_of_finite _) ()

private theorem law_rejected_law : ¬ lawArena.Law lawRejected := by
  intro h
  have he := h Bool Unit Unit ⊤
    (MeasureTheory.Measure.dirac ()) (MeasureTheory.Measure.dirac ())
    (testAssignment true) (testAssignment true)
    (fun c => MeasureTheory.Measure.dirac (testAssignment true c.val ()))
    (fun _ _ => measurable_of_finite _) (fun _ _ => measurable_of_finite _)
    test_independent test_independent test_laws test_laws true 0
  change (0 : MeasureTheory.Measure (Fin 1 → Bool × Label Bool)) =
    (MeasureTheory.Measure.dirac ()).map (history (testAssignment true) true 0) at he
  rw [MeasureTheory.Measure.map_dirac' (measurable_of_finite _) ()] at he
  have hu := congrArg (fun μ => μ Set.univ) he
  simpa using hu

def law_family : Registration lawArena (type_of% (@history_law_of_positive_coordinate_laws)) where
  actual := lawActual
  bridge := law_bridge
  variation := ⟨law_bridge.mp @history_law_of_positive_coordinate_laws,
    lawRejected, law_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lawRejected, ?_, rfl, law_rejected_law⟩
      intro j hji
      exact (hji (show j = i by cases i; cases j; rfl)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    refine ⟨⟨Bool, Unit, Unit, ⊤, inferInstance, inferInstance, inferInstance,
      MeasureTheory.Measure.dirac (), MeasureTheory.Measure.dirac (), testAssignment true,
      (fun c => MeasureTheory.Measure.dirac (testAssignment true c.val ())), true, 0⟩,
      testAssignment true, testAssignment false, ?_⟩
    intro h
    change (MeasureTheory.Measure.dirac ()).map (history (testAssignment true) true 0) =
      (MeasureTheory.Measure.dirac ()).map (history (testAssignment false) true 0) at h
    rw [MeasureTheory.Measure.map_dirac' (measurable_of_finite _) (),
      MeasureTheory.Measure.map_dirac' (measurable_of_finite _) ()] at h
    have he := congrArg (fun f => (f 0).1) (MeasureTheory.injective_dirac h)
    change true = false at he
    exact Bool.true_ne_false he

def law_registration : Contract.Registration
    (@history_law_of_positive_coordinate_laws) (Realization lawSignature)
    (type_of% (@history)) Unit where
  unitName := `D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs.history_law_of_positive_coordinate_laws.__information_unit
  realizationName := ``law_family
  realizationSource := none
  generated := false
  arena := .source ⟨lawArena⟩
  objectArena := .source ⟨lawArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lawArena ⟨law_family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lawSignature (fun _ p x => by
    letI := p.locallyFinite
    letI := p.measurableΩ
    exact p.P.map (history x p.u p.N)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@history)
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 18, 19]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
