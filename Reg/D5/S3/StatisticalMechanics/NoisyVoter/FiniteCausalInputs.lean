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
  base : (c : Coord V) → Value G c
  u : V
  N : ℕ
  ω : Ω

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
  Law R := ∀ {V Ω : Type} {G : SimpleGraph V} [_hG : G.LocallyFinite]
    (base : (c : Coord V) → Value G c) (u : V) (N : ℕ),
    (∀ c ∈ historyInputs (G := G) u N, positive c) ∧
      ∀ (x : (c : Coord V) → Ω → Value G c) (ω : Ω),
        R.readout () ⟨V, Ω, G, base, u, N, ω⟩ x =
          decode base u N (restrictInputs x u N ω)

def testAssignment (b : Bool) : (c : Coord Bool) → Unit → Value (⊤ : SimpleGraph Bool) c
  | .initial _, _ | .fresh _ _, _ | .refresh _ _, _ => b
  | .choice _ v, _ => ⟨!v, by cases v <;> decide⟩

def testBase : (c : Coord Bool) → Value (⊤ : SimpleGraph Bool) c :=
  fun c => testAssignment false c ()

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h (V := Bool) (Ω := Unit) (G := ⊤) testBase true 0).2 (testAssignment true) ()
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
    refine ⟨⟨Bool, Unit, ⊤, testBase, true, 0, ()⟩,
      testAssignment true, testAssignment false, ?_⟩
    intro h
    have he := congrArg (fun f => (f 0).1) h
    change true = false at he
    cases he

def factorization_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
    definition := none
    coordinates := #[0, 1, 2, 4, 5, 6, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

structure LawQuery where
  V : Type
  Ω : Type
  G : SimpleGraph V
  u : V
  N : ℕ

abbrev lawAssignment (p : LawQuery) := (c : Coord p.V) → p.Ω → Value p.G c

def lawSignature : Signature where
  Params := LawQuery
  State := lawAssignment
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Ω → Fin (p.N+1) → Bool × Label p.V
  Anchor := Empty
  finiteAnchor := inferInstance

def lawActual : Realization lawSignature :=
  realize lawSignature (fun _ p x => history x p.u p.N) (fun e => nomatch e)

def lawRejected : Realization lawSignature :=
  realize lawSignature
    (fun _ p x ω n => (!(nvm x n.val p.u ω), source x n.val p.u ω))
    (fun e => nomatch e)

def lawArena : Arena where
  signature := lawSignature
  Law R := ∀ {V Ω Ω' : Type} {G : SimpleGraph V} [_hG : G.LocallyFinite]
    [_mΩ : MeasurableSpace Ω] [_mΩ' : MeasurableSpace Ω']
    (P : MeasureTheory.Measure Ω) (Q : MeasureTheory.Measure Ω')
    (x : (c : Coord V) → Ω → Value G c) (y : (c : Coord V) → Ω' → Value G c)
    (μ : (c : {c : Coord V // positive c}) → MeasureTheory.Measure (Value G c.val))
    (_hx : ∀ c, positive c → Measurable (x c))
    (_hy : ∀ c, positive c → Measurable (y c))
    (_hix : ProbabilityTheory.iIndepFun (fun c : {c : Coord V // positive c} => x c.val) P)
    (_hiy : ProbabilityTheory.iIndepFun (fun c : {c : Coord V // positive c} => y c.val) Q)
    (_hlx : ∀ c : {c : Coord V // positive c}, ProbabilityTheory.HasLaw (x c.val) (μ c) P)
    (_hly : ∀ c : {c : Coord V // positive c}, ProbabilityTheory.HasLaw (y c.val) (μ c) Q)
    (u : V) (N : ℕ),
      P.map (R.readout () ⟨V, Ω, G, u, N⟩ x) = Q.map (history y u N)

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
    rw [hd, ite_eq_left hi]
    symm
    apply Finset.prod_eq_one
    intro c hc
    rw [hd, ite_eq_left (h c hc)]
  · push Not at h
    obtain ⟨c, hc, hn⟩ := h
    have hi : () ∉ ⋂ c ∈ s, f c := by
      intro h
      exact hn ((Set.mem_iInter.mp (Set.mem_iInter.mp h c)) hc)
    rw [hd, ite_eq_right hi]
    symm
    apply Finset.prod_eq_zero hc
    rw [hd, ite_eq_right hn]

private theorem test_laws (c : {c : Coord Bool // positive c}) :
    ProbabilityTheory.HasLaw (testAssignment true c.val)
      (MeasureTheory.Measure.dirac (testAssignment true c.val ()))
      (MeasureTheory.Measure.dirac ()) where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := MeasureTheory.Measure.map_dirac' (measurable_of_finite _) ()

private theorem law_rejected_law : ¬ lawArena.Law lawRejected := by
  intro h
  have he := h (V := Bool) (Ω := Unit) (Ω' := Unit) (G := ⊤)
    (MeasureTheory.Measure.dirac ()) (MeasureTheory.Measure.dirac ())
    (testAssignment true) (testAssignment true)
    (fun c => MeasureTheory.Measure.dirac (testAssignment true c.val ()))
    (fun _ _ => measurable_of_finite _) (fun _ _ => measurable_of_finite _)
    test_independent test_independent test_laws test_laws true 0
  change (MeasureTheory.Measure.dirac ()).map
      (fun (_ : Unit) (n : Fin 1) =>
        (!(nvm (testAssignment true) n.val true ()), source (testAssignment true) n.val true ())) =
    (MeasureTheory.Measure.dirac ()).map (history (testAssignment true) true 0) at he
  rw [MeasureTheory.Measure.map_dirac' (measurable_of_finite _) (),
    MeasureTheory.Measure.map_dirac' (measurable_of_finite _) ()] at he
  have hb := congrArg (fun f => (f 0).1) (MeasureTheory.injective_dirac he)
  change false = true at hb
  exact Bool.false_ne_true hb

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
    refine ⟨⟨Bool, Unit, ⊤, true, 0⟩, testAssignment true, testAssignment false, ?_⟩
    intro h
    have he := congrArg (fun f => (f () 0).1) h
    change true = false at he
    cases he

def law_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
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
  readout := some (realize lawSignature (fun _ p x => history x p.u p.N)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
    definition := none
    coordinates := #[0, 1, 3, 18, 19]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.NoisyVoter.FiniteCausalInputs
