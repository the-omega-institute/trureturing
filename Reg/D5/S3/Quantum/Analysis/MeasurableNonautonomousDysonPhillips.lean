import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
import Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

/-! Full original telescopes with typed observational interventions. -/

open scoped Nat Topology NNReal
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis
open LeanInformationAudit

noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips

private def zeroSemigroup : Contraction PUnit.{u+1} :=
  _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup

abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

namespace Clock

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => fun _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {r t : ℝ} (hrt : r ≤ t) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Set.Icc r t)) (n : ℕ),
    IntervalIntegrable (fun s => g s * ((∫ z in r..s, g z)^n / n !)) volume r t ∧
    R.readout () () (∫ s in r..t, g s * ((∫ z in r..s, g z)^n / n !))
      ((∫ z in r..t, g z)^(n+1) / (n+1)!)

private theorem actual_law : arena.Law actual := @clock_moment

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (r := 0) (t := 0) le_rfl (g := fun _ => 0)
    (integrableOn_const measure_Icc_lt_top.ne) 0).2

def family : Registration arena (type_of% (@clock_moment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@clock_moment) (Realization scalarSignature) (Type) Unit where
  unitName := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.clock_momentUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.Clock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ a b => a = b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Clock

namespace Iterate

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => fun _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) {r H : ℝ} (hrH : r ≤ H)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc r H))
    (hgn : ∀ s ∈ Set.Icc r H, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s),
    ∀ (v : ℝ → E) (hv : ContinuousOn v (Set.Icc r H))
    (C : ℝ) (hvC : ∀ s ∈ Set.Icc r H, ‖v s‖ ≤ C),
    ∀ n : ℕ, ∀ t ∈ Set.Icc r H,
    R.readout () () ‖causalIterate S B r v n t‖ (C * ((∫ s in r..t, g s)^n / n !))

private theorem actual_law : arena.{u}.Law actual := @measurable_causal_iterate_bound.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h zeroSemigroup (fun _ => 0) (r := 0) (H := 0) le_rfl
    (fun _ => by simp) (fun _ => 0) (integrableOn_const measure_Icc_lt_top.ne)
    (fun _ _ => le_rfl) (fun _ _ => by simp)
    (fun _ => 0) continuous_const.continuousOn 0 (fun _ _ => by simp) 0 0 ⟨le_rfl,le_rfl⟩

def family : Registration arena.{u} (type_of% (@measurable_causal_iterate_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@measurable_causal_iterate_bound.{u}) (Realization scalarSignature) (Type) Unit where
  unitName := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.measurable_causal_iterate_boundUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.Iterate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Iterate

namespace Series

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a => Summable a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) {r H : ℝ} (hrH : r ≤ H)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc r H))
    (hgn : ∀ s ∈ Set.Icc r H, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s),
    ∀ {t : ℝ} (ht : t ∈ Set.Icc r H) (x : E),
    R.readout () () (fun n => ‖term S B n t r x‖) ∧
    HasSum (fun n => term S B n t r x) (sum S B t r x)

private theorem actual_law : arena.{u}.Law actual := @measurable_series.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h zeroSemigroup (fun _ => 0) (r := 0) (H := 0) le_rfl
    (fun _ => by simp) (fun _ => 0) (integrableOn_const measure_Icc_lt_top.ne)
    (fun _ _ => le_rfl) (fun _ _ => by simp) ⟨le_rfl,le_rfl⟩ 0).1

def family : Registration arena.{u} (type_of% (@measurable_series.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (fun _ => (0 : ℝ)), (fun _ => (1 : ℝ)), ?_⟩
    intro he
    have h : Summable (fun _ : ℕ => (1 : ℝ)) := Eq.mp he (by simp [actual, realize])
    simpa [summable_const_iff] using h

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@measurable_series.{u}) (Realization signature) (Type) Unit where
  unitName := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.measurable_seriesUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.Series.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => Summable a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℕ → ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Series

structure VectorSpace where
  E : Type u
  group : NormedAddCommGroup E
  space : NormedSpace ℂ E
attribute [instance] VectorSpace.group VectorSpace.space

namespace Residual

abbrev signature : Signature where
  Params := Type u
  State E := E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := E → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E) {r H : ℝ} (hrH : r ≤ H)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc r H))
    (hgn : ∀ s ∈ Set.Icc r H, 0 ≤ g s)
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s),
    ∀ {Y : ℝ → E} (hY : ContinuousOn Y (Set.Icc r H))
    (heq : ∀ t ∈ Set.Icc r H, Y t = causal S B r Y t),
    ∀ t ∈ Set.Icc r H,
    R.readout () E (Y t) 0

private theorem actual_law : arena.{u}.Law actual := @continuous_residual_eq_zero.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h zeroSemigroup (fun _ => 0) (r := 0) (H := 0) le_rfl
    (fun _ => by simp) (fun _ => 0) (integrableOn_const measure_Icc_lt_top.ne)
    (fun _ _ => le_rfl) (fun _ _ => by simp)
    (Y := fun _ => 0) continuous_const.continuousOn (fun _ _ => by simp [causal])
    0 ⟨le_rfl,le_rfl⟩

def family : Registration arena.{u} (type_of% (@continuous_residual_eq_zero.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} ℂ, (0 : ULift.{u} ℂ), (1 : ULift.{u} ℂ), ?_⟩
    intro he
    have hb : (1 : ULift.{u} ℂ) = 0 := Eq.mp (congrFun he 0) rfl
    exact one_ne_zero (congrArg ULift.down hb)

#print axioms family
end Residual

namespace Evolution

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ => fun _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E),
    ∃ Phi : (ℝ → E →L[ℂ] E) → ℝ → ℝ → E →L[ℂ] E,
    ∀ (B : ℝ → E →L[ℂ] E) (T : ℝ), 0 ≤ T →
    (∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T))) →
    ∀ (g : ℝ → ℝ), IntegrableOn g (Set.Icc 0 T) →
    (∀ s ∈ Set.Icc 0 T, 0 ≤ g s) → (∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) →
    (∀ r ∈ Set.Icc 0 T, ∀ v : ℝ → E, ContinuousOn v (Set.Icc r T) →
      ContinuousOn (causal S B r v) (Set.Icc r T) ∧
      ∀ t ∈ Set.Icc r T, IntervalIntegrable
        (fun s => S.action (t-s) (B s (v s))) volume r t) ∧
    (∀ n t r, (t,r) ∈ triangle T → ∀ x : E,
      IntervalIntegrable (fun s => S.action (t-s) (B s (term S B n s r x))) volume r t) ∧
    (∀ n t r, (t,r) ∈ triangle T → ∀ x : E,
      R.readout () () ‖term S B n t r x‖ ((∫ s in r..t, g s)^n / n ! * ‖x‖)) ∧
    (∀ t r, (t,r) ∈ triangle T → ∀ x : E,
      Summable (fun n => ‖term S B n t r x‖) ∧
      HasSum (fun n => term S B n t r x) (Phi B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => Phi B p.1 p.2 x) (triangle T)) ∧
    (∀ t r, (t,r) ∈ triangle T → ∀ x : E,
      Phi B t r x = S.action (t-r) x +
        ∫ s in r..t, S.action (t-s) (B s (Phi B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, Phi B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t-r) x +
        ∫ s in r..t, S.action (t-s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = Phi B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (Phi B t s).comp (Phi B s r) = Phi B t r) ∧
    (∀ t r, (t,r) ∈ triangle T → ‖Phi B t r‖ ≤ Real.exp (∫ s in r..t, g s)) ∧
    (∀ n r x, term S B (n+1) r r x = 0) ∧
    (∀ (Q : ℝ → E →L[ℂ] E) t r, (t,r) ∈ triangle T →
      Set.EqOn B Q (Set.Icc r t) → Phi B t r = Phi Q t r) ∧
    ((∀ x : E, ContinuousOn (fun s => B s x) (Set.Icc 0 T)) →
      ∀ t r, (t,r) ∈ triangle T →
      Phi B t r = StrongNonautonomousDysonPhillips.strongEvolution S B t r) ∧
    (∀ Z : E →L[ℂ] E, Set.EqOn B (fun _ => Z) (Set.Icc 0 T) →
      ∀ t r, (t,r) ∈ triangle T → ∀ x : E, Phi B t r x =
        DysonPhillipsPerturbation.dysonSum S.action Z (t-r) x) ∧
    (Set.EqOn B (fun _ => 0) (Set.Icc 0 T) → ∀ t r, (t,r) ∈ triangle T →
      Phi B t r = S.action (t-r))

private theorem actual_law : arena.{u}.Law actual := @measurable_evolution.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨Phi,hp⟩ := h zeroSemigroup
  have he := hp (fun _ => 0) 0 le_rfl (fun _ => by simp) (fun _ => 0)
    (integrableOn_const measure_Icc_lt_top.ne) (fun _ _ => le_rfl) (fun _ _ => by simp)
  exact he.2.2.1 0 0 0 ⟨le_rfl,le_rfl,le_rfl⟩ 0

def family : Registration arena.{u} (type_of% (@measurable_evolution.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@measurable_evolution.{u}) (Realization scalarSignature) (Type) Unit where
  unitName := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.measurable_evolutionUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips.Evolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (ℝ)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Evolution

structure EvaluationContext where
  α : Type v
  E : Type u
  measurable : MeasurableSpace α
  group : NormedAddCommGroup E
  space : NormedSpace ℂ E
attribute [instance] EvaluationContext.measurable EvaluationContext.group EvaluationContext.space

namespace Evaluation

abbrev signature : Signature where
  Params := EvaluationContext.{v,u}
  State p := p.α → p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Measure p.α → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f μ => AEStronglyMeasurable f μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {α : Type v} [MeasurableSpace α] {μ : Measure α}
    (B : α → E →L[ℂ] E)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) μ)
    {v : α → E} (hv : AEStronglyMeasurable v μ),
    R.readout () ⟨α,E,inferInstance,inferInstance,inferInstance⟩ (fun s => B s (v s)) μ

private theorem actual_law : arena.{u,v}.Law actual := @aestronglyMeasurable_evaluation.{u,v}

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (E := PUnit.{u+1}) (α := PUnit.{v+1}) (μ := 0) (fun _ => 0)
    (fun _ => aestronglyMeasurable_const) (v := fun _ => 0) aestronglyMeasurable_const

def family : Registration arena.{u,v} (type_of% (@aestronglyMeasurable_evaluation.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let p : signature.Params :=
      ⟨ULift Bool, ULift ℂ, ⊥, inferInstance, inferInstance⟩
    letI : MeasurableSpace p.α := p.measurable
    let jump : p.α → p.E := fun b => if b.down then 1 else 0
    refine ⟨p, (fun _ => 0), jump, ?_⟩
    intro he
    have hj : AEStronglyMeasurable jump Measure.count :=
      Eq.mp (congrFun he Measure.count) aestronglyMeasurable_const
    obtain ⟨f,hf,heq⟩ := hj
    have heq' : jump = f := funext (MeasureTheory.Measure.ae_count_iff.mp heq)
    have hstrong : StronglyMeasurable[⊥] jump := by
      rw [heq']; exact hf
    have hc : ∃ c, jump = fun _ => c := stronglyMeasurable_bot_iff.mp hstrong
    obtain ⟨c,hc⟩ := hc
    have h0 := congrFun hc (ULift.up false)
    have h1 := congrFun hc (ULift.up true)
    have he10 : (1 : p.E) = 0 := by simpa [jump] using h1.trans h0.symm
    exact one_ne_zero (congrArg ULift.down he10)

#print axioms family
end Evaluation

namespace Causal

abbrev signature : Signature where
  Params := VectorSpace.{u}
  State p := ℝ → p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f A => ContinuousOn f A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S : Contraction E) {B : ℝ → E →L[ℂ] E} {r H : ℝ}
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc r H)))
    {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc r H))
    (hBg : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ g s)
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r H)),
    R.readout () ⟨E,inferInstance,inferInstance⟩ (causal S B r v) (Set.Icc r H) ∧
    ∀ t ∈ Set.Icc r H, IntervalIntegrable
      (fun s => S.action (t-s) (B s (v s))) volume r t

private theorem actual_law : arena.{u}.Law actual := @causal_regular.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact (h zeroSemigroup (B := fun _ => 0) (r := 0) (H := 0)
    (fun _ => by simp) (g := fun _ => 0) (integrableOn_const measure_Icc_lt_top.ne)
    (fun _ _ => by simp) (v := fun _ => 0) continuous_const.continuousOn).1

def family : Registration arena.{u} (type_of% (@causal_regular.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    classical
    intro i
    let p : VectorSpace.{u} := ⟨ULift.{u} ℂ, inferInstance, inferInstance⟩
    let jump : ℝ → p.E := fun t => if t = 0 then 0 else 1
    refine ⟨p, (fun _ => 0), jump, ?_⟩
    intro he
    have hc : ContinuousOn jump Set.univ :=
      Eq.mp (congrFun he Set.univ) continuous_const.continuousOn
    have hl := (continuousOn_univ.mp hc).continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hj : ∀ n : ℕ, jump (1 / ((n : ℝ)+1)) = 1 := by
      intro n
      exact if_neg (by positivity)
    have hl' : Filter.Tendsto (fun _ : ℕ => (1 : ULift.{u} ℂ)) Filter.atTop (𝓝 0) := by
      simpa only [Function.comp_def, hj, jump, if_pos rfl] using hl
    have he10 : (1 : ULift.{u} ℂ) = 0 := tendsto_nhds_unique tendsto_const_nhds hl'
    exact one_ne_zero (congrArg ULift.down he10)

#print axioms family
end Causal

end Reg.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
