import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
import Reg.Support.DependentFamily

open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum
open _root_.D5.S3.TotalVariation.Bhattacharyya
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Filter Finset
open scoped BigOperators ENNReal NNReal Topology ProbabilityTheory

noncomputable section
namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
universe u

namespace Localization
@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law O := ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
        (e d y : ℕ → Ω → ℝ)
    (he : StronglyAdapted ℱ e) (hei : ∀ n, Integrable (e n) μ)
    (he0 : ∀ n ω, 0 ≤ e n ω) (he1 : ∀ n ω, e n ω ≤ 1)
    (hd : ∀ n, StronglyMeasurable[ℱ (n + 1)] (d n))
    (hd2 : ∀ n, MemLp (d n) 2 μ)
    (hd0 : ∀ n, μ[d n | ℱ n] =ᵐ[μ] 0)
    (hdv : ∀ n, μ[fun ω => (d n ω) ^ 2 | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω)
    (hy : ∀ n, StronglyMeasurable[ℱ (n + 1)] (y n))
    (hyi : ∀ n, Integrable (y n) μ)
    (hy0 : ∀ n ω, 0 ≤ y n ω)
    (hyc : ∀ n, μ[y n | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω),
    (∀ K : ℕ, ∀ n : ℕ,
      (∫ ω, O.readout () () (∑ i ∈ range n, (energyCut e K i).indicator (d i) ω) ∂μ)
          ≤ 2 * (K + 1) ∧
      (∫ ω, (∑ i ∈ range n, (energyCut e K i).indicator (y i) ω) ∂μ)
          ≤ 2 * (K + 1)) ∧
    (∀ᵐ ω ∂μ, Summable (fun n => e n ω) →
      (∃ l : ℝ, Tendsto (fun n => ∑ i ∈ range n, d i ω) atTop (𝓝 l)) ∧
      Summable (fun n => y n ω))

private theorem actual_law : arena.{u}.Law actual := @common_energy_localization.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let F : Filtration ℕ (⊤ : MeasurableSpace (ULift.{u} Unit)) :=
    Filtration.const ℕ ⊤ le_rfl
  have hz : StronglyAdapted F (fun _ _ => (0 : ℝ)) := fun _ => stronglyMeasurable_const
  have h0 : ∀ n, μ[fun _ => (0 : ℝ) | F n] =ᵐ[μ] 0 := by
    intro n
    rw [show (fun _ : ULift.{u} Unit => (0 : ℝ)) = 0 from rfl, condExp_zero]
  have hv : ∀ n, μ[fun _ => (0 : ℝ) ^ 2 | F n] ≤ᵐ[μ] fun _ => 2 * (0 : ℝ) := by
    intro n
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    rw [show (fun _ : ULift.{u} Unit => (0 : ℝ)) = 0 from rfl, condExp_zero]
  have h' := h (μ := μ) (ℱ := F) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    hz (fun _ => integrable_zero _ _ _) (by simp) (by norm_num)
    (fun _ => stronglyMeasurable_const) (fun _ => memLp_const 0) h0 hv
    (fun _ => stronglyMeasurable_const) (fun _ => integrable_zero _ _ _)
    (by simp) (by simpa using hv)
  have hb := (h'.1 0 0).1
  dsimp only [rejected, realize, signature] at hb
  norm_num [μ] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.common_energy_localization.{u})
    (type_of% (realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e))) Unit Unit where
  unitName := `SequentialHellingerLocalization.common_energy_localization.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.Localization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Localization

namespace Product
@[reducible] def signature : Signature where
  Params := Σ Ω : Type u, Σ _r : ℕ → Ω → ℝ, Ω
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p n => ∏ i ∈ range n, p.2.1 i p.2.2) (fun e => Empty.elim e)
def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => Empty.elim e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law O := ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
        (e r : ℕ → Ω → ℝ)
    (he : StronglyAdapted ℱ e)
    (he0 : ∀ n ω, 0 ≤ e n ω) (he1 : ∀ n ω, e n ω ≤ 1)
    (hr : ∀ n, StronglyMeasurable[ℱ (n + 1)] (r n))
    (hr2 : ∀ n, MemLp (r n) 2 μ)
    (hr0 : ∀ n ω, 0 < r n ω)
    (hrmean : ∀ n, μ[r n | ℱ n] =ᵐ[μ] fun ω => 1 - e n ω)
    (hrsq : ∀ n, μ[fun ω => (r n ω - 1) ^ 2 | ℱ n] ≤ᵐ[μ] fun ω => 2 * e n ω),
    ∀ᵐ ω ∂μ, Summable (fun n => e n ω) →
      ∃ l : ℝ, 0 < l ∧ Tendsto (fun n => O.readout () ⟨Ω, r, ω⟩ n) atTop (𝓝 l)

private theorem actual_law : arena.{u}.Law actual := @finite_energy_positive_product.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  letI : MeasurableSpace (ULift.{u} Unit) := ⊤
  let μ : Measure (ULift.{u} Unit) := Measure.dirac (ULift.up ())
  let F : Filtration ℕ (⊤ : MeasurableSpace (ULift.{u} Unit)) :=
    Filtration.const ℕ ⊤ le_rfl
  have hz : StronglyAdapted F (fun _ _ => (0 : ℝ)) := fun _ => stronglyMeasurable_const
  have hm : ∀ n, μ[fun _ => (1 : ℝ) | F n] =ᵐ[μ] fun _ => 1 - (0 : ℝ) := by
    intro n
    simpa using (condExp_const (μ := μ) (F.le n) (1 : ℝ)).eventuallyEq
  have hv : ∀ n, μ[fun _ => ((1 : ℝ) - 1) ^ 2 | F n] ≤ᵐ[μ] fun _ => 2 * (0 : ℝ) := by
    intro n
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    rw [show (fun _ : ULift.{u} Unit => (0 : ℝ)) = 0 from rfl, condExp_zero]
  have h' := h (μ := μ) (ℱ := F) (fun _ _ => 0) (fun _ _ => 1)
    hz (by simp) (by norm_num) (fun _ => stronglyMeasurable_const)
    (fun _ => memLp_const 1) (by norm_num) hm hv
  obtain ⟨l, hl, ht⟩ := (h'.exists.choose_spec) (by simp)
  have he : (0 : ℝ) = l := tendsto_nhds_unique tendsto_const_nhds ht
  exact hl.ne he

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, fun _ _ => 2, ULift.up ()⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.finite_energy_positive_product.{u})
    (type_of% (realize signature.{u} actual.readout actual.anchor)) Unit Unit where
  unitName := `SequentialHellingerLocalization.finite_energy_positive_product.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.Product.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
    definition := none
    coordinates := #[0, 6, 15]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg", "body", "arg", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Product

namespace Likelihood
@[reducible] def signature : Signature where
  Params := Σ A : Type u, Σ _p : List A → A → ℝ, Σ _q : List A → A → ℝ, ℕ → A
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p n => ∏ i ∈ range n,
    p.2.2.1 (List.ofFn (fun j : Fin i => p.2.2.2 j)) (p.2.2.2 i) /
    p.2.1 (List.ofFn (fun j : Fin i => p.2.2.2 j)) (p.2.2.2 i)) (fun e => Empty.elim e)
def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => Empty.elim e)

@[reducible] def arena : Arena where
  signature := signature.{u}
  Law O := ∀ {A : Type u} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p q : List A → A → ℝ) (hp : NormalizedRows p) (hq : NormalizedRows q)
    (hp0 : ∀ h a, 0 < p h a) (hq0 : ∀ h a, 0 < q h a),
    let H := fun (n : ℕ) (x : ℕ → A) => List.ofFn (fun i : Fin n => x i)
    ∀ᵐ x ∂trajectoryLaw p hp,
      (Summable (fun n => 1 - bhattacharyya (p (H n x)) (q (H n x))) →
      ∃ l : ℝ, 0 < l ∧
        Tendsto (fun n => O.readout () ⟨A, p, q, x⟩ n) atTop (𝓝 l)) ∧
      (¬ Summable (fun n => 1 - bhattacharyya (p (H n x)) (q (H n x))) →
        Tendsto (fun n => ∏ i ∈ range n, q (H i x) (x i) / p (H i x) (x i)) atTop (𝓝 0))

private theorem actual_law : arena.{u}.Law actual := @trajectory_hellinger_likelihood_limits.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} Unit
  let p : List A → A → ℝ := fun _ _ => 1
  have hp : NormalizedRows p := by constructor <;> simp [p]
  have h' := h p p hp hp (by simp [p]) (by simp [p])
  have hρ h : bhattacharyya (p h) (p h) = 1 :=
    bhattacharyya_self _ ⟨hp.1 h, hp.2 h⟩
  letI : IsProbabilityMeasure (trajectoryLaw p hp) := by
    dsimp [trajectoryLaw]; infer_instance
  obtain ⟨l, hl, ht⟩ := (h'.exists.choose_spec).1 (by simp [hρ])
  have he : (0 : ℝ) = l := tendsto_nhds_unique tendsto_const_nhds ht
  exact hl.ne he

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, (fun _ _ => 1), (fun _ _ => 2), (fun _ => ULift.up ())⟩,
    0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.trajectory_hellinger_likelihood_limits.{u})
    (type_of% (realize signature.{u} actual.readout actual.anchor)) Unit Unit where
  unitName := `SequentialHellingerLocalization.trajectory_hellinger_likelihood_limits.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.Likelihood.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
    definition := none
    coordinates := #[0, 5, 6, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "body", "arg", "body", "arg", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Likelihood

namespace Dichotomy
@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => -Real.log x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law O := ∀ {A : Type u} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (hd : 2 ≤ Fintype.card A)
    (p q : List A → A → ℝ) (hp : NormalizedRows p) (hq : NormalizedRows q)
    (hp0 : ∀ h a, 0 < p h a) (hq0 : ∀ h a, 0 < q h a),
    let H := fun (n : ℕ) (x : ℕ → A) => List.ofFn (fun i : Fin n => x i)
    let C := {x : ℕ → A | (∑' n, ENNReal.ofReal
      (1 - bhattacharyya (p (H n x)) (q (H n x)))) < ∞}
    let J := fun (n : ℕ) (x : ℕ → A) => ∑ i ∈ range n,
      O.readout () () (bhattacharyya (p (H i x)) (q (H i x)))
    ((trajectoryLaw p hp).restrict C ≪ (trajectoryLaw q hq).restrict C ∧
      (trajectoryLaw q hq).restrict C ≪ (trajectoryLaw p hp).restrict C) ∧
    ((trajectoryLaw p hp).restrict Cᶜ ⟂ₘ (trajectoryLaw q hq).restrict Cᶜ) ∧
    ((∀ᵐ x ∂trajectoryLaw p hp, Tendsto (fun n => J n x) atTop atTop) →
      (∀ᵐ x ∂trajectoryLaw q hq, Tendsto (fun n => J n x) atTop atTop) →
      trajectoryLaw p hp ⟂ₘ trajectoryLaw q hq)

private theorem actual_law : arena.{u}.Law actual := @trajectory_hellinger_dichotomy.{u}
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let A := ULift.{u} (Fin 2)
  let p : List A → A → ℝ := fun _ _ => 1 / 2
  have hp : NormalizedRows p := by constructor <;> norm_num [p, A, Fintype.card_ulift]
  have hp0 : ∀ h a, 0 < p h a := by norm_num [p]
  have h' := h (by simp [A]) p p hp hp hp0 hp0
  have ht : ∀ᵐ x ∂trajectoryLaw p hp,
      Tendsto (fun n => ∑ _i ∈ range n, (1 : ℝ)) atTop atTop := by
    exact Filter.Eventually.of_forall fun _ => by simpa using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hs := h'.2.2 ht ht
  have he := (Measure.MutuallySingular.self_iff _).mp hs
  have hm := congrArg (fun μ : Measure (ℕ → A) => μ Set.univ) he
  letI : IsProbabilityMeasure (trajectoryLaw p hp) := by
    dsimp [trajectoryLaw]; infer_instance
  simpa using hm

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, Real.exp 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun _i => ⟨rejected,
    fun _j h => (h (Subsingleton.elim _ _)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.trajectory_hellinger_dichotomy.{u})
    (type_of% (realize signature (fun _ _ x => -Real.log x) (fun e => nomatch e))) Unit Unit where
  unitName := `SequentialHellingerLocalization.trajectory_hellinger_dichotomy.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization.Dichotomy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => -Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "body", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Dichotomy

end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SequentialHellingerLocalization
