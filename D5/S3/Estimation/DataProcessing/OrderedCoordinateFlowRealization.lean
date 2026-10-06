/- GID: D5/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/OrderedCoordinateFlowRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic]
   utility: none
   digest: Complete archive conditional caps yield ordered flows realized by staged independent innovations. -/

import D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Independence.Basic

open MeasureTheory Finset Function
open scoped BigOperators ENNReal Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Estimation.DataProcessing.OrderedCoordinateFlowRealization
open D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter
variable {I : Type*} {X : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]

/-- Averaging the scalar conditional cap over an event measurable in the complete
pre-result archive works on an arbitrary underlying probability space. -/
theorem archive_event_cap {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : MeasurableSpace Ω) (hG : G ≤ m)
    (s z : Set Ω) (hs : MeasurableSet[G] s) (hz : MeasurableSet[m] z) (r : ℝ)
    (hcap : ∀ᵐ ω ∂μ, ω ∈ s →
      (μ[z.indicator (fun _ => (1 : ℝ)) | G]) ω ≤ r) :
    μ.real (s ∩ z) ≤ r * μ.real s := by
  have hi : Integrable (z.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator hz
  have he : (∫ ω in s, z.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real (s ∩ z) := by
    rw [setIntegral_indicator hz, setIntegral_const]
    simp [Set.inter_comm]
  calc
    μ.real (s ∩ z) = ∫ ω in s, (μ[z.indicator (fun _ => (1 : ℝ)) | G]) ω ∂μ := by
      rw [setIntegral_condExp hG hi hs, he]
    _ ≤ ∫ _ in s, r ∂μ :=
      setIntegral_mono_on_ae (integrable_condExp.integrableOn)
        (integrable_const r).integrableOn (hG s hs) hcap
    _ = r * μ.real s := by simp [setIntegral_const, mul_comm]

local instance scheduleMeasurableSpace (k : ℕ) :
    MeasurableSpace (ScheduleTable (X := X) k) := ⊤
local instance resultMeasurableSpace (k : ℕ) :
    MeasurableSpace (ResultTable (X := X) k) := ⊤
local instance scheduleMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (ScheduleTable (X := X) k) := ⟨fun _ => trivial⟩
local instance resultMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (ResultTable (X := X) k) := ⟨fun _ => trivial⟩

abbrev TableTrace (k : ℕ) := (t : Fin k) →
  ScheduleTable (X := X) t.val × ResultTable (X := X) t.val
abbrev Sample := Unit × TableTrace (X := X) (Fintype.card I)

/-- The actual probability-space law of the independent finite innovation blocks. -/
def innovationLaw {r : I → ℝ} (p : Flow (X := X) r) :
    Measure (Unit × ((t : Fin (Fintype.card I)) →
      ScheduleTable (X := X) t.val × ResultTable (X := X) t.val)) :=
  FiniteHistoryConditionalExpectation.historyLaw (fun _ : Unit => 1)
    (innovationKernel p) (Fintype.card I)

/-- On the independently sampled table space, the recursive interpreter realizes all
node, selection and result masses, and the exact terminal named-assignment projection. -/
theorem table_trace_realization {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) :
    IsProbabilityMeasure (innovationLaw p) ∧
    (∀ k (hk : k ≤ Fintype.card I) (h : History X k),
      (innovationLaw p).real {ω | interpret k
        (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) hk ω.2) = h} = p.mass k h) ∧
    (∀ k (hk : k < Fintype.card I) (h : History X k) (i : Unread h),
      (innovationLaw p).real {ω | ∃ x, interpret (k+1)
        (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) (Nat.succ_le_of_lt hk) ω.2) =
          append h i x} = p.select k h i) ∧
    (∀ k (hk : k < Fintype.card I) (h : History X k) (i : Unread h) (x : X i.val),
      (innovationLaw p).real {ω | interpret (k+1)
        (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) (Nat.succ_le_of_lt hk) ω.2) =
          append h i x} = p.result k h i x) ∧
    (∀ v : (i : I) → X i, (innovationLaw p).real
      {ω | terminalAssignment (interpret (Fintype.card I) ω.2) = v} =
        terminalProjection p v) := by
  classical
  have hn (k : ℕ) (hk : k < Fintype.card I) :
      (∀ (j : Unit) w z, 0 ≤ innovationKernel p k j w z) ∧
        ∀ (j : Unit) w, ∑ z, innovationKernel p k j w z = 1 := by
    obtain ⟨ha, hb⟩ := table_laws p hr hk
    constructor
    · intro j w z
      exact mul_nonneg (ha.1 z.1) (hb.1 z.2)
    · intro j w
      change (∑ z : ScheduleTable (X := X) k × ResultTable (X := X) k,
        scheduleDensity p k z.1 * resultDensity p k z.2) = 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, hb.2, mul_one]
      exact ha.2
  have supplier := FiniteHistoryConditionalExpectation.history_law_conditional_expectation
    (fun _ : Unit => (1 : ℝ)) ⟨fun _ => zero_le_one, by simp⟩
    (innovationKernel p) (Fintype.card I) hn
  have hμ : IsProbabilityMeasure (innovationLaw p) := supplier.1
  letI := hμ
  have nodes (k : ℕ) (hk : k ≤ Fintype.card I) (h : History X k) :
      (innovationLaw p).real {ω | interpret k
        (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) hk ω.2) = h} = p.mass k h := by
    rw [← integral_indicator_one ((Set.toFinite _).measurableSet)]
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply]
    change (∫ ω, (if interpret k
      (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) hk ω.2) = h then (1 : ℝ) else 0)
        ∂innovationLaw p) = p.mass k h
    unfold innovationLaw
    rw [supplier.2.1 k hk (fun _ w => if interpret k w = h then 1 else 0)]
    simp only [Fintype.sum_unique, one_mul]
    exact interpret_mass p hr k hk h
  have results (k : ℕ) (hk : k < Fintype.card I) (h : History X k)
      (i : Unread h) (x : X i.val) :
      (innovationLaw p).real {ω | interpret (k+1)
        (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) (Nat.succ_le_of_lt hk) ω.2) =
          append h i x} = p.result k h i x := by
    rw [nodes, p.child_mass]
  refine ⟨hμ, nodes, ?_, results, ?_⟩
  · intro k hk h i
    let e (x : X i.val) : Set (Sample (X := X)) := {ω | interpret (k+1)
      (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) (Nat.succ_le_of_lt hk) ω.2) =
        append h i x}
    have hd : Pairwise (Disjoint on e) := by
      intro x y hxy
      apply Set.disjoint_left.mpr
      intro ω hx hy
      have hh : append h i x = append h i y := hx.symm.trans hy
      have hi : (⟨h, i, x⟩ : Σ h : History X k, Σ i : Unread h, X i.val) =
          ⟨h, i, y⟩ := append_injective k hh
      exact hxy (eq_of_heq (Sigma.mk.inj (Sigma.mk.inj hi).2.eq).2)
    have he : {ω | ∃ x, interpret (k+1)
      (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) (Nat.succ_le_of_lt hk) ω.2) =
        append h i x} = ⋃ x, e x := by ext ω; simp [e]
    rw [he, measureReal_iUnion_fintype hd (fun _ => (Set.toFinite _).measurableSet)]
    simp_rw [show ∀ x, (innovationLaw p).real (e x) = p.result k h i x from results k hk h i]
    exact p.result_sum k h i
  · intro v
    let e (h : History X (Fintype.card I)) : Set (Sample (X := X)) :=
      {ω | interpret (Fintype.card I) ω.2 = h ∧ terminalAssignment h = v}
    have hd : Pairwise (Disjoint on e) := by
      intro h g hne
      apply Set.disjoint_left.mpr
      intro ω hh hg
      exact hne (hh.1.symm.trans hg.1)
    have he : {ω | terminalAssignment (interpret (Fintype.card I) ω.2) = v} =
        ⋃ h, e h := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, e]
      exact ⟨fun hv => ⟨_, rfl, hv⟩, fun ⟨h, hh, hv⟩ => hh.symm ▸ hv⟩
    rw [he, measureReal_iUnion_fintype hd (fun _ => (Set.toFinite _).measurableSet)]
    unfold terminalProjection
    apply Finset.sum_congr rfl
    intro h _
    by_cases hv : terminalAssignment h = v
    · simp only [hv, if_true]
      have heh : e h = {ω | interpret (Fintype.card I)
          (FiniteHistoryConditionalExpectation.readPrefix (Z := fun t =>
          ScheduleTable (X := X) t × ResultTable (X := X) t) le_rfl ω.2) = h} := by
        ext ω
        have hp (w : TableTrace (X := X) (Fintype.card I)) :
            FiniteHistoryConditionalExpectation.readPrefix
              (Z := fun t => ScheduleTable (X := X) t × ResultTable (X := X) t)
              (t := Fintype.card I) (n := Fintype.card I) le_rfl w = w := rfl
        simp only [e, hv, and_true, hp]
      rw [heh, nodes]
    · simp [e, hv]

private theorem unread_lt {k : ℕ} (h : History X k) (i : Unread h) :
    k < Fintype.card I := by
  have hc := Fintype.card_le_of_injective (fun j => ((append h i
    (Classical.choice (inferInstance : Nonempty (X i.val)))).val j).1)
      (append h i (Classical.choice (inferInstance : Nonempty (X i.val)))).property
  simp only [Fintype.card_fin] at hc
  omega

abbrev Selection (k : ℕ) := Σ h : History X k, Unread h
abbrev Step (k : ℕ) := Σ h : History X k, Σ i : Unread h, X i.val

local instance historyMeasurableSpace (k : ℕ) : MeasurableSpace (History X k) := ⊤
local instance selectionMeasurableSpace (k : ℕ) :
    MeasurableSpace (Selection (X := X) k) := ⊤
local instance stepMeasurableSpace (k : ℕ) : MeasurableSpace (Step (X := X) k) := ⊤
local instance historyMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (History X k) := ⟨fun _ => trivial⟩
local instance selectionMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (Selection (X := X) k) := ⟨fun _ => trivial⟩
local instance stepMeasurableSingleton (k : ℕ) :
    MeasurableSingletonClass (Step (X := X) k) := ⟨fun _ => trivial⟩

/-- Forget the just-obtained result, retaining the actual history and selected coordinate. -/
def forgetResult {k : ℕ} (e : Step (X := X) k) : Selection (X := X) k := ⟨e.1, e.2.1⟩

private theorem selection_fiber {k : ℕ} (e : Step (X := X) k)
    (h : History X k) (i : Unread h) :
    forgetResult e = ⟨h, i⟩ ↔ ∃ x, e = ⟨h, i, x⟩ := by
  rcases e with ⟨g, j, y⟩
  constructor
  · intro he
    have hg : g = h := congrArg Sigma.fst he
    subst g
    have hj : j = i := eq_of_heq (Sigma.mk.inj he).2
    subst j
    exact ⟨y, rfl⟩
  · rintro ⟨x, hx⟩
    exact congrArg forgetResult hx

/-- The coordinate-history projection of an actual process on an arbitrary probability
space. F and G are its supplied complete archives, and may contain arbitrary extra
records. The cap is tested on G, on each known history/selection branch. -/
structure ArchivePath (r : I → ℝ) {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) where
  F : ℕ → MeasurableSpace Ω
  G : ℕ → MeasurableSpace Ω
  F_le_G : ∀ k, F k ≤ G k
  G_le_next : ∀ k, G k ≤ F (k+1)
  F_le : ∀ k, F k ≤ m
  history : (k : ℕ) → k ≤ Fintype.card I → Ω → History X k
  step : (k : ℕ) → k < Fintype.card I → Ω → Step (X := X) k
  history_measurable : ∀ k hk, Measurable[F k] (history k hk)
  selection_measurable : ∀ k hk, Measurable[G k] (fun ω => forgetResult (step k hk ω))
  step_measurable : ∀ k hk, Measurable[F (k+1)] (step k hk)
  parent_history : ∀ k hk ω, (step k hk ω).1 = history k (Nat.le_of_lt hk) ω
  child_history : ∀ k hk ω,
    history (k+1) (Nat.succ_le_of_lt hk) ω = extensionEquiv k (step k hk ω)
  conditional_cap : ∀ k hk (h : History X k) (i : Unread h) (x : X i.val),
    ∀ᵐ ω ∂μ, forgetResult (step k hk ω) = ⟨h, i⟩ →
      (μ[({ω | step k hk ω = ⟨h, i, x⟩}).indicator (fun _ => (1 : ℝ)) | G k]) ω ≤ r i.val

namespace ArchivePath
variable {r : I → ℝ} {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] (A : ArchivePath (X := X) r μ)

def nodeEvent (k : ℕ) (h : History X k) : Set Ω :=
  {ω | ∃ hk : k ≤ Fintype.card I, A.history k hk ω = h}
def selectEvent {k : ℕ} (h : History X k) (i : Unread h) : Set Ω :=
  {ω | forgetResult (A.step k (unread_lt h i) ω) = ⟨h, i⟩}
def resultEvent {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) : Set Ω :=
  {ω | A.step k (unread_lt h i) ω = ⟨h, i, x⟩}

private theorem node_measurable (k : ℕ) (h : History X k) :
    MeasurableSet[m] (A.nodeEvent k h) := by
  by_cases hk : k ≤ Fintype.card I
  · have he : A.nodeEvent k h = (A.history k hk) ⁻¹' {h} := by ext ω; simp [nodeEvent, hk]
    rw [he]
    exact (A.history_measurable k hk).mono (A.F_le k) le_rfl (measurableSet_singleton h)
  · have he : A.nodeEvent k h = ∅ := by ext ω; simp [nodeEvent, hk]
    rw [he]; exact MeasurableSet.empty

private theorem select_measurable {k : ℕ} (h : History X k) (i : Unread h) :
    MeasurableSet[A.G k] (A.selectEvent h i) :=
  by
    simpa only [selectEvent, Set.preimage, Set.mem_singleton_iff] using
      A.selection_measurable k (unread_lt h i)
        (measurableSet_singleton (⟨h, i⟩ : Selection (X := X) k))

private theorem result_measurable {k : ℕ} (h : History X k) (i : Unread h) (x : X i.val) :
    MeasurableSet[m] (A.resultEvent h i x) :=
  by
    simpa only [resultEvent, Set.preimage, Set.mem_singleton_iff] using
      (A.step_measurable k (unread_lt h i)).mono (A.F_le (k+1)) le_rfl
        (measurableSet_singleton (⟨h, i, x⟩ : Step (X := X) k))

/-- Actual probabilities of history, selection and result events form a feasible flow. -/
def toFlow : Flow (X := X) r where
  mass k h := μ.real (A.nodeEvent k h)
  select _ h i := μ.real (A.selectEvent h i)
  result _ h i x := μ.real (A.resultEvent h i x)
  mass_nonneg _ _ := measureReal_nonneg
  select_nonneg _ _ _ := measureReal_nonneg
  result_nonneg _ _ _ _ := measureReal_nonneg
  root_mass := by
    have he : A.nodeEvent 0 root = Set.univ := by
      ext ω
      simp only [nodeEvent, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨Nat.zero_le _, Subsingleton.elim _ _⟩
    rw [he]
    simp [Measure.real]
  select_sum k hk h := by
    let e (i : Unread h) := A.selectEvent h i
    have hd : Pairwise (Disjoint on e) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro ω hi hj
      have he : (⟨h, i⟩ : Selection (X := X) k) = ⟨h, j⟩ := hi.symm.trans hj
      exact hij (eq_of_heq (Sigma.mk.inj he).2)
    have he : (⋃ i, e i) = A.nodeEvent k h := by
      ext ω
      simp only [Set.mem_iUnion, e, selectEvent, nodeEvent, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨Nat.le_of_lt hk, by
          rw [← A.parent_history k hk ω]
          exact congrArg Sigma.fst hi⟩
      · rintro ⟨hn, hh⟩
        generalize hqe : A.step k hk ω = q
        have hq : q.1 = h := by
          rw [← hqe, A.parent_history k hk ω]
          exact hh
        rcases q with ⟨g, i, x⟩
        dsimp at hq
        subst g
        exact ⟨i, congrArg forgetResult hqe⟩
    rw [← measureReal_iUnion_fintype hd (fun i =>
      ((A.G_le_next k).trans (A.F_le (k+1))) _
        (A.select_measurable h i)), he]
  result_sum k h i := by
    let e (x : X i.val) := A.resultEvent h i x
    have hd : Pairwise (Disjoint on e) := by
      intro x y hxy
      apply Set.disjoint_left.mpr
      intro ω hx hy
      have he : (⟨h, i, x⟩ : Step (X := X) k) = ⟨h, i, y⟩ := hx.symm.trans hy
      exact hxy (eq_of_heq (Sigma.mk.inj (Sigma.mk.inj he).2.eq).2)
    have he : (⋃ x, e x) = A.selectEvent h i := by
      ext ω
      simp only [Set.mem_iUnion, e, resultEvent, selectEvent, Set.mem_setOf_eq]
      exact (selection_fiber _ h i).symm
    rw [← measureReal_iUnion_fintype hd (fun x => A.result_measurable h i x), he]
  result_cap k h i x := by
    have hG : A.G k ≤ m := (A.G_le_next k).trans (A.F_le (k+1))
    have he : A.selectEvent h i ∩ A.resultEvent h i x = A.resultEvent h i x := by
      ext ω
      simp only [Set.mem_inter_iff, selectEvent, resultEvent, Set.mem_setOf_eq, and_iff_right_iff_imp]
      intro hx
      exact congrArg forgetResult hx
    have hc := archive_event_cap μ (A.G k) hG (A.selectEvent h i) (A.resultEvent h i x)
      (A.select_measurable h i) (A.result_measurable h i x) (r i.val)
        (A.conditional_cap k (unread_lt h i) h i x)
    rwa [he] at hc
  child_mass k h i x := by
    have hn := Nat.succ_le_of_lt (unread_lt h i)
    have he : A.nodeEvent (k+1) (append h i x) = A.resultEvent h i x := by
      ext ω
      simp only [nodeEvent, resultEvent, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hn', hh⟩
        rw [A.child_history k (unread_lt h i) ω] at hh
        exact (extensionEquiv k).injective hh
      · intro hh
        refine ⟨hn, ?_⟩
        rw [A.child_history k (unread_lt h i) ω, hh]
        rfl
    rw [he]

/-- The actual terminal law is defined from the named terminal assignment, independently
of any flow or flow projection. -/
def terminalLaw (v : (i : I) → X i) : ℝ :=
  μ.real {ω | terminalAssignment (A.history (Fintype.card I) le_rfl ω) = v}

/-- All full ordered-history fibers recover the original actual terminal law. -/
theorem terminalLaw_projection : terminalProjection A.toFlow = A.terminalLaw := by
  classical
  funext v
  let e (h : History X (Fintype.card I)) : Set Ω :=
    {ω | A.history (Fintype.card I) le_rfl ω = h ∧ terminalAssignment h = v}
  have hd : Pairwise (Disjoint on e) := by
    intro h g hne
    apply Set.disjoint_left.mpr
    intro ω hh hg
    exact hne (hh.1.symm.trans hg.1)
  have hem (h : History X (Fintype.card I)) : MeasurableSet[m] (e h) := by
    by_cases hv : terminalAssignment h = v
    · have he : e h = A.nodeEvent (Fintype.card I) h := by
        ext ω
        simp [e, nodeEvent, hv]
      rw [he]
      exact A.node_measurable _ h
    · have he : e h = ∅ := by ext ω; simp [e, hv]
      rw [he]
      exact MeasurableSet.empty
  have he : {ω | terminalAssignment (A.history (Fintype.card I) le_rfl ω) = v} =
      ⋃ h, e h := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, e]
    exact ⟨fun hv => ⟨_, rfl, hv⟩, fun ⟨h, hh, hv⟩ => hh.symm ▸ hv⟩
  unfold terminalLaw
  rw [he, measureReal_iUnion_fintype hd hem]
  unfold terminalProjection
  apply Finset.sum_congr rfl
  intro h _
  by_cases hv : terminalAssignment h = v
  · simp only [hv, if_true]
    change μ.real (A.nodeEvent _ h) = μ.real (e h)
    congr 1
    ext ω
    simp [nodeEvent, e, hv]
  · simp [e, hv]

end ArchivePath

/-- Complete archive of all preceding innovation blocks. -/
def beforeTables (k : ℕ) (hk : k ≤ Fintype.card I) (ω : Sample (X := X)) :
    TableTrace (X := X) k :=
  FiniteHistoryConditionalExpectation.readPrefix
    (Z := fun t => ScheduleTable (X := X) t × ResultTable (X := X) t) hk ω.2

/-- The new block is independent of previous blocks; its two components are separate
scheduling and result innovations. -/
def currentBlock (k : ℕ) (hk : k < Fintype.card I) (ω : Sample (X := X)) :
    ScheduleTable (X := X) k × ResultTable (X := X) k := ω.2 ⟨k, hk⟩

/-- Full pre-result disclosure: every past block and the entire new scheduling table. -/
def scheduleArchive (k : ℕ) (hk : k < Fintype.card I) :
    MeasurableSpace (Sample (X := X)) :=
  MeasurableSpace.comap
    (fun ω => (beforeTables k (Nat.le_of_lt hk) ω, (currentBlock k hk ω).1)) inferInstance

private theorem next_block_integral {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (hk : k < Fintype.card I)
    (f : TableTrace (X := X) k → ScheduleTable (X := X) k →
      ResultTable (X := X) k → ℝ) :
    (∫ ω, f (beforeTables k (Nat.le_of_lt hk) ω)
      (currentBlock k hk ω).1 (currentBlock k hk ω).2 ∂innovationLaw p) =
    ∑ w : TableTrace (X := X) k,
      FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w *
        ∑ a, scheduleDensity p k a * ∑ b, resultDensity p k b * f w a b := by
  have hn (t : ℕ) (ht : t < Fintype.card I) :
      (∀ (j : Unit) w z, 0 ≤ innovationKernel p t j w z) ∧
        ∀ (j : Unit) w, ∑ z, innovationKernel p t j w z = 1 := by
    obtain ⟨ha, hb⟩ := table_laws p hr ht
    refine ⟨fun _ _ z => mul_nonneg (ha.1 _) (hb.1 _), fun _ _ => ?_⟩
    change (∑ z : ScheduleTable (X := X) t × ResultTable (X := X) t,
      scheduleDensity p t z.1 * resultDensity p t z.2) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hb.2, mul_one]
    exact ha.2
  have he := (FiniteHistoryConditionalExpectation.history_law_conditional_expectation
    (fun _ : Unit => (1 : ℝ)) ⟨fun _ => zero_le_one, by simp⟩
    (innovationKernel p) (Fintype.card I) hn).2.1 (k+1) (Nat.succ_le_of_lt hk)
      (fun _ w => f (Fin.init w) (w (Fin.last k)).1 (w (Fin.last k)).2)
  change (∫ ω, f (beforeTables k (Nat.le_of_lt hk) ω)
      (currentBlock k hk ω).1 (currentBlock k hk ω).2 ∂innovationLaw p) = _ at he
  simp only [Fintype.sum_unique, one_mul] at he
  rw [he, ← (Fin.snocEquiv (fun t : Fin (k+1) =>
    ScheduleTable (X := X) t.val × ResultTable (X := X) t.val)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk,
    FiniteHistoryConditionalExpectation.likelihood, Fin.init_snoc, Fin.snoc_last,
    innovationKernel]
  have hu : (default : Unit) = () := Subsingleton.elim _ _
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_assoc, hu]
  apply Fintype.sum_congr
  intro w
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rfl

/-- After disclosing every previous table and the entire current scheduling table,
the child event still has its prescribed conditional result row. -/
theorem conditional_child_given_schedule {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    (k : ℕ) (hk : k < Fintype.card I)
    (h : History X k) (i : Unread h) (x : X i.val) :
    (innovationLaw p)[
      (fun ω => if interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) =
        append h i x then (1 : ℝ) else 0) | scheduleArchive k hk] =ᵐ[innovationLaw p]
    fun ω => if interpret k (beforeTables k (Nat.le_of_lt hk) ω) = h ∧
      (currentBlock k hk ω).1 h = i then resultRow p h i x else 0 := by
  classical
  haveI := (table_trace_realization p hr).1
  let cut (ω : Sample (X := X)) :=
    (beforeTables k (Nat.le_of_lt hk) ω, (currentBlock k hk ω).1)
  let g (c : TableTrace (X := X) k × ScheduleTable (X := X) k) : ℝ :=
    if interpret k c.1 = h ∧ c.2 h = i then resultRow p h i x else 0
  have hm : scheduleArchive (X := X) k hk ≤ (inferInstance : MeasurableSpace (Sample (X := X))) :=
    (measurable_of_finite cut).comap_le
  have hfiber (ω : Sample (X := X)) :
      interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) = append h i x ↔
        interpret k (beforeTables k (Nat.le_of_lt hk) ω) = h ∧
          (currentBlock k hk ω).1 h = i ∧ (currentBlock k hk ω).2 h i = x := by
    have he := interpret_snoc_fiber k (beforeTables k (Nat.le_of_lt hk) ω)
      (currentBlock k hk ω) h i x
    have hp : Fin.snoc (beforeTables k (Nat.le_of_lt hk) ω) (currentBlock k hk ω) =
        beforeTables (k+1) (Nat.succ_le_of_lt hk) ω := by
      change Fin.snoc (Fin.init (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω))
        ((beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) (Fin.last k)) = _
      exact Fin.snoc_init_self _
    rwa [hp] at he
  change (innovationLaw p)[_ | scheduleArchive k hk] =ᵐ[innovationLaw p] fun ω => g (cut ω)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm Integrable.of_finite
  · intro s hs hsμ
    exact Integrable.of_finite
  · intro s hs hsμ
    have hsm := hm s hs
    obtain ⟨S, hS, rfl⟩ := hs
    rw [← integral_indicator hsm, ← integral_indicator hsm]
    simp only [Set.indicator, Set.mem_preimage, hfiber]
    change (∫ ω, (if cut ω ∈ S then g (cut ω) else 0) ∂innovationLaw p) =
      ∫ ω, (if cut ω ∈ S then
        (if interpret k (beforeTables k (Nat.le_of_lt hk) ω) = h ∧
          (currentBlock k hk ω).1 h = i ∧ (currentBlock k hk ω).2 h i = x
          then (1 : ℝ) else 0) else 0) ∂innovationLaw p
    rw [next_block_integral p hr k hk (fun w a _ => if (w, a) ∈ S then g (w, a) else 0),
      next_block_integral p hr k hk (fun w a b => if (w, a) ∈ S then
        (if interpret k w = h ∧ a h = i ∧ b h i = x then (1 : ℝ) else 0) else 0)]
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    have hb := (table_laws p hr hk).2.2
    by_cases hs : (w, a) ∈ S
    · by_cases hw : interpret k w = h ∧ a h = i
      · have hmarg := result_table_marginal p hr h i (fun y => if y = x then 1 else 0)
        simpa [hs, g, hw, hw.1, hw.2, ← Finset.sum_mul, hb] using hmarg.symm
      · have hz (b : ResultTable (X := X) k) :
            ¬(interpret k w = h ∧ a h = i ∧ b h i = x) :=
          fun hh => hw ⟨hh.1, hh.2.1⟩
        simp [hs, g, hw, hz]
    · simp [hs]
  · exact StronglyMeasurable.aestronglyMeasurable
      (((measurable_of_finite g).comp (comap_measurable cut)).stronglyMeasurable)

/-- The canonical archive process reveals the scheduling table before using the
separate result table, retaining every completed innovation block afterward. -/
def canonicalArchivePath {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) :
    ArchivePath (X := X) r (innovationLaw p) := by
  classical
  haveI := (table_trace_realization p hr).1
  let F (k : ℕ) : MeasurableSpace (Sample (X := X)) :=
    if hk : k ≤ Fintype.card I then
      MeasurableSpace.comap (beforeTables (X := X) k hk) inferInstance else inferInstance
  let G (k : ℕ) : MeasurableSpace (Sample (X := X)) :=
    if hk : k < Fintype.card I then scheduleArchive k hk else F (k+1)
  let H (k : ℕ) (hk : k ≤ Fintype.card I) (ω : Sample (X := X)) : History X k :=
    interpret k (beforeTables k hk ω)
  let nextStep (k : ℕ) (hk : k < Fintype.card I) (ω : Sample (X := X)) : Step (X := X) k :=
    (extensionEquiv k).symm (H (k+1) (Nat.succ_le_of_lt hk) ω)
  have he (k : ℕ) (hk : k < Fintype.card I) (ω : Sample (X := X)) :
      nextStep k hk ω = ⟨H k (Nat.le_of_lt hk) ω,
        (currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω),
        (currentBlock k hk ω).2 (H k (Nat.le_of_lt hk) ω)
          ((currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω))⟩ := by
    have hp : Fin.snoc (beforeTables k (Nat.le_of_lt hk) ω) (currentBlock k hk ω) =
        beforeTables (k+1) (Nat.succ_le_of_lt hk) ω := by
      change Fin.snoc (Fin.init (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω))
        ((beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) (Fin.last k)) = _
      exact Fin.snoc_init_self _
    have hs := (interpret_snoc_fiber k (beforeTables k (Nat.le_of_lt hk) ω)
      (currentBlock k hk ω) (H k (Nat.le_of_lt hk) ω)
      ((currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω))
      ((currentBlock k hk ω).2 (H k (Nat.le_of_lt hk) ω)
        ((currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω)))).mpr ⟨rfl, rfl, rfl⟩
    rw [hp] at hs
    change (extensionEquiv k).symm _ = _
    rw [show H (k+1) (Nat.succ_le_of_lt hk) ω = _ from hs]
    exact (extensionEquiv k).symm_apply_apply
      ⟨H k (Nat.le_of_lt hk) ω, (currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω),
        (currentBlock k hk ω).2 (H k (Nat.le_of_lt hk) ω)
          ((currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω))⟩
  refine {
    F := F
    G := G
    history := H
    step := nextStep
    F_le_G := ?_
    G_le_next := ?_
    F_le := ?_
    history_measurable := ?_
    selection_measurable := ?_
    step_measurable := ?_
    parent_history := ?_
    child_history := ?_
    conditional_cap := ?_ }
  · intro k
    change F k ≤ G k
    by_cases hk : k < Fintype.card I
    · dsimp only [F, G]
      rw [dif_pos (Nat.le_of_lt hk), dif_pos hk]
      exact MeasurableSpace.comap_le_comap_of_eq_comp Prod.fst
        (measurable_of_finite _) rfl
    · dsimp only [G]
      rw [dif_neg hk]
      have hn : ¬ k+1 ≤ Fintype.card I := by omega
      dsimp only [F]
      rw [dif_neg hn]
      split
      · exact (measurable_of_finite _).comap_le
      · exact le_rfl
  · intro k
    change G k ≤ F (k+1)
    by_cases hk : k < Fintype.card I
    · dsimp only [G, F]
      rw [dif_pos hk, dif_pos (Nat.succ_le_of_lt hk)]
      exact MeasurableSpace.comap_le_comap_of_eq_comp
        (fun w : TableTrace (X := X) (k+1) => (Fin.init w, (w (Fin.last k)).1))
          (measurable_of_finite _) rfl
    · dsimp only [G]
      rw [dif_neg hk]
  · intro k
    change F k ≤ _
    dsimp only [F]
    split
    · exact (measurable_of_finite _).comap_le
    · exact le_rfl
  · intro k hk
    change Measurable[F k] (H k hk)
    rw [show F k = MeasurableSpace.comap (beforeTables k hk) inferInstance from dif_pos hk]
    change Measurable[MeasurableSpace.comap (beforeTables k hk) inferInstance]
      (fun ω => interpret k (beforeTables k hk ω))
    exact (measurable_of_finite (interpret k)).comp (comap_measurable _)
  · intro k hk
    change Measurable[G k] (fun ω => forgetResult (nextStep k hk ω))
    rw [show G k = scheduleArchive k hk from dif_pos hk]
    have hfn : (fun ω => forgetResult (nextStep k hk ω)) =
        fun ω => (fun c : TableTrace (X := X) k × ScheduleTable (X := X) k =>
          (⟨interpret k c.1, c.2 (interpret k c.1)⟩ : Selection (X := X) k))
            (beforeTables k (Nat.le_of_lt hk) ω, (currentBlock k hk ω).1) := by
      funext ω
      rw [he]
      rfl
    rw [hfn]
    exact (measurable_of_finite (fun c : TableTrace (X := X) k × ScheduleTable (X := X) k =>
      (⟨interpret k c.1, c.2 (interpret k c.1)⟩ : Selection (X := X) k))).comp
        (comap_measurable (fun ω : Sample (X := X) =>
          (beforeTables k (Nat.le_of_lt hk) ω, (currentBlock k hk ω).1)))
  · intro k hk
    change Measurable[F (k+1)] (nextStep k hk)
    rw [show F (k+1) = MeasurableSpace.comap
      (beforeTables (k+1) (Nat.succ_le_of_lt hk)) inferInstance from
        dif_pos (Nat.succ_le_of_lt hk)]
    change Measurable[MeasurableSpace.comap
      (beforeTables (k+1) (Nat.succ_le_of_lt hk)) inferInstance]
      (fun ω => (extensionEquiv k).symm
        (interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω)))
    exact (measurable_of_finite (extensionEquiv (X := X) k).symm).comp
      ((measurable_of_finite (interpret (X := X) (k+1))).comp
        (comap_measurable (beforeTables (X := X) (k+1) (Nat.succ_le_of_lt hk))))
  · intro k hk ω
    rw [he k hk ω]
  · intro k hk ω
    exact ((extensionEquiv k).apply_symm_apply _).symm
  · intro k hk h i x
    dsimp only [G]
    rw [dif_pos hk]
    have hfn : ({ω | nextStep k hk ω = ⟨h, i, x⟩}).indicator (fun _ => (1 : ℝ)) =
        fun ω => if interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) =
          append h i x then (1 : ℝ) else 0 := by
      funext ω
      simp only [nextStep, H, Set.indicator, Set.mem_setOf_eq, Equiv.symm_apply_eq]
      rfl
    rw [hfn]
    filter_upwards [conditional_child_given_schedule p hr k hk h i x] with ω hc
    intro hs
    rw [he k hk ω] at hs
    have hh := congrArg Sigma.fst hs
    change H k (Nat.le_of_lt hk) ω = h at hh
    subst h
    have hi := eq_of_heq (Sigma.mk.inj hs).2
    have hbranch : interpret k (beforeTables k (Nat.le_of_lt hk) ω) =
        H k (Nat.le_of_lt hk) ω ∧
          (currentBlock k hk ω).1 (H k (Nat.le_of_lt hk) ω) = i := ⟨rfl, hi⟩
    rw [if_pos hbranch] at hc
    exact hc.le.trans (((result_law p hr (H k (Nat.le_of_lt hk) ω) i).1 x).2)

/-- Every prescribed flow has an actual archived table realization with the complete
conditional cap; its history, selection and result masses agree exactly with the flow. -/
theorem realize_ordered_flow {r : I → ℝ} (p : Flow (X := X) r)
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i) :
    IsProbabilityMeasure (innovationLaw p) ∧
      (letI := (table_trace_realization p hr).1
       (canonicalArchivePath p hr).toFlow = p) := by
  haveI := (table_trace_realization p hr).1
  refine ⟨inferInstance, ?_⟩
  apply Flow.ext
  · funext k h
    have hk : k ≤ Fintype.card I := by
      have hc := Fintype.card_le_of_injective (fun j => (h.val j).1) h.property
      simpa using hc
    change (innovationLaw p).real ((canonicalArchivePath p hr).nodeEvent k h) = _
    have he : (canonicalArchivePath p hr).nodeEvent k h =
        {ω | interpret k (beforeTables k hk ω) = h} := by
      ext ω
      change (∃ hk' : k ≤ Fintype.card I,
        interpret k (beforeTables k hk' ω) = h) ↔ _
      exact ⟨fun ⟨_, hh⟩ => hh, fun hh => ⟨hk, hh⟩⟩
    rw [he]
    exact (table_trace_realization p hr).2.1 k hk h
  · funext k h i
    have hk := unread_lt h i
    change (innovationLaw p).real _ = _
    have he : (canonicalArchivePath p hr).selectEvent h i =
        {ω | ∃ x, interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) =
          append h i x} := by
      ext ω
      simp only [ArchivePath.selectEvent, canonicalArchivePath, selection_fiber,
        Equiv.symm_apply_eq]
      rfl
    rw [he]
    exact (table_trace_realization p hr).2.2.1 k hk h i
  · funext k h i x
    have hk := unread_lt h i
    change (innovationLaw p).real _ = _
    have he : (canonicalArchivePath p hr).resultEvent h i x =
        {ω | interpret (k+1) (beforeTables (k+1) (Nat.succ_le_of_lt hk) ω) = append h i x} := by
      ext ω
      simp only [ArchivePath.resultEvent, canonicalArchivePath, Equiv.symm_apply_eq]
      rfl
    rw [he]
    exact (table_trace_realization p hr).2.2.2.1 k hk h i x


private theorem innovation_likelihood_product {r : I → ℝ} (p : Flow (X := X) r)
    (k : ℕ) (w : TableTrace (X := X) k) :
    FiniteHistoryConditionalExpectation.likelihood (innovationKernel p) k () w =
      ∏ t : Fin k, scheduleDensity p t.val (w t).1 * resultDensity p t.val (w t).2 := by
  induction k with
  | zero => simp [FiniteHistoryConditionalExpectation.likelihood]
  | succ k ih =>
      rw [FiniteHistoryConditionalExpectation.likelihood, Fin.prod_univ_castSucc, ih]
      rfl

/-- The full innovation trace has the product atom law of every separate scheduling
and result table at every time. Together with normalized table laws, this certifies
fresh innovations, including independence of future results from current scheduling. -/
theorem innovation_product_atom {r : I → ℝ} (p : Flow (X := X) r)
    (w : TableTrace (X := X) (Fintype.card I)) :
    innovationLaw p {((), w)} = ENNReal.ofReal
      (∏ t : Fin (Fintype.card I),
        scheduleDensity p t.val (w t).1 * resultDensity p t.val (w t).2) := by
  classical
  simp [innovationLaw, FiniteHistoryConditionalExpectation.historyLaw,
    Measure.coe_finsetSum, Pi.single_apply, innovation_likelihood_product]

/-- Exact two-direction realization of the ordered-history flow projection. The
forward clause accepts any underlying probability space and arbitrary supplied full
archives. The reverse clause supplies an actual archive process with all prescribed
node, selection, result and terminal masses and the joint fresh-innovation product law.
The construction uses cap-only row pasting and preserves coordinate-result history
and terminal laws; it does not preserve the original auxiliary-record joint law. -/
theorem ordered_flow_terminal_law_realization {r : I → ℝ}
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    (∀ A : ArchivePath (X := X) r μ,
      ∃ p : Flow (X := X) r, A.toFlow = p ∧ terminalProjection p = A.terminalLaw) ∧
    (∀ p : Flow (X := X) r,
      IsProbabilityMeasure (innovationLaw p) ∧
      (letI := (table_trace_realization p hr).1
       (canonicalArchivePath p hr).toFlow = p ∧
       (canonicalArchivePath p hr).terminalLaw = terminalProjection p) ∧
      ∀ w : TableTrace (X := X) (Fintype.card I),
        innovationLaw p {((), w)} = ENNReal.ofReal
          (∏ t : Fin (Fintype.card I),
            scheduleDensity p t.val (w t).1 * resultDensity p t.val (w t).2)) := by
  constructor
  · intro A
    exact ⟨A.toFlow, rfl, A.terminalLaw_projection⟩
  · intro p
    haveI := (table_trace_realization p hr).1
    obtain ⟨hμ, hf⟩ := realize_ordered_flow p hr
    refine ⟨hμ, ⟨hf, ?_⟩, innovation_product_atom p⟩
    rw [← (canonicalArchivePath p hr).terminalLaw_projection, hf]


/-- Terminal laws of actual archived strategies on the universal finite innovation
carrier. The measure and archive path are quantified independently of flows. Every
law of an arbitrary-carrier strategy belongs here by the two-direction theorem. -/
def archiveTerminalLaws (r : I → ℝ) : Set (((i : I) → X i) → ℝ) :=
  {law | ∃ μ : Measure (Sample (X := X)), ∃ hμ : IsProbabilityMeasure μ,
    ∃ A : ArchivePath (X := X) r μ, letI := hμ; A.terminalLaw = law}

/-- The terminal projection range is exactly the actual archived-strategy law set.
The same statement also embeds the terminal law of any arbitrary-carrier archived
strategy into this set, so the finite witness carrier does not narrow the forward law set. -/
theorem ordered_terminal_law_range {r : I → ℝ}
    (hr : ∀ i, 1 / (Fintype.card (X i) : ℝ) ≤ r i)
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Set.range (terminalProjection (X := X) (r := r)) = archiveTerminalLaws (X := X) r ∧
    ∀ A : ArchivePath (X := X) r μ, A.terminalLaw ∈ archiveTerminalLaws (X := X) r := by
  have ranges : Set.range (terminalProjection (X := X) (r := r)) =
      archiveTerminalLaws (X := X) r := by
    ext law
    constructor
    · rintro ⟨p, rfl⟩
      haveI := (table_trace_realization p hr).1
      refine ⟨innovationLaw p, inferInstance, canonicalArchivePath p hr, ?_⟩
      exact ((ordered_flow_terminal_law_realization hr μ).2 p).2.1.2
    · rintro ⟨ν, hν, A, he⟩
      letI := hν
      exact ⟨A.toFlow, A.terminalLaw_projection.trans he⟩
  refine ⟨ranges, ?_⟩
  intro A
  rw [← ranges]
  exact ⟨A.toFlow, A.terminalLaw_projection⟩




#print axioms ordered_terminal_law_range
#print axioms ordered_flow_terminal_law_realization
#print axioms innovation_product_atom
#print axioms archive_event_cap
#print axioms table_trace_realization
#print axioms ArchivePath.toFlow
#print axioms conditional_child_given_schedule
#print axioms realize_ordered_flow
end D5.S3.Estimation.DataProcessing.OrderedCoordinateFlowRealization
