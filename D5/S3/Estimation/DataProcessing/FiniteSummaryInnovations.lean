/- GID: D5/S3/Estimation/DataProcessing/FiniteSummaryInnovations
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/FiniteSummaryInnovations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Combination]
   utility: none
   digest: Chronological finite summary innovations separate scheduling tables from fresh result tables. -/

import D5.S3.Estimation.DataProcessing.FiniteSummaryAggregation
import D5.S3.Estimation.DataProcessing.OrderedCoordinateHistoryInterpreter
import D5.S3.Estimation.DataProcessing.PartialAssignmentOccupancyFlow

open MeasureTheory Finset
open scoped BigOperators ENNReal Classical
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section
namespace D5.S3.Estimation.DataProcessing.FiniteSummaryInnovations
open FiniteSummaryAggregation
open FiniteHistoryConditionalExpectation
open OrderedCoordinateHistoryInterpreter (product_row_marginal)

variable {S : ℕ → Type} {H : (k : ℕ) → S k → Type}
  {A : (k : ℕ) → S k → Type} {X : (k : ℕ) → (s : S k) → A k s → Type}
  [∀ k, Fintype (S k)] [∀ k s, Fintype (H k s)]
  [∀ k s, Fintype (A k s)]
  [∀ k s i, Fintype (X k s i)]
  {N : ℕ} {tree : Dynamics S H A X N} {K : RowSets S A X}

abbrev ScheduleTable (k : ℕ) := (s : S k) → A k s
abbrev ResultTable (k : ℕ) := (c : Σ s : S k, A k s) → X k c.1 c.2

@[reducible] def clock : ℕ → ℕ
  | 0 => 0
  | k+1 => clock k + 2

private theorem clock_eq (k : ℕ) : clock k = 2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [clock, ih]; omega

def scheduleDensity (p : Flow tree K) (k : ℕ) (a : ScheduleTable (A := A) k) : ℝ :=
  ∏ s, scheduler p k s (a s)
def resultDensity (p : Flow tree K) (k : ℕ) (b : ResultTable (X := X) k) : ℝ :=
  ∏ c, resultRow p k c.1 c.2 (b c)

theorem table_laws (p : Flow tree K) (k : ℕ) (hk : k < N) :
    ((∀ a, 0 ≤ scheduleDensity p k a) ∧ ∑ a, scheduleDensity p k a = 1) ∧
    ((∀ b, 0 ≤ resultDensity p k b) ∧ ∑ b, resultDensity p k b = 1) := by
  constructor
  · exact ⟨fun a => Finset.prod_nonneg (fun s _ => (normalized_rows p k hk s).1.1 _), by
      unfold scheduleDensity
      rw [← Fintype.prod_sum]
      simp_rw [(normalized_rows p k hk _).1.2]
      simp⟩
  · exact ⟨fun b => Finset.prod_nonneg (fun c _ =>
      (K.lawful k c.1 c.2 _ ((normalized_rows p k hk c.1).2 c.2)).1 _), by
      unfold resultDensity
      rw [← Fintype.prod_sum]
      simp_rw [(K.lawful k _ _ _ ((normalized_rows p k hk _).2 _)).2]
      simp⟩

/-- Only schedule innovations are recorded at even microsteps; only fresh result
innovations are recorded at odd microsteps. The unused telescope tail is a singleton. -/
abbrev Innovation (n : ℕ) : Type :=
  if n < 2*N then
    if n % 2 = 0 then ScheduleTable (A := A) (n/2) else ResultTable (X := X) (n/2)
  else Unit

instance innovationFintype (n : ℕ) : Fintype (Innovation (A := A) (X := X) (N := N) n) := by
  unfold Innovation
  split_ifs <;> infer_instance
instance innovationMeasurable (n : ℕ) : MeasurableSpace (Innovation (A := A) (X := X) (N := N) n) := ⊤
instance innovationSingleton (n : ℕ) :
    MeasurableSingletonClass (Innovation (A := A) (X := X) (N := N) n) :=
  ⟨fun _ => trivial⟩

def scheduleEquiv (k : ℕ) (hk : k < N) :
    Innovation (A := A) (X := X) (N := N) (clock k) ≃ ScheduleTable (A := A) k :=
  Equiv.cast (by
    have hb : 2*k < 2*N := by omega
    have hm : (2*k)%2 = 0 := by omega
    have hd : (2*k)/2 = k := by omega
    simp [Innovation, clock_eq, hb, hm, hd])

def resultEquiv (k : ℕ) (hk : k < N) :
    Innovation (A := A) (X := X) (N := N) (clock k+1) ≃ ResultTable (X := X) k :=
  Equiv.cast (by
    have hb : 2*k+1 < 2*N := by omega
    have hm : (2*k+1)%2 = 1 := by omega
    have hd : (2*k+1)/2 = k := by omega
    simp [Innovation, clock_eq, hb, hm, hd])

def innovationDensity (p : Flow tree K) (n : ℕ)
    (z : Innovation (A := A) (X := X) (N := N) n) : ℝ :=
  if hn : n < 2*N then
    if hm : n%2 = 0 then
      scheduleDensity p (n/2) (Equiv.cast (by simp [Innovation, hn, hm]) z)
    else resultDensity p (n/2) (Equiv.cast (by simp [Innovation, hn, hm]) z)
  else 1

def innovationKernel (p : Flow tree K) (n : ℕ) (_ : Unit)
    (_ : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) n)
    (z : Innovation (A := A) (X := X) (N := N) n) : ℝ := innovationDensity p n z

theorem innovation_law (p : Flow tree K) (n : ℕ) :
    (∀ z, 0 ≤ innovationDensity p n z) ∧ ∑ z, innovationDensity p n z = 1 := by
  classical
  by_cases hn : n < 2*N
  · by_cases hm : n%2 = 0
    · let e : Innovation (A := A) (X := X) (N := N) n ≃ ScheduleTable (A := A) (n/2) :=
        Equiv.cast (by simp [Innovation, hn, hm])
      have he (z : Innovation (A := A) (X := X) (N := N) n) :
          innovationDensity p n z = scheduleDensity p (n/2) (e z) := by
        simp [innovationDensity, hn, hm, e, cast_cast]
      simp_rw [he]
      exact ⟨fun z => (table_laws p (n/2) (by omega)).1.1 _, by
        rw [e.sum_comp, (table_laws p (n/2) (by omega)).1.2]⟩
    · let e : Innovation (A := A) (X := X) (N := N) n ≃ ResultTable (X := X) (n/2) :=
        Equiv.cast (by simp [Innovation, hn, hm])
      have he (z : Innovation (A := A) (X := X) (N := N) n) :
          innovationDensity p n z = resultDensity p (n/2) (e z) := by
        simp [innovationDensity, hn, hm, e, cast_cast]
      simp_rw [he]
      exact ⟨fun z => (table_laws p (n/2) (by omega)).2.1 _, by
        rw [e.sum_comp, (table_laws p (n/2) (by omega)).2.2]⟩
  · have he : Innovation (A := A) (X := X) (N := N) n ≃ Unit :=
      Equiv.cast (by simp [Innovation, hn])
    simp [innovationDensity, hn, Fintype.card_congr he]

/-- The actual finite probability carrier has no hidden initial information. -/
def law (p : Flow tree K) :
    Measure (Unit × FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (2*N)) :=
  historyLaw (fun _ : Unit => 1) (innovationKernel p) (2*N)

theorem probability_law (p : Flow tree K) : IsProbabilityMeasure (law p) := by
  exact (history_law_conditional_expectation (fun _ : Unit => 1)
    ⟨fun _ => zero_le_one, by simp⟩ (innovationKernel p) (2*N)
    (fun n _ => ⟨fun _ _ z => (innovation_law p n).1 z,
      fun _ _ => (innovation_law p n).2⟩)).1

/-- The public state depends only on the tables already consumed. -/
def run : (k : ℕ) → k ≤ N →
    FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k) → S k
  | 0, _, _ => tree.root.1
  | k+1, hk, w =>
      let s := run k (by omega) (Fin.init (Fin.init w))
      let a := scheduleEquiv k (by omega) ((Fin.init w) (Fin.last (clock k)))
      let b := resultEquiv k (by omega) (w (Fin.last (clock k+1)))
      tree.update k s (a s) (b ⟨s,a s⟩)

def selected (k : ℕ) (hk : k < N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k+1)) : Σ s : S k, A k s :=
  let s := run (tree := tree) k (Nat.le_of_lt hk) (Fin.init w)
  ⟨s, scheduleEquiv k hk (w (Fin.last (clock k))) s⟩

private theorem schedule_density (p : Flow tree K) (k : ℕ) (hk : k < N)
    (z : Innovation (A := A) (X := X) (N := N) (clock k)) :
    innovationDensity p (clock k) z = scheduleDensity p k (scheduleEquiv k hk z) := by
  have hb : clock k < 2*N := by rw [clock_eq]; omega
  have hm : clock k%2 = 0 := by rw [clock_eq]; omega
  have hd : clock k/2 = k := by rw [clock_eq]; omega
  simp only [innovationDensity, dif_pos hb, dif_pos hm, scheduleEquiv, Equiv.cast_apply]
  apply congr_heq (congr_arg_heq (fun j => scheduleDensity p j) hd)
  exact (cast_heq _ z).trans (cast_heq _ z).symm

private theorem result_density (p : Flow tree K) (k : ℕ) (hk : k < N)
    (z : Innovation (A := A) (X := X) (N := N) (clock k+1)) :
    innovationDensity p (clock k+1) z = resultDensity p k (resultEquiv k hk z) := by
  have hb : clock k+1 < 2*N := by rw [clock_eq]; omega
  have hm : (clock k+1)%2 = 1 := by rw [clock_eq]; omega
  have hd : (clock k+1)/2 = k := by rw [clock_eq]; omega
  have hm' : ¬(clock k+1)%2 = 0 := by omega
  simp only [innovationDensity, dif_pos hb, dif_neg hm', resultEquiv, Equiv.cast_apply]
  apply congr_heq (congr_arg_heq (fun j => resultDensity p j) hd)
  exact (cast_heq _ z).trans (cast_heq _ z).symm

private theorem schedule_average (p : Flow tree K) (k : ℕ) (hk : k < N)
    (s : S k) (f : A k s → ℝ) :
    (∑ z, innovationDensity p (clock k) z * f (scheduleEquiv k hk z s)) =
      ∑ i, scheduler p k s i * f i := by
  simp_rw [schedule_density p k hk]
  change (∑ z, (fun a : ScheduleTable (A := A) k =>
    scheduleDensity p k a * f (a s)) (scheduleEquiv k hk z)) = _
  calc
    _ = ∑ a : ScheduleTable (A := A) k, scheduleDensity p k a * f (a s) :=
      Fintype.sum_equiv (scheduleEquiv (A := A) (X := X) k hk) _ _ (fun _ => rfl)
    _ = _ := product_row_marginal (C := S k) (Y := A k) (fun s i => scheduler p k s i)
      (fun s => (normalized_rows p k hk s).1.2) s f

private theorem result_average (p : Flow tree K) (k : ℕ) (hk : k < N)
    (s : S k) (i : A k s) (f : X k s i → ℝ) :
    (∑ z, innovationDensity p (clock k+1) z * f (resultEquiv k hk z ⟨s,i⟩)) =
      ∑ x, resultRow p k s i x * f x := by
  simp_rw [result_density p k hk]
  change (∑ z, (fun b : ResultTable (X := X) k =>
    resultDensity p k b * f (b ⟨s,i⟩)) (resultEquiv k hk z)) = _
  calc
    _ = ∑ b : ResultTable (X := X) k, resultDensity p k b * f (b ⟨s,i⟩) :=
      Fintype.sum_equiv (resultEquiv (A := A) (X := X) k hk) _ _ (fun _ => rfl)
    _ = _ := product_row_marginal (C := Σ s : S k, A k s)
      (Y := fun c => X k c.1 c.2) (fun c x => resultRow p k c.1 c.2 x)
      (fun c => (K.lawful k c.1 c.2 _ ((normalized_rows p k hk c.1).2 c.2)).2) ⟨s,i⟩ f

private theorem append_sum (p : Flow tree K) (n : ℕ)
    (f : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (n+1) → ℝ) :
    (∑ w, likelihood (innovationKernel p) (n+1) () w * f w) =
      ∑ w, ∑ z, likelihood (innovationKernel p) n () w *
        innovationDensity p n z * f (Fin.snoc w z) := by
  rw [← (Fin.snocEquiv (fun j : Fin (n+1) =>
    Innovation (A := A) (X := X) (N := N) j.val)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, likelihood, Fin.init_snoc,
    Fin.snoc_last, innovationKernel]
  rw [Finset.sum_comm]
  rfl

private theorem incoming_test (p : Flow tree K) (k : ℕ) (hk : k < N)
    (f : S (k+1) → ℝ) :
    (∑ s, nodeMass p k s * (∑ i, scheduler p k s i *
      (∑ x, resultRow p k s i x * f (tree.update k s i x)))) =
      ∑ t, nodeMass p (k+1) t * f t := by
  classical
  simp_rw [incoming_conservation p k hk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_assoc, ← mul_assoc, (weighted_rows p k hk s).1 i,
    (weighted_rows p k hk s).2 i x]
  simp

private theorem run_snoc (k : ℕ) (hk : k+1 ≤ N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k))
    (a : Innovation (A := A) (X := X) (N := N) (clock k))
    (b : Innovation (A := A) (X := X) (N := N) (clock k+1)) :
    run (tree := tree) (k+1) hk (Fin.snoc (Fin.snoc w a) b) =
      tree.update k (run (tree := tree) k (by omega) w)
        (scheduleEquiv k (by omega) a (run (tree := tree) k (by omega) w))
        (resultEquiv k (by omega) b ⟨run (tree := tree) k (by omega) w,
          scheduleEquiv k (by omega) a (run (tree := tree) k (by omega) w)⟩) := by
  dsimp only [run]
  rw [Fin.init_snoc, Fin.init_snoc, Fin.snoc_last, Fin.snoc_last]

/-- Interpreting the same fresh trace realizes every summary node mass. -/
theorem trace_expectation (p : Flow tree K) (k : ℕ) (hk : k ≤ N) (f : S k → ℝ) :
    (∑ w, likelihood (innovationKernel p) (clock k) () w *
      f (run (tree := tree) k hk w)) = ∑ s, nodeMass p k s * f s := by
  classical
  induction k with
  | zero =>
    have hm (s : S 0) : nodeMass p 0 s = if s = tree.root.1 then 1 else 0 :=
      (recursive_mass p 0 (Nat.zero_le N) s).symm
    simp [clock, likelihood, run, hm, Fintype.card_eq_one_iff]
  | succ k ih =>
    have hk' : k < N := by omega
    have step (w : FiniteHistoryConditionalExpectation.History
        (Innovation (A := A) (X := X) (N := N)) (clock k)) :
        (∑ a, innovationDensity p (clock k) a *
          (∑ b, innovationDensity p (clock k+1) b *
            f (run (tree := tree) (k+1) hk (Fin.snoc (Fin.snoc w a) b)))) =
          ∑ i, scheduler p k (run (tree := tree) k (by omega) w) i *
            (∑ x, resultRow p k (run (tree := tree) k (by omega) w) i x *
              f (tree.update k (run (tree := tree) k (by omega) w) i x)) := by
      simp_rw [run_snoc k hk]
      have hb (a : Innovation (A := A) (X := X) (N := N) (clock k)) :=
        result_average p k hk' (run (tree := tree) k (by omega) w)
          (scheduleEquiv k hk' a (run (tree := tree) k (by omega) w))
          (fun x => f (tree.update k (run (tree := tree) k (by omega) w)
            (scheduleEquiv k hk' a (run (tree := tree) k (by omega) w)) x))
      simp_rw [hb]
      exact schedule_average p k hk' (run (tree := tree) k (by omega) w)
        (fun i => ∑ x, resultRow p k (run (tree := tree) k (by omega) w) i x *
          f (tree.update k (run (tree := tree) k (by omega) w) i x))
    change (∑ w, likelihood (innovationKernel p) (clock k+1+1) () w *
      f (run (tree := tree) (k+1) hk w)) = _
    calc
      _ = ∑ v, likelihood (innovationKernel p) (clock k+1) () v *
          (∑ b, innovationDensity p (clock k+1) b *
            f (run (tree := tree) (k+1) hk (Fin.snoc v b))) := by
        rw [append_sum]
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ w, likelihood (innovationKernel p) (clock k) () w *
          (∑ a, innovationDensity p (clock k) a *
            (∑ b, innovationDensity p (clock k+1) b *
              f (run (tree := tree) (k+1) hk (Fin.snoc (Fin.snoc w a) b)))) := by
        rw [append_sum]
        simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ s, nodeMass p k s * (∑ i, scheduler p k s i *
          (∑ x, resultRow p k s i x * f (tree.update k s i x))) := by
        simp_rw [step]
        exact ih (by omega) (fun s => ∑ i, scheduler p k s i *
          (∑ x, resultRow p k s i x * f (tree.update k s i x)))
      _ = _ := incoming_test p k hk' f

private theorem selected_snoc (k : ℕ) (hk : k < N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k))
    (a : Innovation (A := A) (X := X) (N := N) (clock k)) :
    selected (tree := tree) k hk (Fin.snoc w a) =
      ⟨run (tree := tree) k hk.le w,
        scheduleEquiv k hk a (run (tree := tree) k hk.le w)⟩ := by
  dsimp only [selected]
  rw [Fin.init_snoc, Fin.snoc_last]

private theorem selection_expectation (p : Flow tree K) (k : ℕ) (hk : k < N)
    (f : (Σ s : S k, A k s) → ℝ) :
    (∑ w, likelihood (innovationKernel p) (clock k+1) () w *
      f (selected (tree := tree) k hk w)) =
      ∑ s, ∑ i, selectionMass p k s i * f ⟨s,i⟩ := by
  classical
  rw [append_sum]
  have he (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k)) :
      (∑ a, innovationDensity p (clock k) a *
        f (selected (tree := tree) k hk (Fin.snoc w a))) =
        ∑ i, scheduler p k (run (tree := tree) k hk.le w) i *
          f ⟨run (tree := tree) k hk.le w,i⟩ := by
    simp_rw [selected_snoc]
    exact schedule_average p k hk _ (fun i => f ⟨run (tree := tree) k hk.le w,i⟩)
  calc
    _ = ∑ w, likelihood (innovationKernel p) (clock k) () w *
        (∑ i, scheduler p k (run (tree := tree) k hk.le w) i *
          f ⟨run (tree := tree) k hk.le w,i⟩) := by
      simp only [mul_assoc, ← Finset.mul_sum, he]
    _ = ∑ s, nodeMass p k s * (∑ i, scheduler p k s i * f ⟨s,i⟩) :=
      trace_expectation p k hk.le (fun s => ∑ i, scheduler p k s i * f ⟨s,i⟩)
    _ = _ := by
      simp_rw [Finset.mul_sum, ← mul_assoc, (weighted_rows p k hk _).1]

/-- The actual observed edge uses the current result table after scheduling. -/
def observedEdge (k : ℕ) (hk : k < N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k+2)) :
    Σ s : S k, Σ i : A k s, X k s i :=
  let c := selected (tree := tree) k hk (Fin.init w)
  ⟨c.1,c.2,resultEquiv k hk (w (Fin.last (clock k+1))) c⟩

private theorem observed_snoc (k : ℕ) (hk : k < N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k+1))
    (b : Innovation (A := A) (X := X) (N := N) (clock k+1)) :
    observedEdge (tree := tree) k hk (Fin.snoc w b) =
      ⟨(selected (tree := tree) k hk w).1,(selected (tree := tree) k hk w).2,
        resultEquiv k hk b (selected (tree := tree) k hk w)⟩ := by
  dsimp only [observedEdge]
  rw [Fin.init_snoc, Fin.snoc_last]

private theorem edge_expectation (p : Flow tree K) (k : ℕ) (hk : k < N)
    (f : (Σ s : S k, Σ i : A k s, X k s i) → ℝ) :
    (∑ w, likelihood (innovationKernel p) (clock k+2) () w *
      f (observedEdge (tree := tree) k hk w)) =
      ∑ s, ∑ i, ∑ x, resultMass p k s i x * f ⟨s,i,x⟩ := by
  classical
  rw [append_sum]
  have he (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k+1)) :
      (∑ b, innovationDensity p (clock k+1) b *
        f (observedEdge (tree := tree) k hk (Fin.snoc w b))) =
        ∑ x, resultRow p k (selected (tree := tree) k hk w).1
          (selected (tree := tree) k hk w).2 x *
            f ⟨(selected (tree := tree) k hk w).1,(selected (tree := tree) k hk w).2,x⟩ := by
    simp_rw [observed_snoc]
    exact result_average p k hk _ _ (fun x => f
      ⟨(selected (tree := tree) k hk w).1,(selected (tree := tree) k hk w).2,x⟩)
  calc
    _ = ∑ w, likelihood (innovationKernel p) (clock k+1) () w *
        (∑ x, resultRow p k (selected (tree := tree) k hk w).1
          (selected (tree := tree) k hk w).2 x *
            f ⟨(selected (tree := tree) k hk w).1,(selected (tree := tree) k hk w).2,x⟩) := by
      simp only [mul_assoc, ← Finset.mul_sum, he]
    _ = ∑ s, ∑ i, selectionMass p k s i *
        (∑ x, resultRow p k s i x * f ⟨s,i,x⟩) :=
      selection_expectation p k hk (fun c => ∑ x, resultRow p k c.1 c.2 x * f ⟨c.1,c.2,x⟩)
    _ = _ := by
      simp_rw [Finset.mul_sum, ← mul_assoc, (weighted_rows p k hk _).2]

/-- Exact prefix integrals on the actual carrier; the initial coordinate is a singleton. -/
private theorem prefix_integral (p : Flow tree K) (t : ℕ) (ht : t ≤ 2*N)
    (f : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) t → ℝ) :
    (∫ ω, f (readPrefix ht ω.2) ∂law p) =
      ∑ w, likelihood (innovationKernel p) t () w * f w := by
  simpa [law] using (history_law_conditional_expectation (fun _ : Unit => 1)
    ⟨fun _ => zero_le_one, by simp⟩ (innovationKernel p) (2*N)
    (fun n _ => ⟨fun _ _ z => (innovation_law p n).1 z,
      fun _ _ => (innovation_law p n).2⟩)).2.1 t ht (fun _ w => f w)

/-- All node, named-action selection and dependent-result masses belong to one
actual probability process, including zero-mass branches. -/
theorem realized_flows (p : Flow tree K) :
    IsProbabilityMeasure (law p) ∧
    (∀ k (hk : k ≤ N) (f : S k → ℝ),
      (∫ ω, f (run (tree := tree) k hk
        (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p) =
          ∑ s, nodeMass p k s * f s) ∧
    (∀ k (hk : k < N) (f : (Σ s : S k, A k s) → ℝ),
      (∫ ω, f (selected (tree := tree) k hk
        (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p) =
          ∑ s, ∑ i, selectionMass p k s i * f ⟨s,i⟩) ∧
    (∀ k (hk : k < N) (f : (Σ s : S k, Σ i : A k s, X k s i) → ℝ),
      (∫ ω, f (observedEdge (tree := tree) k hk
        (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p) =
          ∑ s, ∑ i, ∑ x, resultMass p k s i x * f ⟨s,i,x⟩) := by
  refine ⟨probability_law p, ?_, ?_, ?_⟩
  · intro k hk f
    exact (prefix_integral p (clock k) (by rw [clock_eq]; omega)
      (fun w => f (run (tree := tree) k hk w))).trans (trace_expectation p k hk f)
  · intro k hk f
    exact (prefix_integral p (clock k+1) (by rw [clock_eq]; omega)
      (fun w => f (selected (tree := tree) k hk w))).trans (selection_expectation p k hk f)
  · intro k hk f
    exact (prefix_integral p (clock k+2) (by rw [clock_eq]; omega)
      (fun w => f (observedEdge (tree := tree) k hk w))).trans (edge_expectation p k hk f)

private theorem fresh_conditional (p : Flow tree K) (t : ℕ) (ht : t < 2*N)
    (f : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (t+1) → ℝ) :
    (law p)[(fun ω => f (readPrefix (Nat.succ_le_of_lt ht) ω.2)) |
      historySigma t (Nat.le_of_lt ht)] =ᵐ[law p]
      fun ω => ∑ z, innovationDensity p t z *
        f (Fin.snoc (readPrefix (Nat.le_of_lt ht) ω.2) z) := by
  classical
  letI := probability_law p
  have hce := (history_law_conditional_expectation (fun _ : Unit => 1)
    ⟨fun _ => zero_le_one, by simp⟩ (innovationKernel p) (2*N)
    (fun n _ => ⟨fun _ _ z => (innovation_law p n).1 z,
      fun _ _ => (innovation_law p n).2⟩)).2.2 t ht f
  simp only [historyMass, Fintype.sum_unique, one_mul, likelihood, Fin.init_snoc,
    Fin.snoc_last, innovationKernel] at hce
  change (law p)[(fun ω => f (readPrefix (Nat.succ_le_of_lt ht) ω.2)) |
    historySigma t (Nat.le_of_lt ht)] =ᵐ[law p] _ at hce
  refine hce.trans ?_
  let L (h : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) t) := likelihood (innovationKernel p) t () h
  let r (h : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) t) :=
    ∑ z, (L h * innovationDensity p t z) / L h * f (Fin.snoc h z)
  let u (h : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) t) :=
    ∑ z, innovationDensity p t z * f (Fin.snoc h z)
  let e (h : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) t) :=
    {ω : Unit × FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (2*N) |
      readPrefix (Nat.le_of_lt ht) ω.2 = h}
  have mass (h) : (law p).real (e h) = L h := by
    have hme : MeasurableSet (e h) := (Set.toFinite _).measurableSet
    rw [← integral_indicator_one hme]
    simpa [e, Set.indicator, L] using
      prefix_integral p t (Nat.le_of_lt ht) (fun w => if w = h then 1 else 0)
  have balance (h) : L h * r h = L h * u h := by
    dsimp [r, u]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : L h = 0
    · simp [hz]
    · field_simp
  have hn (h) : (e h).indicator (fun _ => r h) =ᵐ[law p]
      (e h).indicator (fun _ => u h) :=
    PartialAssignmentOccupancyFlow.null_row_replace (law p) (e h) (L h) (r h) (u h)
      (mass h) (balance h)
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  change r (readPrefix (Nat.le_of_lt ht) ω.2) = u (readPrefix (Nat.le_of_lt ht) ω.2)
  have hi := hω (readPrefix (Nat.le_of_lt ht) ω.2)
  simpa [e, Set.indicator_of_mem] using hi

private theorem schedule_indicator (p : Flow tree K) (k : ℕ) (hk : k < N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k)) (s : S k) (i : A k s) :
    (∑ a, innovationDensity p (clock k) a *
      (if selected (tree := tree) k hk (Fin.snoc w a) = ⟨s,i⟩ then (1 : ℝ) else 0)) =
      if run (tree := tree) k hk.le w = s then scheduler p k s i else 0 := by
  classical
  simp_rw [selected_snoc]
  by_cases hs : run (tree := tree) k hk.le w = s
  · subst s
    simpa using schedule_average p k hk (run (tree := tree) k hk.le w)
      (fun j => if j = i then 1 else 0)
  · have he (a : Innovation (A := A) (X := X) (N := N) (clock k)) :
        (⟨run (tree := tree) k hk.le w,
          scheduleEquiv k hk a (run (tree := tree) k hk.le w)⟩ : Σ s : S k, A k s) ≠ ⟨s,i⟩ := by
      intro h
      exact hs (congrArg Sigma.fst h)
    simp [he, hs]

private theorem result_indicator (p : Flow tree K) (k : ℕ) (hk : k < N)
    (w : FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (clock k+1))
    (s : S k) (i : A k s) (x : X k s i) :
    (∑ b, innovationDensity p (clock k+1) b *
      (if observedEdge (tree := tree) k hk (Fin.snoc w b) = ⟨s,i,x⟩ then (1 : ℝ) else 0)) =
      if selected (tree := tree) k hk w = ⟨s,i⟩ then resultRow p k s i x else 0 := by
  classical
  simp_rw [observed_snoc]
  generalize hc : selected (tree := tree) k hk w = c
  rcases c with ⟨t,j⟩
  by_cases hs : t = s
  · subst s
    by_cases hi : j = i
    · subst i
      simpa using result_average p k hk t j (fun y => if y = x then 1 else 0)
    · have he (b : Innovation (A := A) (X := X) (N := N) (clock k+1)) :
          (⟨t,j,resultEquiv k hk b ⟨t,j⟩⟩ : Σ s : S k, Σ i : A k s, X k s i) ≠ ⟨t,i,x⟩ := by
        intro h
        exact hi (Sigma.mk.inj ((Sigma.mk.inj h).2.eq)).1
      simp [he, hi]
  · have he (b : Innovation (A := A) (X := X) (N := N) (clock k+1)) :
        (⟨t,j,resultEquiv k hk b ⟨t,j⟩⟩ : Σ s : S k, Σ i : A k s, X k s i) ≠ ⟨s,i,x⟩ := by
      intro h
      exact hs (congrArg Sigma.fst h)
    have hn : (⟨t,j⟩ : Σ s : S k, A k s) ≠ ⟨s,i⟩ := by
      intro h
      exact hs (congrArg Sigma.fst h)
    simp [he, hn]

/-- Scheduler conditioning uses the complete prefix before its fresh table;
result conditioning uses the complete prefix including that scheduling table. -/
theorem full_history_kernels (p : Flow tree K) (k : ℕ) (hk : k < N)
    (s : S k) (i : A k s) :
    ((law p)[(fun ω => if selected (tree := tree) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2) = ⟨s,i⟩ then (1 : ℝ) else 0) |
      historySigma (clock k) (by rw [clock_eq]; omega)] =ᵐ[law p]
      fun ω => if run (tree := tree) k hk.le
        (readPrefix (by rw [clock_eq]; omega) ω.2) = s then scheduler p k s i else 0) ∧
    ∀ x : X k s i,
      (law p)[(fun ω => if observedEdge (tree := tree) k hk
        (readPrefix (by rw [clock_eq]; omega) ω.2) = ⟨s,i,x⟩ then (1 : ℝ) else 0) |
        historySigma (clock k+1) (by rw [clock_eq]; omega)] =ᵐ[law p]
        fun ω => if selected (tree := tree) k hk
          (readPrefix (by rw [clock_eq]; omega) ω.2) = ⟨s,i⟩ then resultRow p k s i x else 0 := by
  constructor
  · refine (fresh_conditional p (clock k) (by rw [clock_eq]; omega)
      (fun w => if selected (tree := tree) k hk w = ⟨s,i⟩ then 1 else 0)).trans ?_
    exact Filter.Eventually.of_forall (fun ω => schedule_indicator p k hk _ s i)
  · intro x
    refine (fresh_conditional p (clock k+1) (by rw [clock_eq]; omega)
      (fun w => if observedEdge (tree := tree) k hk w = ⟨s,i,x⟩ then 1 else 0)).trans ?_
    exact Filter.Eventually.of_forall (fun ω => result_indicator p k hk _ s i x)

def terminalOutput {Y : Type*} (output : S N → Y)
    (ω : Unit × FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (2*N)) : Y :=
  output (run (tree := tree) N le_rfl (readPrefix (by rw [clock_eq]) ω.2))

def sourceOutputLaw {Y : Type*} [MeasurableSpace Y] (p : Flow tree K)
    (output : (s : S N) → H N s → Y) : Measure Y :=
  ∑ s, ∑ h, ENNReal.ofReal (p.mass N s h) • Measure.dirac (output s h)

/-- Complete terminal output factorization preserves its entire pushforward law. -/
theorem terminal_output_law {Y : Type*} [MeasurableSpace Y] (p : Flow tree K)
    (output : (s : S N) → H N s → Y) (summaryOutput : S N → Y)
    (factor : ∀ s h, output s h = summaryOutput s) :
    Measure.map (terminalOutput (tree := tree) summaryOutput) (law p) =
      sourceOutputLaw p output := by
  classical
  letI := probability_law p
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_of_finite _) hB]
  let e := {ω : Unit × FiniteHistoryConditionalExpectation.History
      (Innovation (A := A) (X := X) (N := N)) (2*N) |
      terminalOutput (tree := tree) summaryOutput ω ∈ B}
  have he : MeasurableSet e := (Set.toFinite _).measurableSet
  have hmass : (law p).real e = ∑ s, nodeMass p N s *
      (if summaryOutput s ∈ B then 1 else 0) := by
    rw [← integral_indicator_one he]
    calc
      _ = ∫ ω, (if summaryOutput (run (tree := tree) N le_rfl
          (readPrefix (by rw [clock_eq]) ω.2)) ∈ B then (1 : ℝ) else 0) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          simp only [e, Set.indicator, terminalOutput, Set.mem_setOf_eq, Pi.one_apply]
          )
      _ = _ := (realized_flows p).2.1 N le_rfl
        (fun s => if summaryOutput s ∈ B then 1 else 0)
  change (law p) e = _
  rw [← ENNReal.ofReal_toReal (measure_ne_top (law p) e)]
  change ENNReal.ofReal ((law p).real e) = _
  rw [hmass]
  simp only [nodeMass, Finset.sum_mul]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · unfold sourceOutputLaw
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro s _
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro h _
      simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB, factor]
      by_cases hs : summaryOutput s ∈ B <;> simp [hs]
    · intro h _
      exact mul_nonneg (p.mass_nonneg N s h) (by split_ifs <;> norm_num)
  · intro s _
    exact Finset.sum_nonneg (fun h _ => mul_nonneg (p.mass_nonneg N s h)
      (by split_ifs <;> norm_num))

/-- Price-preserving transition labels retain expected additive cost. A row-choice
charge is covered only if it satisfies the stated source label factorization. -/
theorem expected_additive_price (p : Flow tree K)
    (label : (k : Fin N) → (Σ s : S k.val, Σ i : A k.val s, X k.val s i) → ℝ)
    (price : (k : Fin N) → (s : S k.val) → H k.val s →
      (i : A k.val s) → X k.val s i → ℝ)
    (preserved : ∀ k s h i x, price k s h i x = label k ⟨s,i,x⟩) :
    (∫ ω, (∑ k : Fin N, label k (observedEdge (tree := tree) k.val k.isLt
      (readPrefix (by rw [clock_eq]; omega) ω.2))) ∂law p) =
      ∑ k : Fin N, ∑ s, ∑ h, ∑ i, ∑ x,
        (p.select k.val s h i * p.row k.val s h i x) * price k s h i x := by
  classical
  letI := probability_law p
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro k _
  rw [(realized_flows p).2.2.2 k.val k.isLt (label k)]
  simp_rw [resultMass, Finset.sum_mul, preserved]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]

/-- One carrier, all occupation flows, full chronological conditional kernels,
complete terminal tasks, and explicitly price-preserving additive labels. -/
structure Realization (p : Flow tree K) : Prop where
  probability : IsProbabilityMeasure (law p)
  nodes : ∀ k (hk : k ≤ N) (f : S k → ℝ),
    (∫ ω, f (run (tree := tree) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p) =
        ∑ s, nodeMass p k s * f s
  selections : ∀ k (hk : k < N) (f : (Σ s : S k, A k s) → ℝ),
    (∫ ω, f (selected (tree := tree) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p) =
        ∑ s, ∑ i, selectionMass p k s i * f ⟨s,i⟩
  results : ∀ k (hk : k < N) (f : (Σ s : S k, Σ i : A k s, X k s i) → ℝ),
    (∫ ω, f (observedEdge (tree := tree) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p) =
        ∑ s, ∑ i, ∑ x, resultMass p k s i x * f ⟨s,i,x⟩
  scheduler_kernel : ∀ k (hk : k < N) (s : S k) (i : A k s),
    (law p)[(fun ω => if selected (tree := tree) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2) = ⟨s,i⟩ then (1 : ℝ) else 0) |
      historySigma (clock k) (by rw [clock_eq]; omega)] =ᵐ[law p]
      fun ω => if run (tree := tree) k hk.le
        (readPrefix (by rw [clock_eq]; omega) ω.2) = s then scheduler p k s i else 0
  result_kernel : ∀ k (hk : k < N) (s : S k) (i : A k s) (x : X k s i),
    (law p)[(fun ω => if observedEdge (tree := tree) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2) = ⟨s,i,x⟩ then (1 : ℝ) else 0) |
      historySigma (clock k+1) (by rw [clock_eq]; omega)] =ᵐ[law p]
      fun ω => if selected (tree := tree) k hk
        (readPrefix (by rw [clock_eq]; omega) ω.2) = ⟨s,i⟩ then resultRow p k s i x else 0
  terminal : ∀ {Y : Type*} [MeasurableSpace Y]
    (output : (s : S N) → H N s → Y) (summaryOutput : S N → Y),
    (∀ s h, output s h = summaryOutput s) →
    Measure.map (terminalOutput (tree := tree) summaryOutput) (law p) = sourceOutputLaw p output
  additive_price : ∀
    (label : (k : Fin N) → (Σ s : S k.val, Σ i : A k.val s, X k.val s i) → ℝ)
    (price : (k : Fin N) → (s : S k.val) → H k.val s →
      (i : A k.val s) → X k.val s i → ℝ),
    (∀ k s h i x, price k s h i x = label k ⟨s,i,x⟩) →
    (∫ ω, (∑ k : Fin N, label k (observedEdge (tree := tree) k.val k.isLt
      (readPrefix (by rw [clock_eq]; omega) ω.2))) ∂law p) =
      ∑ k : Fin N, ∑ s, ∑ h, ∑ i, ∑ x,
        (p.select k.val s h i * p.row k.val s h i x) * price k s h i x

/-- The source's independent local pasting contract admits the constructed rows;
no occupation-mass realization witness is a premise. -/
theorem summary_policy_realization (p : Flow tree K)
    (admissible : ((k : ℕ) → (s : S k) → A k s → ℝ) →
      ((k : ℕ) → (s : S k) → (i : A k s) → X k s i → ℝ) → Prop)
    (paste : ∀ sigma q,
      (∀ k, k < N → ∀ s,
        ((∀ i, 0 ≤ sigma k s i) ∧ ∑ i, sigma k s i = 1) ∧
          ∀ i, q k s i ∈ K.carrier k s i) → admissible sigma q) :
    admissible (scheduler p) (resultRow p) ∧ Realization p := by
  have hf := realized_flows p
  refine ⟨paste _ _ (fun k hk s => normalized_rows p k hk s), ?_⟩
  exact {
    probability := hf.1
    nodes := hf.2.1
    selections := hf.2.2.1
    results := hf.2.2.2
    scheduler_kernel := fun k hk s i => (full_history_kernels p k hk s i).1
    result_kernel := fun k hk s i => (full_history_kernels p k hk s i).2
    terminal := terminal_output_law p
    additive_price := expected_additive_price p }

/-- Raw branch/result/retained-child prices are preserved only under explicit
factorization through the public transition label. -/
theorem archive_expected_additive_price {atree : ArchiveTree S H A X N}
    (p : ArchiveFlow atree K)
    (label : (k : Fin N) → (Σ s : S k.val, Σ i : A k.val s, X k.val s i) → ℝ)
    (price : (k : Fin N) → (e : FineEdge (S := S) (H := H) (A := A) (X := X)
      atree.Pre atree.Post k.val) → ℝ)
    (preserved : ∀ k e, price k e = label k ⟨e.1,e.2.2.1,e.2.2.2.2.1⟩) :
    (∫ ω, (∑ k : Fin N, label k (observedEdge (tree := atree.toDynamics)
      k.val k.isLt (readPrefix (by rw [clock_eq]; omega) ω.2))) ∂law p.toFlow) =
      ∑ k : Fin N, ∑ e : FineEdge (S := S) (H := H) (A := A) (X := X)
        atree.Pre atree.Post k.val,
        p.mass (k.val+1) (atree.extend k.val k.isLt e).1
          (atree.extend k.val k.isLt e).2 * price k e := by
  classical
  rw [expected_additive_price p.toFlow label
    (fun k s _h i x => label k ⟨s,i,x⟩) (fun _ _ _ _ _ => rfl)]
  apply Finset.sum_congr rfl
  intro k _
  simp only [ArchiveFlow.toFlow, pre_weighted, Finset.sum_mul, Fintype.sum_sigma, preserved]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_mul, p.partition]

/-- Complete finite-archive realization on the single independently generated
fresh summary law, with prices evaluated on the actual compatible children. -/
structure ArchiveRealization {atree : ArchiveTree S H A X N}
    (p : ArchiveFlow atree K) : Prop extends Realization p.toFlow where
  source_selections : ∀ k (hk : k < N) (f : (Σ s : S k, A k s) → ℝ),
    (∫ ω, f (selected (tree := atree.toDynamics) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p.toFlow) =
      ∑ s, ∑ i, (∑ h, ∑ r, p.select k s h i r) * f ⟨s,i⟩
  source_results : ∀ k (hk : k < N) (f : (Σ s : S k, Σ i : A k s, X k s i) → ℝ),
    (∫ ω, f (observedEdge (tree := atree.toDynamics) k hk
      (readPrefix (by rw [clock_eq]; omega) ω.2)) ∂law p.toFlow) =
      ∑ s, ∑ i, ∑ x, (∑ h, ∑ r, p.select k s h i r * p.row k s h i r x) * f ⟨s,i,x⟩
  source_prices : ∀
    (label : (k : Fin N) → (Σ s : S k.val, Σ i : A k.val s, X k.val s i) → ℝ)
    (price : (k : Fin N) → (e : FineEdge (S := S) (H := H) (A := A) (X := X)
      atree.Pre atree.Post k.val) → ℝ),
    (∀ k e, price k e = label k ⟨e.1,e.2.2.1,e.2.2.2.2.1⟩) →
    (∫ ω, (∑ k : Fin N, label k (observedEdge (tree := atree.toDynamics)
      k.val k.isLt (readPrefix (by rw [clock_eq]; omega) ω.2))) ∂law p.toFlow) =
      ∑ k : Fin N, ∑ e : FineEdge (S := S) (H := H) (A := A) (X := X)
        atree.Pre atree.Post k.val,
        p.mass (k.val+1) (atree.extend k.val k.isLt e).1
          (atree.extend k.val k.isLt e).2 * price k e

/-- The original five sufficient conditions applied to actual finite archives:
common legal rows, public update, task factorization and independent pasting. -/
theorem archive_summary_policy_realization {atree : ArchiveTree S H A X N}
    (p : ArchiveFlow atree K)
    (admissible : ((k : ℕ) → (s : S k) → A k s → ℝ) →
      ((k : ℕ) → (s : S k) → (i : A k s) → X k s i → ℝ) → Prop)
    (paste : ∀ sigma q,
      (∀ k, k < N → ∀ s,
        ((∀ i, 0 ≤ sigma k s i) ∧ ∑ i, sigma k s i = 1) ∧
          ∀ i, q k s i ∈ K.carrier k s i) → admissible sigma q) :
    admissible (scheduler p.toFlow) (resultRow p.toFlow) ∧ ArchiveRealization p := by
  have h := summary_policy_realization p.toFlow admissible paste
  exact ⟨h.1, {
    toRealization := h.2
    source_selections := fun k hk f => by
      simpa only [selectionMass, ArchiveFlow.toFlow, preSelection] using h.2.selections k hk f
    source_results := fun k hk f => by
      simpa only [resultMass, ArchiveFlow.toFlow, pre_weighted] using h.2.results k hk f
    source_prices := archive_expected_additive_price p }⟩

#print axioms archive_expected_additive_price
#print axioms archive_summary_policy_realization

#print axioms table_laws
#print axioms probability_law
#print axioms trace_expectation
#print axioms realized_flows
#print axioms full_history_kernels
#print axioms terminal_output_law
#print axioms expected_additive_price
#print axioms summary_policy_realization
end D5.S3.Estimation.DataProcessing.FiniteSummaryInnovations
