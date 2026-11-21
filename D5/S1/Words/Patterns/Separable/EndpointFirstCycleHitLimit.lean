/- GID: D5/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointFirstCycleHitLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed prefixes of actual emitted cycles converge in literal diagonal-hit probability to the marked stream law. -/

import D5.S1.Words.Patterns.Separable.EndpointCanonicalCycle
import Mathlib.MeasureTheory.Measure.Real

namespace D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit

open ActualCycles ActualCycleLaw CutFactorization MinimumCutKernel
open EndpointCycleHazard (hit)
open EndpointCanonicalCycle
open Set MeasureTheory Filter Topology
open scoped BigOperators

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S1.Words.Patterns.Separable.ActualCycles
open D5.S1.Words.Patterns.Separable.ActualCycleLaw
open D5.S1.Words.Patterns.Separable.CutFactorization (Avoider)
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.OccupiedComparison (rho)
open Filter Topology MeasureTheory Set Classical
open scoped BigOperators ENNReal

private theorem cycleEraseInjective (K H : ℕ) (s : Bool) :
    Function.Injective (Cycle.erase (K := K) (H := H) (sign := s)) := by
  induction H generalizing s with
  | zero =>
    intro x
    exact nomatch x
  | succ H ih =>
    intro x y h
    change SmallJ K s ⊕ (SmallU K × Cycle K (!s) H) at x y
    rcases x with ⟨i, a⟩ | ⟨⟨i, a⟩, x⟩ <;>
      rcases y with ⟨j, b⟩ | ⟨⟨j, b⟩, y⟩ <;>
      simp only [Cycle.erase] at h
    · obtain ⟨hij, hab⟩ := UnboundedCycle.terminal.inj h
      obtain rfl : i = j := Fin.ext hij
      obtain rfl : a = b := eq_of_heq hab
      rfl
    · cases h
    · cases h
    · obtain ⟨hij, hab, hxy⟩ := UnboundedCycle.discard.inj h
      obtain rfl : i = j := Fin.ext hij
      obtain rfl : a = b := eq_of_heq hab
      obtain rfl : x = y := ih (!s) hxy
      rfl

private theorem tupleEraseInjective (K H k : ℕ) :
    Function.Injective (Tuple.erase (K := K) (H := H) (k := k)) := by
  induction k with
  | zero => intro x y _; exact @Subsingleton.elim Unit _ x y
  | succ k ih =>
    intro x y h
    rcases x with ⟨⟨s, c⟩, u⟩
    rcases y with ⟨⟨t, d⟩, v⟩
    change ((⟨s, c.erase⟩, u.erase) : UnboundedTuple (k + 1)) =
      (⟨t, d.erase⟩, v.erase) at h
    obtain ⟨head, tail⟩ := Prod.mk.inj h
    obtain ⟨hst, hcd⟩ := Sigma.mk.inj_iff.mp head
    subst t
    obtain rfl : c = d := cycleEraseInjective K H s (eq_of_heq hcd)
    obtain rfl : u = v := ih tail
    rfl

private theorem streamCylindersDisjoint (k : ℕ) :
    Pairwise (fun (u v : UnboundedTuple k) => Disjoint (Prefix.cylinder u) (Prefix.cylinder v)) := by
  intro u v hne
  refine Set.disjoint_left.mpr (fun ω hu hv => hne ?_)
  apply (actual_countable_cycle_law.2.2.1 k).1
  funext i
  exact (hu i).symm.trans (hv i)

local instance (n : ℕ) : MeasurableSpace (Avoider n) := ⊤
local instance (n : ℕ) : Nonempty (Avoider n) := ⟨identityAvoider n⟩
local instance (n : ℕ) : MeasurableSingletonClass (Avoider n) := ⟨fun _ => trivial⟩

private noncomputable def finiteLaw (n : ℕ) : Measure (Avoider n) :=
  (uniformPmf (Avoider n)).toMeasure

local instance (n : ℕ) : IsProbabilityMeasure (finiteLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (uniformPmf (Avoider n)).toMeasure)

private theorem actualMass_eq_real (n : ℕ) (P : Avoider n → Prop) :
    actualMass n P = (finiteLaw n).real {x | P x} := by
  unfold actualMass finiteLaw Measure.real
  rw [PMF.toMeasure_apply_eq_toOuterMeasure]

private theorem selected_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (A S B : Set α)
    (hS : B = A ∩ S) :
    dist (μ.real A) (μ.real B) ≤ μ.real Sᶜ := by
  subst B
  have h₁ : μ.real (A ∩ S) ≤ μ.real A := measureReal_mono inter_subset_left
  have h₂ : A ⊆ (A ∩ S) ∪ Sᶜ := by
    intro x hx
    by_cases h : x ∈ S
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  have h₃ := (measureReal_mono (μ := μ) h₂).trans (measureReal_union_le (μ := μ) _ _)
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h₁)]
  linarith

private theorem streamCylMass {k : ℕ} (p : UnboundedTuple k) :
    streamMeasure.real (Prefix.cylinder p) = rho ^ p.size := by
  have hr : 0 ≤ rho := by unfold rho; exact sq_nonneg _
  rw [Measure.real, (actual_countable_cycle_law.2.2.2.2.2.1 k p).2,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]


private theorem finiteCylindersDisjoint {K H k n : ℕ} (big : Tuple.threshold K H k < n) :
    Pairwise (fun (u v : Tuple K H k) =>
      Disjoint {π | u.Event n big π} {π | v.Event n big π}) := by
  intro u v hne
  exact Set.disjoint_left.mpr (fun π hu hv =>
    hne (actual_complete_cycles.1 K H k n big u v π hu hv))

private theorem window_mass_limit {K H k : ℕ} (I : Type)
    [Fintype I] (i : I → Tuple K H k) (hi : Function.Injective i) :
    Tendsto (fun n => ∑ j : I, (i j).probability n) atTop
      (𝓝 (streamMeasure.real (⋃ j : I, Prefix.cylinder (i j).erase))) := by
  have hdisj : Pairwise (fun j l : I =>
      Disjoint (Prefix.cylinder (i j).erase) (Prefix.cylinder (i l).erase)) :=
    fun j l hne => streamCylindersDisjoint k
      (fun h => hne (hi (tupleEraseInjective K H k h)))
  rw [measureReal_iUnion_fintype hdisj
    (fun j => (actual_countable_cycle_law.2.2.2.2.2.1 k (i j).erase).1)]
  simp only [streamCylMass, Tuple.erase_size]
  exact tendsto_finsetSum Finset.univ (fun j _ => actual_complete_cycles.2.2.1 K H k (i j))

private theorem finite_window_mass {K H k n : ℕ} (big : Tuple.threshold K H k < n)
    (I : Type) [Fintype I] (i : I → Tuple K H k) (hi : Function.Injective i) :
    (finiteLaw n).real (⋃ j : I, {π | (i j).Event n big π}) =
      ∑ j : I, (i j).probability n := by
  have hdisj : Pairwise (fun j l : I =>
      Disjoint {π | (i j).Event n big π} {π | (i l).Event n big π}) :=
    fun j l hne => finiteCylindersDisjoint big (fun h => hne (hi h))
  rw [measureReal_iUnion_fintype hdisj (fun j => show MeasurableSet _ from trivial)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← actualMass_eq_real, Tuple.probability, dite_eq_left big]

private theorem failure_eq_compl_window {K H k n : ℕ} (big : Tuple.threshold K H k < n) :
    {π | Failed K H k n π} = (⋃ p : Tuple K H k, {π | p.Event n big π})ᶜ := by
  ext π
  simp [Failed, Success, big]

private theorem stream_failure_limit (K H k : ℕ) :
    Tendsto (fun n => actualMass n (Failed K H k n)) atTop
      (𝓝 (streamMeasure.real (⋃ p : Tuple K H k, Prefix.cylinder p.erase)ᶜ)) := by
  have heq : (fun n => actualMass n (Failed K H k n)) =ᶠ[atTop]
      (fun n => 1 - ∑ p : Tuple K H k, p.probability n) := by
    filter_upwards [Filter.eventually_gt_atTop (Tuple.threshold K H k)] with n big
    rw [actualMass_eq_real, failure_eq_compl_window big,
      measureReal_compl (show MeasurableSet (⋃ p : Tuple K H k, {π | p.Event n big π}) from trivial)]
    rw [show (finiteLaw n).real (⋃ p : Tuple K H k, {π | p.Event n big π}) =
      ∑ p : Tuple K H k, p.probability n by
        simpa only [id_eq] using finite_window_mass big (Tuple K H k) id Function.injective_id]
    simp [Measure.real]
  rw [measureReal_compl (MeasurableSet.iUnion
    (fun p : Tuple K H k => (actual_countable_cycle_law.2.2.2.2.2.1 k p.erase).1))]
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, id_eq] using
    (tendsto_const_nhds.sub (window_mass_limit (Tuple K H k) id Function.injective_id)).congr' heq.symm

/-- Local parser agreement on successful finite tuple events suffices. Nothing is
assumed about the finite target event on failed parses, or about probabilities
conditioned on a successful parse. -/
private theorem actual_parser_limit_of_successful_agreement (k : ℕ) (Q : UnboundedTuple k → Prop)
    (A : (n : ℕ) → Avoider n → Prop)
    (agree : ∀ K H : ℕ, ∀ᶠ n in atTop,
      ∀ (big : Tuple.threshold K H k < n) (p : Tuple K H k) (π : Avoider n),
        p.Event n big π → (A n π ↔ Q p.erase)) :
    Tendsto (fun n => actualMass n (A n)) atTop
      (𝓝 (streamMeasure.real (⋃ p : {p : UnboundedTuple k // Q p}, Prefix.cylinder p.val))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, H, N, hN⟩ :=
    actual_complete_cycles.2.2.2.2.2.2.1 k (ε / 3) (by linarith)
  let T := Tuple K H k
  let I := {p : T // Q p.erase}
  let J := ⋃ p : T, Prefix.cylinder p.erase
  let C := ⋃ p : I, Prefix.cylinder p.val.erase
  let limitEvent := ⋃ p : {p : UnboundedTuple k // Q p}, Prefix.cylinder p.val
  let g (n : ℕ) := ∑ p : I, p.val.probability n
  have hC : C = limitEvent ∩ J := by
    ext ω
    simp only [C, limitEvent, J, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨⟨⟨p.val.erase, p.property⟩, hp⟩, ⟨p.val, hp⟩⟩
    · rintro ⟨⟨p, hp⟩, q, hq⟩
      have eq : p.val = q.erase := by
        apply (actual_countable_cycle_law.2.2.1 k).1
        funext i
        exact (hp i).symm.trans (hq i)
      exact ⟨⟨q, eq ▸ p.property⟩, hq⟩
  have hfail : ∀ᶠ n in atTop, actualMass n (Failed K H k n) < ε / 3 :=
    Filter.eventually_atTop.mpr ⟨N, hN⟩
  have hJ : streamMeasure.real Jᶜ ≤ ε / 3 :=
    le_of_tendsto (stream_failure_limit K H k) (hfail.mono (fun _ hn => hn.le))
  have hs : dist (streamMeasure.real limitEvent) (streamMeasure.real C) ≤ ε / 3 :=
    (selected_bound streamMeasure limitEvent J C hC).trans hJ
  have hg := (Metric.tendsto_nhds.mp
    (window_mass_limit I Subtype.val Subtype.val_injective)) (ε / 3) (by linarith)
  filter_upwards [hfail, hg, agree K H, Filter.eventually_gt_atTop (Tuple.threshold K H k)]
    with n hf hgn ha big
  have hselect :
      (⋃ p : I, {π | p.val.Event n big π}) =
        {π | A n π} ∩ (⋃ p : T, {π | p.Event n big π}) := by
    ext π
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨(ha big p.val π hp).mpr p.property, ⟨p.val, hp⟩⟩
    · rintro ⟨hA, p, hp⟩
      exact ⟨⟨p, (ha big p π hp).mp hA⟩, hp⟩
  have hn : dist (actualMass n (A n)) (g n) < ε / 3 := by
    change dist (actualMass n (A n)) (∑ p : I, p.val.probability n) < ε / 3
    rw [actualMass_eq_real n (A n), ← finite_window_mass big I Subtype.val Subtype.val_injective]
    apply lt_of_le_of_lt (selected_bound (finiteLaw n) _ _ _ hselect)
    rwa [← failure_eq_compl_window big, ← actualMass_eq_real]
  have h₁ := dist_triangle (actualMass n (A n)) (g n) (streamMeasure.real limitEvent)
  have h₂ := dist_triangle (g n) (streamMeasure.real C) (streamMeasure.real limitEvent)
  rw [dist_comm (streamMeasure.real C)] at h₂
  change dist (g n) (streamMeasure.real C) < ε / 3 at hgn
  change dist (actualMass n (A n)) (streamMeasure.real limitEvent) < ε
  linarith


/-- The increment before reading mark j, with no contribution from mark j. -/
def streamDiscrepancy (j : ℕ) (ω : Stream) : ℤ :=
  ∑ i : Fin j, discrepancyDelta (ω i.val).2

/-- A hit in one of the first k actual marked cycles, evaluated at the
incoming offset plus the advances of exactly its preceding marks. -/
def firstKHit (k : ℕ) (e : ℤ) : Set Stream :=
  {ω | ∃ j < k, hit (ω j).2 (e + streamDiscrepancy j ω)}

private def shift (ω : Stream) : Stream := fun j => ω (j + 1)

private theorem streamDiscrepancy_succ (j : ℕ) (ω : Stream) :
    streamDiscrepancy (j+1) ω =
      discrepancyDelta (ω 0).2 + streamDiscrepancy j (shift ω) := by
  unfold streamDiscrepancy shift
  rw [Fin.sum_univ_succ]
  rfl

private theorem firstKHit_succ (k : ℕ) (e : ℤ) (ω : Stream) :
    ω ∈ firstKHit (k+1) e ↔
      hit (ω 0).2 e ∨ shift ω ∈ firstKHit k (e + discrepancyDelta (ω 0).2) := by
  change (∃ j < k+1, hit (ω j).2 (e + streamDiscrepancy j ω)) ↔
    hit (ω 0).2 e ∨ ∃ j < k, hit (shift ω j).2
      ((e + discrepancyDelta (ω 0).2) + streamDiscrepancy j (shift ω))
  constructor
  · rintro ⟨j, hj, h⟩
    cases j with
    | zero => exact Or.inl (by simpa [streamDiscrepancy] using h)
    | succ j =>
      refine Or.inr ⟨j, by omega, ?_⟩
      simpa only [streamDiscrepancy_succ, shift, add_assoc] using h
  · rintro (h | ⟨j, hj, h⟩)
    · exact ⟨0, by omega, by simpa [streamDiscrepancy] using h⟩
    · refine ⟨j+1, by omega, ?_⟩
      simpa only [streamDiscrepancy_succ, shift, add_assoc] using h

private theorem on_cylinder {k : ℕ} (p : UnboundedTuple k) (e : ℤ)
    (ω : Stream) (h : ω ∈ Prefix.cylinder p) :
    ω ∈ firstKHit k e ↔ tupleHits p e := by
  induction k generalizing e ω with
  | zero => simp [firstKHit, tupleHits]
  | succ k ih =>
    have hhead : ω 0 = p.1 := h (0 : Fin (k+1))
    have htail : shift ω ∈ Prefix.cylinder p.2 := by
      intro i
      exact h i.succ
    rw [firstKHit_succ, ih p.2 (e + discrepancyDelta (ω 0).2) (shift ω) htail, hhead]
    rfl

/-- Identifies exactly the cylinder event in the ε/3 complement bridge,
at every integer initial discrepancy and every natural number of cycles. -/
private theorem hit_cylinder_union (k : ℕ) (e : ℤ) :
    (⋃ p : {p : UnboundedTuple k // tupleHits p e}, Prefix.cylinder p.val) =
      firstKHit k e := by
  ext ω
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, h⟩
    exact (on_cylinder p.val e ω h).mpr p.property
  · intro h
    obtain ⟨p, hp⟩ := (actual_countable_cycle_law.2.2.1 k).2
      (fun i : Fin k => ω i.val)
    have hc : ω ∈ Prefix.cylinder p := fun i => (congrFun hp i).symm
    exact ⟨⟨p, (on_cylinder p e ω hc).mp h⟩, hc⟩


/-- Probability of a hit in the first k marks of the actual stream. -/
noncomputable def firstKHitProbability (k : ℕ) (e : ℤ) : ℝ :=
  streamMeasure.real (firstKHit k e)

/-- For fixed k and e, the original emitted-coordinate hit probability of
finite avoiding permutations converges to the actual marked-stream hit law. -/
theorem actualCanonicalFirstKLiteralHit_limit (k : ℕ) (e : ℤ) :
    Tendsto (fun n => actualMass n (actualCanonicalFirstKLiteralHit k e n)) atTop
      (𝓝 (firstKHitProbability k e)) := by
  rw [firstKHitProbability, ← hit_cylinder_union]
  exact actual_parser_limit_of_successful_agreement k (fun p => tupleHits p e)
    (actualCanonicalFirstKLiteralHit k e) (actualCanonicalFirstKLiteralHit_eventually_agrees k e)

end D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
