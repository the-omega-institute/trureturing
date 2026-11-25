/- GID: D5/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/CayleyColoring/FiniteProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pushing forward complete marked words identifies the source count with the independent occupancy law. -/

import D5.S3.Combinatorics.Graph.CayleyColoring.FiniteLaw
import D5.S3.Analytic.Probability.DiscardedOccupancy.NormalLimit
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.IdentDistrib

section

open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace CayleyTreeProbability

noncomputable section

/-- The uniform law on a finite discrete sample. -/
def uniform (X : Type*) [Finite X] [MeasurableSpace X] : Measure X :=
  let := Fintype.ofFinite X
  Measure.uniformOfFinset Finset.univ

private theorem uniform_apply {X : Type*} [Finite X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (s : Set X) :
    uniform X s = (Nat.card s : ℝ≥0∞) / Nat.card X := by
  classical
  let := Fintype.ofFinite X
  change Measure.uniformOfFinset (Finset.univ : Finset X) s = _
  rw [Measure.uniformOfFinset_apply, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  congr 2
  exact (Fintype.card_subtype (fun x => x ∈ s)).symm

instance instIsProbabilityMeasureUniformOfNonemptyOfMeasurableSingletonClass {X : Type*} [Finite X] [Nonempty X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : IsProbabilityMeasure (uniform X) := by
  constructor
  rw [uniform_apply, Nat.card_congr (Equiv.Set.univ X)]
  exact ENNReal.div_self (by exact_mod_cast Nat.card_pos.ne') (by simp)

private theorem uniform_map_atom {X Y : Type*} [Finite X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : X → Y) (y : Y) :
    (uniform X).map f {y} = (Nat.card {x : X // f x = y} : ℝ≥0∞) / Nat.card X := by
  rw [Measure.map_apply (measurable_of_countable f) (measurableSet_singleton y), uniform_apply]
  rfl

private theorem uniform_map_equiv {X Y : Type*} [Finite X] [Finite Y] [MeasurableSpace X]
    [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSingletonClass Y] (e : X ≃ Y) :
    (uniform X).map e = uniform Y := by
  apply Measure.ext_of_singleton
  intro y
  let : Subsingleton {x // e x = y} :=
    ⟨fun x z => Subtype.ext (e.injective (x.prop.trans z.prop.symm))⟩
  rw [uniform_map_atom, uniform_apply, Nat.card_congr e,
    Nat.card_of_subsingleton (⟨e.symm y, e.apply_symm_apply y⟩ : {x // e x = y}),
    Nat.card_of_subsingleton (⟨y, rfl⟩ : ({y} : Set Y))]

private theorem uniform_singleton {X : Type*} [Finite X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (x : X) :
    uniform X {x} = (Nat.card X : ℝ≥0∞)⁻¹ := by
  rw [uniform_apply, Nat.card_of_subsingleton (⟨x, rfl⟩ : ({x} : Set X))]
  simp

private theorem uniform_words (I X : Type*) [Fintype I] [Finite X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] :
    uniform (I → X) = Measure.pi (fun _ : I => uniform X) := by
  classical
  let := Fintype.ofFinite X
  apply Measure.ext_of_singleton
  intro x
  rw [uniform_singleton, Measure.pi_singleton]
  simp only [uniform_singleton, Finset.prod_const, Finset.card_univ,
    Nat.card_eq_fintype_card, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

open CayleyFiniteLaw DiscardedOccupancy

private theorem microstate_bin_law {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    [NeZero k] :
    (uniform (Fin n × ZMod k)).map bin =
      (throwPMF hn (palette_bounds hk).1.le (palette_bounds hk).2.le).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  have hc : Nat.card (Fin n × ZMod k) = n * k := by
    rw [Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card (α := ZMod k), ZMod.card]
  rw [uniform_map_atom, hc]
  cases b with
  | none =>
      rw [bin_none_card, Nat.card_fin, cardinality_nonzero, (palette_throw_mass hn hk).1]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_div_of_pos (by positivity : 0 < ((n * k : ℕ) : ℝ))]
      congr 1
      push_cast [Nat.cast_sub (show 1 ≤ k by omega)]
      field_simp
  | some v =>
      rw [bin_some_card, (palette_throw_mass hn hk).2 v,
        ENNReal.ofReal_div_of_pos (by positivity : 0 < (k : ℝ) * n)]
      rw [Nat.cast_mul, ENNReal.ofReal_mul (by positivity : 0 ≤ (k : ℝ))]
      simp [mul_comm]

/-- Apply the bin map coordinatewise to a uniform microstate word. The entire resulting
word has the independent discard-and-bin law, including the empty word. -/
theorem microstate_word_law {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) [NeZero k] (m : ℕ) :
    (uniform (Fin m → Fin n × ZMod k)).map (fun w i => bin (w i)) = literalMeasure hn hk m := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbin := microstate_bin_law hn hk
  let (i : Fin m) : IsProbabilityMeasure ((uniform (Fin n × ZMod k)).map
      (fun x : Fin n × ZMod k => bin x)) := by rw [hbin]; infer_instance
  rw [uniform_words, Measure.pi_map_pi (fun _ => (measurable_of_countable bin).aemeasurable)]
  simp only [microstate_bin_law hn hk, literalMeasure]

end
end CayleyTreeProbability

end

section

open scoped BigOperators ENNReal ProbabilityTheory Topology
open Filter MeasureTheory ProbabilityTheory

namespace CayleyTreeProbability

noncomputable section

open CayleyColors CayleyExactAudit CayleyFiniteLaw CayleyNativeLaw CayleyParent CayleyProbe CayleyReduction
  CayleyScheduler DiscardedOccupancy

universe u

abbrev SourceSample (n k : ℕ) := Equiv.Perm (Fin n) × Colored (Fin n) (ZMod k)

scoped instance permutationMeasurableSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
scoped instance permutationMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (Equiv.Perm (Fin n)) := ⟨fun _ => trivial⟩

scoped instance treeMeasurableSpace (n : ℕ) : MeasurableSpace (CayleyProbe.Tree (Fin n)) := ⊤
scoped instance treeMeasurableSingleton (n : ℕ) :
    MeasurableSingletonClass (CayleyProbe.Tree (Fin n)) := ⟨fun _ => trivial⟩

/-- The discrete sampling law for the uniform ranking, rooted labeled tree and initial colors. -/
def sourceMeasure (n k : ℕ) [NeZero k] : Measure (SourceSample n k) :=
  uniform _

/-- The mass of an actual move count is the total sequential-history numerator divided by
the number of equally likely input and ranking draws. -/
private theorem source_count_atom {n k : ℕ} [NeZero k] {K : Type u} (embed : ZMod k ↪ K)
    (policy : (s : Colored (Fin n) (ZMod k)) → FreePolicy (K := K) s.1.2.val) (j : ℕ) :
    (sourceMeasure n k).map (sourceCount embed) {j} =
      (Nat.card (TotalNumerator embed policy j) : ℝ≥0∞) / Nat.card (SourceSample n k) := by
  rw [sourceMeasure, uniform_map_atom, Nat.card_congr (totalEquiv embed policy j)]

/-- Reindexing the non-anchor coordinates to times preserves each visited ordinary bin. -/
private theorem reindexed_count {n k : ℕ} {a : Fin n} (e : Fin (n - 1) ≃ Away a)
    (t : Throws a (ZMod k)) :
    (occupied t : ℝ) =
      literalCount n (n - 1) (fun i => bin (t (e i))) := by
  classical
  change (filterCard (fun v : Fin n => ∃ i, bin (t i) = some v) : ℝ) = _
  have h : (fun v : Fin n => ∃ i, bin (t i) = some v) =
      (fun v : Fin n => ∃ j, bin (t (e j)) = some v) := by
    funext v
    apply propext
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa using hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, hj⟩
  rw [h]
  unfold filterCard literalCount
  congr 2
  ext v
  simp

/-- The source count and the ordinary occupancy count are identically distributed at every
positive size, with the probabilities of the source obtained from legal sequential histories. -/
theorem source_occupancy_law {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k) [NeZero k]
    {K : Type u} (embed : ZMod k ↪ K)
    (policy : (s : Colored (Fin n) (ZMod k)) → FreePolicy (K := K) s.1.2.val) :
    IdentDistrib (fun s : SourceSample n k => (sourceCount embed s : ℝ))
      (literalCount n (n - 1)) (sourceMeasure n k) (literalMeasure hn hk (n - 1)) := by
  let a : Fin n := ⟨0, hn⟩
  have hfinite (j : ℕ) := native_daemon_occupancy n k hn hk embed policy j
  have hcard : Nat.card (Away a) = n - 1 := (hfinite 0).2.2.2.1
  let := Fintype.ofFinite (Away a)
  let e : Fin (n - 1) ≃ Away a :=
    (Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := Away a)).symm.trans hcard)).symm
  let E : Throws a (ZMod k) ≃ (Fin (n - 1) → Fin n × ZMod k) :=
    Equiv.arrowCongr e.symm (Equiv.refl _)
  let W : (Fin (n - 1) → Fin n × ZMod k) → (Fin (n - 1) → Option (Fin n)) :=
    fun t i => bin (t i)
  let X : SourceSample n k → ℕ := sourceCount embed
  let Y : Throws a (ZMod k) → ℕ := occupied
  have hxy : IdentDistrib X Y (sourceMeasure n k) (uniform (Throws a (ZMod k))) := by
    refine ⟨(measurable_of_countable X).aemeasurable, (measurable_of_countable Y).aemeasurable, ?_⟩
    apply Measure.ext_of_singleton
    intro j
    have h := hfinite j
    change Nat.card (TotalNumerator embed policy j) * Nat.card (Throws a (ZMod k)) =
      frequency (Throws a (ZMod k)) occupied j * Nat.card (SourceSample n k) ∧ _ at h
    rw [show X = sourceCount embed from rfl, source_count_atom embed policy, uniform_map_atom]
    have ha : (Nat.card (Throws a (ZMod k)) : ℝ≥0∞) ≠ 0 := by exact_mod_cast h.2.2.1.ne'
    have hb : (Nat.card (SourceSample n k) : ℝ≥0∞) ≠ 0 := by exact_mod_cast h.2.1.ne'
    rw [ENNReal.div_eq_div_iff ha (ENNReal.natCast_ne_top _) hb (ENNReal.natCast_ne_top _)]
    simpa only [frequency, Y, Nat.cast_mul, mul_comm] using
      congrArg (fun x : ℕ => (x : ℝ≥0∞)) h.1
  have hcoord : (uniform (Throws a (ZMod k))).map (W ∘ E) = literalMeasure hn hk (n - 1) := by
    rw [← Measure.map_map (measurable_of_countable W) (measurable_of_countable E),
      uniform_map_equiv E]
    exact microstate_word_law hn hk (n - 1)
  have hreal := hxy.comp (u := fun j : ℕ => (j : ℝ)) (measurable_of_countable _)
  refine ⟨hreal.aemeasurable_fst, (measurable_of_countable _).aemeasurable, ?_⟩
  refine hreal.map_eq.trans ?_
  have heq : (fun j : ℕ => (j : ℝ)) ∘ Y = literalCount n (n - 1) ∘ (W ∘ E) :=
    funext (reindexed_count e)
  rw [heq, ← Measure.map_map (measurable_of_countable (literalCount n (n - 1)))
    (measurable_of_countable (W ∘ E)), hcoord]

end
end CayleyTreeProbability

end
