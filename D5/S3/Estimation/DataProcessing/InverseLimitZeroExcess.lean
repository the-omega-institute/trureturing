/- GID: D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/InverseLimitZeroExcess
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common cut identifies zero excess on threads with zero excess at every level. -/

import D5.S3.Estimation.DataProcessing.OneCutZeroExcess

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.InverseLimitZeroExcess

universe u

open Set Function MeasureTheory
open scoped ENNReal
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
open D5.S3.Estimation.DataProcessing.OneCutZeroExcess

/-- Coordinatewise action of compatible permutations on the actual thread space. -/
def threadEquiv {B : ℕ → Type u} (q : (l : ℕ) → B (l + 1) → B l)
    (g : (l : ℕ) → B l ≃ B l)
    (hg : ∀ l x, q l (g (l + 1) x) = g l (q l x)) : Thread B q ≃ Thread B q where
  toFun x := ⟨fun l => g l (x.val l), fun l => by rw [hg, x.property]⟩
  invFun x := ⟨fun l => (g l).symm (x.val l), fun l => by
    apply (g l).injective
    rw [← hg, Equiv.apply_symm_apply, x.property, Equiv.apply_symm_apply]⟩
  left_inv x := by apply Subtype.ext; funext l; exact (g l).symm_apply_apply _
  right_inv x := by apply Subtype.ext; funext l; exact (g l).apply_symm_apply _

/-- The nonnegative excess of the cycle failure count over its forced failure. -/
noncomputable def cycleExcess {B : Type*} {n : ℕ} (g : B ≃ B)
    (y : Fin (n + 1) → B) : ℕ := failureCount g y - movingAnchor g y

/-- Zero excess on the completed tuple is equivalent to zero excess at every
finite level. The proof obtains one common cut; cuts at different levels are
not chosen independently in the conclusion. -/
theorem zero_excess_iff_all_levels {B : ℕ → Type u}
    (q : (l : ℕ) → B (l + 1) → B l) (g : (l : ℕ) → B l ≃ B l)
    (hg : ∀ l x, q l (g (l + 1) x) = g l (q l x))
    {n : ℕ} (y : Fin (n + 1) → Thread B q) :
    (cycleExcess (threadEquiv q g hg) y = 0 ↔
      ∀ l, cycleExcess (g l) (levelProjection q (n + 1) l y) = 0) ∧
    (y ∈ oneCutSet (threadEquiv q g hg) ↔
      ∀ l, levelProjection q (n + 1) l y ∈ oneCutSet (g l)) := by
  classical
  have hinv (l : ℕ) (x : B (l + 1)) :
      q l ((g (l + 1)).symm x) = (g l).symm (q l x) := by
    apply (g l).injective
    rw [← hg, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hsupport : y ∈ oneCutSet (threadEquiv q g hg) ↔
      ∀ l, levelProjection q (n + 1) l y ∈ oneCutSet (g l) := by
    constructor
    · rintro ⟨k, hy⟩ l
      refine ⟨k, funext fun j => ?_⟩
      have hj := congrArg (fun z => (z j).val l) hy
      by_cases h : j ≤ k <;> simpa [cutTuple, levelProjection, h, threadEquiv] using hj
    · intro hy
      let K (l : ℕ) : Set (Fin (n + 1)) :=
        {k | ∀ j, (y j).val l = cutTuple (g l) k ((y 0).val l) j}
      have hK (l : ℕ) : (K l).Nonempty := by
        obtain ⟨k, hk⟩ := hy l
        exact ⟨k, fun j => congrFun hk j⟩
      have hdecr (l : ℕ) : K (l + 1) ⊆ K l := by
        intro k hk j
        have h := congrArg (q l) (hk j)
        simpa only [cutTuple, apply_ite, (y j).property l, (y 0).property l, hinv] using h
      let : TopologicalSpace (Fin (n + 1)) := ⊥
      have : DiscreteTopology (Fin (n + 1)) := ⟨rfl⟩
      obtain ⟨k, hk⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        K hdecr hK (Set.toFinite (K 0)).isCompact (fun l => (Set.toFinite (K l)).isClosed)
      refine ⟨k, funext fun j => Subtype.ext (funext fun l => ?_)⟩
      have h := mem_iInter.mp hk l j
      by_cases hjk : j ≤ k <;> simpa [cutTuple, hjk, threadEquiv] using h
  refine ⟨?_, hsupport⟩
  have zero {A : Type u} (e : A ≃ A) (z : Fin (n + 1) → A) :
      cycleExcess e z = 0 ↔ z ∈ oneCutSet e := by
    have h := failure_count_equality_iff_one_cut e z
    exact (Nat.sub_eq_zero_iff_le.trans ⟨fun hz => le_antisymm hz h.1,
      fun hz => hz.le⟩).trans h.2
  exact (zero _ _).trans (hsupport.trans (forall_congr' fun l => (zero _ _).symm))

/-- Expected excess vanishes on a Borel law of tuples of threads exactly when
it vanishes on every actual finite projection. This does not assert monotonicity
of the excess itself. -/
theorem expected_excess_zero_iff_all_levels {B : ℕ → Type u}
    [∀ l, Finite (B l)] [∀ l, TopologicalSpace (B l)] [∀ l, DiscreteTopology (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, BorelSpace (B l)]
    (q : (l : ℕ) → B (l + 1) → B l) (g : (l : ℕ) → B l ≃ B l)
    (hg : ∀ l x, q l (g (l + 1) x) = g l (q l x)) (n : ℕ)
    (Q : Measure (Fin (n + 1) → Thread B q)) :
    (∫⁻ y, (cycleExcess (threadEquiv q g hg) y : ℝ≥0∞) ∂Q) = 0 ↔
      ∀ l, (∫⁻ y, (cycleExcess (g l) y : ℝ≥0∞)
        ∂Q.map (levelProjection q (n + 1) l)) = 0 := by
  classical
  have : SecondCountableTopology ((l : ℕ) → B l) := inferInstance
  have : SecondCountableTopology (Thread B q) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : BorelSpace ((l : ℕ) → B l) := inferInstance
  have : BorelSpace (Thread B q) := inferInstance
  have hm {A : Type u} [MeasurableSpace A] [MeasurableEq A]
      (e : A ≃ A) (he : Measurable e) :
      Measurable (fun y : Fin (n + 1) → A => (cycleExcess e y : ℝ≥0∞)) := by
    have hi : Measurable (fun y : Fin (n + 1) → A => (internalFailures y).card) := by
      simp only [internalFailures, Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.measurable_sum _ fun i _ =>
        Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i.castSucc)
          (measurable_pi_apply i.succ)).compl measurable_const measurable_const
    have hc : Measurable (failureCount e : (Fin (n + 1) → A) → ℕ) :=
      hi.add (Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 0)
        (he.comp (measurable_pi_apply (Fin.last n)))) measurable_const measurable_const)
    have hb : Measurable (movingAnchor e : (Fin (n + 1) → A) → ℕ) :=
      Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 0)
        (he.comp (measurable_pi_apply 0))) measurable_const measurable_const
    exact (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp (hc.sub hb)
  have hgThread : Measurable (threadEquiv q g hg) := by
    apply Measurable.subtype_mk
    exact measurable_pi_lambda _ fun l =>
      (measurable_of_countable (g l)).comp
        ((measurable_pi_apply l).comp measurable_subtype_coe)
  have hπ (l : ℕ) : Measurable (levelProjection q (n + 1) l) := by
    exact measurable_pi_lambda _ fun j =>
      (measurable_pi_apply l).comp (measurable_subtype_coe.comp (measurable_pi_apply j))
  rw [lintegral_eq_zero_iff (hm _ hgThread)]
  simp only [Filter.EventuallyEq, Pi.zero_apply, Nat.cast_eq_zero]
  simp_rw [lintegral_eq_zero_iff (hm _ (measurable_of_countable _)),
    Filter.EventuallyEq, Pi.zero_apply, Nat.cast_eq_zero,
    ae_map_iff (hπ _).aemeasurable ((Set.toFinite _).measurableSet)]
  rw [← ae_all_iff]
  exact Filter.eventually_congr (Filter.Eventually.of_forall fun y =>
    (zero_excess_iff_all_levels q g hg y).1)

#print axioms zero_excess_iff_all_levels
#print axioms expected_excess_zero_iff_all_levels

end D5.S3.Estimation.DataProcessing.InverseLimitZeroExcess
