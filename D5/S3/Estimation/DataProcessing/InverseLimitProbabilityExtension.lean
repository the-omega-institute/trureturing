/- GID: D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatible finite joint laws extend uniquely to Borel laws on tuples of threads. -/

import D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
import Mathlib.MeasureTheory.Measure.Prokhorov

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension

open MeasureTheory Set Function
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- Every compatible family of finite joint laws has a unique probability extension
on the actual finite tuple of inverse-limit threads. Carrier maps are
surjective; no surjectivity of a restricted feasible-law map is assumed. -/
theorem exists_unique_probability_extension
    {B : ℕ → Type*} [∀ l, Finite (B l)] [∀ l, Nonempty (B l)]
    [∀ l, TopologicalSpace (B l)] [∀ l, DiscreteTopology (B l)]
    [∀ l, MeasurableSpace (B l)] [∀ l, BorelSpace (B l)]
    (q : (l : ℕ) → B (l + 1) → B l) (hq : ∀ l, Surjective (q l)) (n : ℕ)
    (Q : (l : ℕ) → ProbabilityMeasure (Fin n → B l))
    (hQ : ∀ l, (Q (l + 1) : Measure (Fin n → B (l + 1))).map
      (fun y j => q l (y j)) = (Q l : Measure (Fin n → B l))) :
    ∃! μ : ProbabilityMeasure (Fin n → Thread B q),
      ∀ l, (μ : Measure (Fin n → Thread B q)).map (levelProjection q n l) =
        (Q l : Measure (Fin n → B l)) := by
  classical
  let X := Fin n → Thread B q
  have hclosed : IsClosed {x : (l : ℕ) → B l | ∀ l, q l (x (l + 1)) = x l} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun l => isClosed_eq ?_ (continuous_apply l)
    exact (continuous_of_discreteTopology (f := q l)).comp (continuous_apply (l + 1))
  have : CompactSpace (Thread B q) := isCompact_iff_compactSpace.mp hclosed.isCompact
  have : SecondCountableTopology ((l : ℕ) → B l) := inferInstance
  have : SecondCountableTopology (Thread B q) :=
    TopologicalSpace.Subtype.secondCountableTopology
      {x : (l : ℕ) → B l | ∀ l, q l (x (l + 1)) = x l}
  have : BorelSpace ((l : ℕ) → B l) := inferInstance
  have : BorelSpace (Thread B q) := inferInstance
  have : BorelSpace X := by dsimp [X]; infer_instance
  have hπ (l : ℕ) : Continuous (levelProjection q n l) := by
    exact continuous_pi fun j =>
      (continuous_apply l).comp (continuous_subtype_val.comp (continuous_apply j))
  have lift_symbol (l : ℕ) (b : B l) : ∃ x : Thread B q, x.val l = b := by
    choose r hr using fun k (z : B k) => hq k z
    let down (k : ℕ) (h : k ≤ l) : B k :=
      Nat.decreasingInduction (motive := fun k _ => B k) (fun k _ z => q k z) b h
    let up (k : ℕ) (h : l ≤ k) : B k :=
      Nat.leRecOn (C := B) h (fun {k} z => r k z) b
    let x (k : ℕ) : B k :=
      if h : k ≤ l then down k h else up k (Nat.le_of_lt (Nat.lt_of_not_ge h))
    have hx : ∀ k, q k (x (k + 1)) = x k := by
      intro k
      by_cases hk : k < l
      · simp only [x, dif_pos (show k + 1 ≤ l from hk), dif_pos hk.le]
        exact (Nat.decreasingInduction_succ_left (motive := fun k _ => B k)
          (fun k _ z => q k z) b hk hk.le).symm
      · have hlk : l ≤ k := Nat.le_of_not_gt hk
        by_cases heq : k = l
        · subst k
          simp only [x, dif_neg (Nat.not_succ_le_self l), dif_pos (le_refl l),
            up, down, Nat.leRecOn_succ', Nat.decreasingInduction_self, hr]
        · have hkl : ¬ k ≤ l := by omega
          have hkl' : ¬ k + 1 ≤ l := by omega
          simp only [x, dif_neg hkl, dif_neg hkl', up]
          rw [Nat.leRecOn_succ hlk]
          exact hr k _
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [x, dif_pos (le_refl l), down, Nat.decreasingInduction_self]
  have hsurj (l : ℕ) : Surjective (levelProjection q n l) := by
    intro y
    choose x hx using fun j => lift_symbol l (y j)
    exact ⟨x, funext hx⟩
  let H (l : ℕ) : Set (ProbabilityMeasure X) :=
    {μ | μ.map (hπ l).measurable.aemeasurable = Q l}
  have hHclosed (l : ℕ) : IsClosed (H l) :=
    isClosed_eq (ProbabilityMeasure.continuous_map (hπ l)) continuous_const
  have hHnonempty (l : ℕ) : (H l).Nonempty := by
    choose s hs using hsurj l
    have hsm : Measurable s := measurable_of_countable s
    refine ⟨(Q l).map hsm.aemeasurable, ?_⟩
    apply Subtype.ext
    change ((Q l : Measure (Fin n → B l)).map s).map (levelProjection q n l) = _
    rw [Measure.map_map (hπ l).measurable hsm]
    rw [show levelProjection q n l ∘ s = id from funext hs, Measure.map_id]
    rfl
  have hHdecreasing (l : ℕ) : H (l + 1) ⊆ H l := by
    intro μ hμ
    apply Subtype.ext
    have hμ' : (μ : Measure X).map (levelProjection q n (l + 1)) =
        (Q (l + 1) : Measure (Fin n → B (l + 1))) :=
      congrArg ProbabilityMeasure.toMeasure hμ
    have hmap : Measurable (fun y : Fin n → B (l + 1) => fun j => q l (y j)) :=
      measurable_of_countable _
    change (μ : Measure X).map (levelProjection q n l) = (Q l : Measure _)
    rw [← hQ l, ← hμ', Measure.map_map hmap (hπ (l + 1)).measurable]
    congr 1
    funext x j
    exact (x j).property l |>.symm
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    H hHdecreasing hHnonempty (hHclosed 0).isCompact hHclosed
  have hμlaw (l : ℕ) : (μ : Measure X).map (levelProjection q n l) =
      (Q l : Measure (Fin n → B l)) :=
    congrArg ProbabilityMeasure.toMeasure (mem_iInter.mp hμ l)
  refine ⟨μ, hμlaw, ?_⟩
  intro ν hν
  apply Subtype.ext
  have hzero : measurableTotalVariation (ν : Measure X) (μ : Measure X) = 0 := by
    rw [total_variation_eq_iSup_level q n]
    simp [hμlaw, hν, measurableTotalVariation]
  apply Measure.ext
  intro A hA
  have hgap : max ((ν : Measure X) A - (μ : Measure X) A)
      ((μ : Measure X) A - (ν : Measure X) A) ≤ 0 := by
    rw [← hzero]
    exact le_iSup (fun e : {s : Set X // MeasurableSet s} =>
      max ((ν : Measure X) e.val - (μ : Measure X) e.val)
        ((μ : Measure X) e.val - (ν : Measure X) e.val)) ⟨A, hA⟩
  exact le_antisymm
    (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_left _ _).trans hgap) bot_le))
    (tsub_eq_zero_iff_le.mp (le_antisymm ((le_max_right _ _).trans hgap) bot_le))

#print axioms exists_unique_probability_extension

end D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
