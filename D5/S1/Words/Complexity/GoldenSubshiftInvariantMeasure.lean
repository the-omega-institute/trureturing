/- GID: D5/S1/Words/Complexity/GoldenSubshiftInvariantMeasure
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/GoldenSubshiftInvariantMeasure
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: The golden word subshift carries a forward-shift-invariant Borel probability measure. Mathlib supplies weak-star compactness of the space of probability measures on a compact space but no existence theorem for invariant measures, so the Krylov-Bogolyubov construction is carried out here: Cesaro averages of pushed-forward Dirac masses have a convergent subsequence whose limit is invariant, because the shifted and unshifted averages differ by a single telescoping term of order one over the block length. -/

import D5.S1.Words.Complexity.GoldenSubshiftMinimality

open Set SymbolicDynamics MeasureTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open D5.S1.Words.Complexity.SubshiftTopology

namespace D5.S1.Words.Complexity.GoldenSubshiftInvariantMeasure

/-- Points of the golden word subshift, carried as a subtype of the full shift space. -/
abbrev GoldenPoint := ↥(wordSubshift goldenWord)

instance : Nonempty GoldenPoint := ⟨⟨goldenWord, self_mem_wordSubshift goldenWord⟩⟩

instance : CompactSpace GoldenPoint :=
  isCompact_iff_compactSpace.mp (IsClosed.isCompact (isClosed_wordSubshift goldenWord))

private lemma shift_mem (y : GoldenPoint) :
    FullShift.shift (1 : ℕ) (y : ℕ → Bool) ∈ wordSubshift goldenWord := by
  have h : FullShift.shift (1 : ℕ) (y : ℕ → Bool) = fun j ↦ (y : ℕ → Bool) (j + 1) := by
    funext j
    simp [FullShift.shift, Nat.add_comm]
  rw [h]
  exact wordSubshift_shift_invariant goldenWord y.2

/-- The one-step forward shift, restricted to the golden subshift. -/
noncomputable def forwardShift : GoldenPoint → GoldenPoint :=
  fun y => ⟨FullShift.shift (1 : ℕ) (y : ℕ → Bool), shift_mem y⟩

lemma forwardShift_continuous : Continuous forwardShift := by
  apply Continuous.subtype_mk
  exact (FullShift.continuous_shift (1 : ℕ)).comp continuous_subtype_val

/-- The Cesaro average of the first `n` shift iterates of the Dirac mass at `x`. -/
noncomputable def cesaroAverage (x : GoldenPoint) (n : ℕ) : Measure GoldenPoint :=
  (n : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range n, Measure.map (forwardShift^[k]) (Measure.dirac x)

private instance finite_iterate_dirac (x : GoldenPoint) (k : ℕ) :
    IsFiniteMeasure (Measure.map (forwardShift^[k]) (Measure.dirac x)) := by
  rw [Measure.map_dirac x]
  infer_instance

private lemma iterate_sum_univ (x : GoldenPoint) (n : ℕ) :
    (∑ k ∈ Finset.range n, Measure.map (forwardShift^[k]) (Measure.dirac x)) univ
      = (n : ℝ≥0∞) := by
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have h : ∀ k ∈ Finset.range n,
      (Measure.map (forwardShift^[k]) (Measure.dirac x)) univ = 1 := by
    intro k _
    rw [Measure.map_dirac x]
    simp
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

lemma cesaroAverage_isProbabilityMeasure_of_pos (x : GoldenPoint) (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (cesaroAverage x n) := by
  constructor
  show ((n : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range n, Measure.map (forwardShift^[k]) (Measure.dirac x)) univ = 1
  rw [Measure.smul_apply, smul_eq_mul, iterate_sum_univ]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)

/-- Every Cesaro average over a nonempty initial block is a probability measure. -/
instance cesaroAverage_isProbabilityMeasure (x : GoldenPoint) (n : ℕ) :
    IsProbabilityMeasure (cesaroAverage x (n + 1)) :=
  cesaroAverage_isProbabilityMeasure_of_pos x (n + 1) n.succ_pos

private instance finite_iterate_sum (x : GoldenPoint) (n : ℕ) :
    IsFiniteMeasure (∑ k ∈ Finset.range n, Measure.map (forwardShift^[k]) (Measure.dirac x)) := by
  constructor
  rw [iterate_sum_univ]
  exact ENNReal.natCast_lt_top n

private lemma integral_iterate_sum (f : GoldenPoint →ᵇ ℝ) (x : GoldenPoint) (n : ℕ) :
    ∫ y, f y ∂(∑ k ∈ Finset.range n, Measure.map (forwardShift^[k]) (Measure.dirac x))
      = ∑ k ∈ Finset.range n, f (forwardShift^[k] x) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun k => f (forwardShift^[k] x))]
      rw [integral_add_measure (f.integrable _) (f.integrable _), ih]
      congr 1
      rw [Measure.map_dirac x]
      simp

/-- Integrating against a Cesaro average is averaging along the forward orbit. -/
lemma integral_cesaroAverage (f : GoldenPoint →ᵇ ℝ) (x : GoldenPoint) (n : ℕ) :
    ∫ y, f y ∂(cesaroAverage x n)
      = ((n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, f (forwardShift^[k] x) := by
  unfold cesaroAverage
  rw [integral_smul_measure, integral_iterate_sum f x n]
  simp [ENNReal.toReal_inv]

private lemma telescope (f : GoldenPoint →ᵇ ℝ) (x : GoldenPoint) (n : ℕ) :
    (∑ k ∈ Finset.range n, f (forwardShift (forwardShift^[k] x)))
        - (∑ k ∈ Finset.range n, f (forwardShift^[k] x))
      = f (forwardShift^[n] x) - f x := by
  have e : ∀ k, f (forwardShift (forwardShift^[k] x)) = f (forwardShift^[k + 1] x) := by
    intro k
    congr 1
    rw [Function.iterate_succ_apply']
  have h1 : ∑ k ∈ Finset.range (n + 1), f (forwardShift^[k] x)
      = (∑ k ∈ Finset.range n, f (forwardShift^[k + 1] x)) + f (forwardShift^[0] x) :=
    Finset.sum_range_succ' (fun k => f (forwardShift^[k] x)) n
  have h2 : ∑ k ∈ Finset.range (n + 1), f (forwardShift^[k] x)
      = (∑ k ∈ Finset.range n, f (forwardShift^[k] x)) + f (forwardShift^[n] x) :=
    Finset.sum_range_succ (fun k => f (forwardShift^[k] x)) n
  simp only [e, Function.iterate_zero_apply] at *
  linarith

private lemma integral_pushforward (f : GoldenPoint →ᵇ ℝ) (nu : Measure GoldenPoint)
    [IsFiniteMeasure nu] :
    ∫ y, f y ∂(Measure.map forwardShift nu) = ∫ y, f (forwardShift y) ∂nu :=
  integral_map forwardShift_continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable

private lemma toMeasure_map (nu : ProbabilityMeasure GoldenPoint) :
    ((ProbabilityMeasure.map nu forwardShift_continuous.measurable.aemeasurable :
        ProbabilityMeasure GoldenPoint) : Measure GoldenPoint)
      = Measure.map forwardShift (nu : Measure GoldenPoint) :=
  ProbabilityMeasure.toMeasure_map nu
    (Continuous.measurable forwardShift_continuous).aemeasurable

private lemma ext_of_integrals (mu1 mu2 : ProbabilityMeasure GoldenPoint)
    (h : ∀ f : GoldenPoint →ᵇ ℝ,
      ∫ y, f y ∂(mu1 : Measure GoldenPoint) = ∫ y, f y ∂(mu2 : Measure GoldenPoint)) :
    mu1 = mu2 := by
  have hfm : mu1.toFiniteMeasure = mu2.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq h
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg (fun nu : FiniteMeasure GoldenPoint => (nu : Measure GoldenPoint)) hfm

/-- Shifting a Cesaro average moves its integral by a single telescoping term. -/
lemma cesaroAverage_shift_diff (f : GoldenPoint →ᵇ ℝ) (x : GoldenPoint) (n : ℕ) :
    (∫ y, f (forwardShift y) ∂(cesaroAverage x n)) - (∫ y, f y ∂(cesaroAverage x n))
      = ((n : ℝ))⁻¹ * (f (forwardShift^[n] x) - f x) := by
  have hcomp : ∀ y : GoldenPoint,
      (f.compContinuous ⟨forwardShift, forwardShift_continuous⟩) y = f (forwardShift y) :=
    fun _ => rfl
  have h1 : ∫ y, f (forwardShift y) ∂(cesaroAverage x n)
      = ((n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, f (forwardShift (forwardShift^[k] x)) := by
    have h := integral_cesaroAverage (f.compContinuous ⟨forwardShift, forwardShift_continuous⟩) x n
    simpa [hcomp] using h
  rw [h1, integral_cesaroAverage f x n, ← mul_sub, telescope f x n]

private noncomputable def cesaroProb (x : GoldenPoint) (n : ℕ) :
    ProbabilityMeasure GoldenPoint :=
  ⟨cesaroAverage x (n + 1), cesaroAverage_isProbabilityMeasure x n⟩

private lemma cesaroProb_toMeasure (x : GoldenPoint) (n : ℕ) :
    ((cesaroProb x n : ProbabilityMeasure GoldenPoint) : Measure GoldenPoint)
      = cesaroAverage x (n + 1) := rfl

/-- The golden word subshift carries a forward-shift-invariant Borel probability measure. -/
theorem exists_invariant_probabilityMeasure :
    ∃ mu : ProbabilityMeasure GoldenPoint,
      MeasurePreserving forwardShift (mu : Measure GoldenPoint) (mu : Measure GoldenPoint) := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty GoldenPoint)
  obtain ⟨mu, phi, hphi, hconv⟩ := SeqCompactSpace.tendsto_subseq (cesaroProb x0)
  refine ⟨mu, forwardShift_continuous.measurable, ?_⟩
  have hcoe : ((ProbabilityMeasure.map mu
      forwardShift_continuous.measurable.aemeasurable : ProbabilityMeasure GoldenPoint) :
      Measure GoldenPoint) = Measure.map forwardShift (mu : Measure GoldenPoint) :=
    toMeasure_map mu
  rw [← hcoe]
  congr 1
  refine ext_of_integrals _ _ ?_
  intro f
  have hmap : Tendsto
      (fun n => ProbabilityMeasure.map (cesaroProb x0 (phi n))
        forwardShift_continuous.measurable.aemeasurable)
      atTop (𝓝 (ProbabilityMeasure.map mu forwardShift_continuous.measurable.aemeasurable)) :=
    ((ProbabilityMeasure.continuous_map forwardShift_continuous).tendsto mu).comp hconv
  have hA := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap f
  have hB := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv f
  have hdiff := hA.sub hB
  have hval : ∀ n : ℕ,
      (∫ y, f y ∂((ProbabilityMeasure.map (cesaroProb x0 (phi n))
          forwardShift_continuous.measurable.aemeasurable :
            ProbabilityMeasure GoldenPoint) : Measure GoldenPoint))
        - (∫ y, f y ∂((cesaroProb x0 (phi n) :
            ProbabilityMeasure GoldenPoint) : Measure GoldenPoint))
        = (((phi n : ℝ) + 1))⁻¹ * (f (forwardShift^[phi n] (forwardShift x0)) - f x0) := by
    intro n
    rw [toMeasure_map, cesaroProb_toMeasure, integral_pushforward]
    have h := cesaroAverage_shift_diff f x0 (phi n + 1)
    rw [Function.iterate_succ_apply] at h
    push_cast at h ⊢
    exact h
  have hphiTop : Tendsto (fun n : ℕ => ((phi n : ℝ) + 1)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => ((phi n : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hphi.tendsto_atTop
    exact Filter.tendsto_atTop_add_const_right _ 1 h1
  have hinv : Tendsto (fun n : ℕ => (((phi n : ℝ) + 1))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hphiTop
  have hbound : Tendsto (fun n : ℕ => (((phi n : ℝ) + 1))⁻¹ * (2 * ‖f‖)) atTop (𝓝 0) := by
    simpa using hinv.mul_const (2 * ‖f‖)
  have hzero : Tendsto (fun n : ℕ => (((phi n : ℝ) + 1))⁻¹
      * (f (forwardShift^[phi n] (forwardShift x0)) - f x0)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_) hbound
    rw [norm_mul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (phi n : ℝ) + 1)]
    have h1 := f.norm_coe_le_norm (forwardShift^[phi n] (forwardShift x0))
    have h2 := f.norm_coe_le_norm x0
    have hb : ‖f (forwardShift^[phi n] (forwardShift x0)) - f x0‖ ≤ 2 * ‖f‖ := by
      calc ‖f (forwardShift^[phi n] (forwardShift x0)) - f x0‖
          ≤ ‖f (forwardShift^[phi n] (forwardShift x0))‖ + ‖f x0‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add h1 h2
        _ = 2 * ‖f‖ := by ring
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hdiff0 : Tendsto (fun n : ℕ =>
      (∫ y, f y ∂((ProbabilityMeasure.map (cesaroProb x0 (phi n))
          forwardShift_continuous.measurable.aemeasurable :
            ProbabilityMeasure GoldenPoint) : Measure GoldenPoint))
        - (∫ y, f y ∂((cesaroProb x0 (phi n) :
            ProbabilityMeasure GoldenPoint) : Measure GoldenPoint)))
      atTop (𝓝 0) :=
    Tendsto.congr (fun n => (hval n).symm) hzero
  have hEq := tendsto_nhds_unique hdiff hdiff0
  linarith [hEq]

#print axioms forwardShift_continuous
#print axioms cesaroAverage_isProbabilityMeasure
#print axioms integral_cesaroAverage
#print axioms cesaroAverage_shift_diff
#print axioms exists_invariant_probabilityMeasure

end D5.S1.Words.Complexity.GoldenSubshiftInvariantMeasure
