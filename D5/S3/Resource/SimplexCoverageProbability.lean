/- GID: D5/S3/Resource/SimplexCoverageProbability
   generality: G
   mirror-B: D5/B/S3/Resource/SimplexCoverageProbability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual uniform physical recovery probabilities equal factorial spanning evaluations. -/

import D5.S3.Resource.SimplexCoverageWords
import D5.S3.Resource.MinimumRetrievalTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Resource.SimplexCoverageProbability

open scoped ENNReal BigOperators
open MeasureTheory
open D5.S3.Resource.SimplexCoveragePolynomial
open D5.S3.Resource.SimplexCoverageWords
open D5.S3.Resource.MinimumRetrievalTime

theorem uniformSamples_recovered_top {K V Index : Type*}
    [Field K] [AddCommGroup V] [Module K V]
    [Fintype Index] [DecidableEq Index] [Nonempty Index]
    [MeasurableSpace Index] [MeasurableSingletonClass Index]
    (columns : Index → V) (time : ℕ) :
    uniformSamples Index {sample | recovered columns (⊤ : Submodule K V) time sample} =
      ENNReal.ofReal ((time.factorial : ℝ) *
        evaluateAt (fun _ => (Fintype.card Index : ℝ)⁻¹)
          (spanningPolynomial columns (⊥ : Submodule K V) time)) := by
  classical
  let cylinder (word : Fin time → Index) : Set (ℕ → Index) :=
    {sample | ∀ position, sample position.val = word position}
  let admitted : Finset (Fin time → Index) := Finset.univ.filter
    (fun word => Submodule.span K (Set.range (fun position => columns (word position))) = ⊤)
  have cylinder_measurable (word : Fin time → Index) : MeasurableSet (cylinder word) := by
    have prefix_measurable : Measurable (fun sample : ℕ → Index =>
        fun position : Fin time => sample position.val) :=
      measurable_pi_iff.mpr (fun position => measurable_pi_apply position.val)
    have cylinder_eq : cylinder word =
        (fun sample : ℕ → Index => fun position : Fin time => sample position.val) ⁻¹'
          {word} := by
      ext sample
      simp [cylinder, funext_iff]
    rw [cylinder_eq]
    exact (measurableSet_singleton word).preimage prefix_measurable
  have cylinder_probability (word : Fin time → Index) :
      uniformSamples Index (cylinder word) = (Fintype.card Index : ℝ≥0∞)⁻¹ ^ time := by
    let coordinates (draw : ℕ) : Set Index :=
      if bound : draw < time then {word ⟨draw, bound⟩} else Set.univ
    have cylinder_eq : cylinder word = Set.pi (Finset.range time) coordinates := by
      ext sample
      change (∀ position : Fin time, sample position.val = word position) ↔ _
      simp only [Set.mem_pi, Finset.mem_coe, Finset.mem_range]
      constructor
      · intro membership draw bound
        simpa [coordinates, bound] using membership ⟨draw, bound⟩
      · intro membership position
        simpa [coordinates, position.isLt] using membership position.val position.isLt
    rw [cylinder_eq, uniformSamples, Measure.infinitePi_pi]
    · calc
        (∏ draw ∈ Finset.range time,
          (PMF.uniformOfFintype Index).toMeasure (coordinates draw)) =
            ∏ _ ∈ Finset.range time, (Fintype.card Index : ℝ≥0∞)⁻¹ := by
          apply Finset.prod_congr rfl
          intro draw membership
          have bound := Finset.mem_range.mp membership
          simp only [coordinates, dif_pos bound]
          rw [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
          simp
        _ = (Fintype.card Index : ℝ≥0∞)⁻¹ ^ time := by simp
    · intro draw _
      dsimp [coordinates]
      split_ifs <;> measurability
  have disjoint : (admitted : Set (Fin time → Index)).PairwiseDisjoint cylinder := by
    intro first _ second _ distinct
    change Disjoint (cylinder first) (cylinder second)
    rw [Set.disjoint_left]
    intro sample first_mem second_mem
    apply distinct
    funext position
    exact (first_mem position).symm.trans (second_mem position)
  have recovery_event : {sample | recovered columns (⊤ : Submodule K V) time sample} =
      ⋃ word ∈ admitted, cylinder word := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro recovery
      refine ⟨(fun position => sample position.val), ?_, ?_⟩
      · simpa [admitted, recovered, prefixSpan, top_le_iff] using recovery
      · exact fun _ => rfl
    · rintro ⟨word, membership, prefix_membership⟩
      have prefix_eq : (fun position : Fin time => sample position.val) = word :=
        funext prefix_membership
      change ⊤ ≤ Submodule.span K (Set.range
        (fun position : Fin time => columns (sample position.val)))
      change ⊤ ≤ Submodule.span K (Set.range (columns ∘
        (fun position : Fin time => sample position.val)))
      rw [prefix_eq]
      change ⊤ ≤ Submodule.span K (Set.range (fun position => columns (word position)))
      rw [(Finset.mem_filter.mp membership).2]
  have word_evaluation :
      evaluateAt (fun _ => (Fintype.card Index : ℝ)⁻¹)
          (wordPolynomial columns (⊥ : Submodule K V) time) =
        ∑ _ ∈ admitted, (Fintype.card Index : ℝ)⁻¹ ^ time := by
    rw [wordPolynomial, evaluateAt, MvPolynomial.eval₂_sum]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro word _
    simp only [bot_sup_eq, apply_ite, MvPolynomial.eval₂_zero]
    split_ifs <;> simp [MvPolynomial.eval₂_prod]
  have evaluation_probability :
      uniformSamples Index {sample | recovered columns (⊤ : Submodule K V) time sample} =
        ENNReal.ofReal (evaluateAt (fun _ => (Fintype.card Index : ℝ)⁻¹)
          (wordPolynomial columns (⊥ : Submodule K V) time)) := by
    rw [recovery_event, measure_biUnion_finset disjoint
      (fun word _ => cylinder_measurable word), word_evaluation]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    apply Finset.sum_congr rfl
    intro word _
    rw [cylinder_probability, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]
  rw [evaluation_probability, wordPolynomial_eq_factorial_smul]
  congr 1
  change (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ)
    (fun _ : Index => (Fintype.card Index : ℝ)⁻¹))
      (time.factorial • spanningPolynomial columns (⊥ : Submodule K V) time) = _
  rw [map_nsmul, nsmul_eq_mul]
  rfl

end D5.S3.Resource.SimplexCoverageProbability
