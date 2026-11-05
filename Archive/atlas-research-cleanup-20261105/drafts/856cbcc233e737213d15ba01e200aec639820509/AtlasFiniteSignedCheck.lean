/- Transient exact application evidence. Never delivered as repository mathematics. -/
import D5.S3.Topology.Measures.FiniteObservationVariation
import D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
import D5.S3.Estimation.DataProcessing.DeclaredSourceInverseLimitMinimum
import D5.S3.Estimation.LeCamTight
import D5.S3.TotalVariation.DataProcessing

/-! Exact task applications; all declarations in this module are transient evidence. -/
set_option pp.universes true
noncomputable section
open Classical
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
open D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
namespace AtlasFiniteSignedCheck

section Finite
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

-- The actual arbitrary-sign vector-measure sum, not a nonnegative measure surrogate.
def atomic (p : X → ℝ) : SignedMeasure X := ∑ x, VectorMeasure.dirac x (p x)

theorem atomic_set (p : X → ℝ) (A : Set X) :
    atomic p A = ∑ x ∈ (Set.toFinite A).toFinset, p x := by
  classical
  simp only [atomic, sum_apply]
  have hm : MeasurableSet A := (Set.toFinite A).measurableSet
  change (∑ x, if MeasurableSet A ∧ x ∈ A then p x else 0) = _
  simp only [hm, true_and]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

theorem atomic_singleton (p : X → ℝ) (x : X) : atomic p {x} = p x := by
  classical
  simp [atomic_set]

theorem signed_sum (s : SignedMeasure X) (A : Finset X) :
    (∑ x ∈ A, s {x}) = s (A : Set X) := by
  simp_rw [s.apply_eq_posPart_real_sub_negPart_real (measurableSet_singleton _)]
  rw [Finset.sum_sub_distrib, sum_measureReal_singleton, sum_measureReal_singleton,
    s.apply_eq_posPart_real_sub_negPart_real (Set.toFinite _).measurableSet]

theorem atomic_injective : Function.Injective (atomic (X := X)) := by
  intro p q h
  funext x
  simpa only [atomic_singleton] using congrArg (fun s : SignedMeasure X => s {x}) h

theorem atomic_surjective : Function.Surjective (atomic (X := X)) := by
  intro s
  refine ⟨fun x => s {x}, ?_⟩
  apply VectorMeasure.ext
  intro A hA
  rw [atomic_set, signed_sum, Set.Finite.coe_toFinset]

theorem atomic_reconstruct (s : SignedMeasure X) : atomic (fun x => s {x}) = s := by
  obtain ⟨p, rfl⟩ := atomic_surjective s
  simp only [atomic_singleton]

-- Arbitrary target: singleton mass is the full finite fiber sum.
theorem atomic_map_singleton {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : X → Y) (p : X → ℝ) (y : Y) :
    (atomic p).map f {y} = ∑ x, if f x = y then p x else 0 := by
  classical
  rw [VectorMeasure.map_apply _ (measurable_of_countable f) (measurableSet_singleton y),
    atomic_set]
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp

theorem atomic_map {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (f : X → Y) (p : X → ℝ) :
    (atomic p).map f = atomic (fun y => ∑ x, if f x = y then p x else 0) := by
  rw [← atomic_reconstruct ((atomic p).map f)]
  congr 1
  funext y
  exact atomic_map_singleton f p y

-- Full variation; there is no equal-mass or positivity premise.
theorem full_variation (s : SignedMeasure X) :
    s.totalVariation.real univ = ∑ x, |s {x}| := by
  have h := sum_measureReal_singleton (μ := s.totalVariation) (Finset.univ : Finset X)
  rw [Finset.coe_univ] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro x hx
  rw [measureReal_def, SignedMeasure.totalVariation_eq_variation,
    VectorMeasure.variation_apply_singleton, ← ofReal_norm,
    ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs]

theorem difference_variation (p q : X → ℝ) :
    (atomic p - atomic q).totalVariation.real univ = ∑ x, |p x - q x| ∧
    (atomic p - atomic q).totalVariation.real univ = 2 * totalVariation p q := by
  have h : (atomic p - atomic q).totalVariation.real univ = ∑ x, |p x - q x| := by
    rw [full_variation]
    simp only [sub_apply, atomic_singleton]
  exact ⟨h, by rw [h, totalVariation]; ring⟩

theorem probability_difference (μ ν : ProbabilityMeasure X) :
    (μ : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure =
      atomic (fun x => massVector μ x - massVector ν x) := by
  rw [← atomic_reconstruct ((μ : Measure X).toSignedMeasure - (ν : Measure X).toSignedMeasure)]
  congr 1
  funext x
  simp only [sub_apply, Measure.toSignedMeasure_apply_measurable (measurableSet_singleton x),
    massVector]

theorem probability_coordinates (μ : ProbabilityMeasure X) :
    (∀ x, 0 ≤ massVector μ x) ∧ (∑ x, massVector μ x) = 1 ∧
    lawOfMass ⟨massVector μ, massVector_mem_simplex μ⟩ = μ := by
  exact ⟨(massVector_mem_simplex μ).1, (massVector_mem_simplex μ).2,
    probabilitySimplexEquiv.left_inv μ⟩

theorem coordinates_probability (p : X → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hunit : ∑ x, p x = 1) :
    ∃! μ : ProbabilityMeasure X, massVector μ = p := by
  refine ⟨lawOfMass ⟨p, hp, hunit⟩, massVector_lawOfMass _, ?_⟩
  intro μ hμ
  exact massVector_injective (hμ.trans (massVector_lawOfMass ⟨p, hp, hunit⟩).symm)

theorem actual_event_maximum (μ ν : ProbabilityMeasure X) :
    IsGreatest (Set.range fun A : Finset X =>
      |(μ : Measure X).real A - (ν : Measure X).real A|)
      (totalVariation (massVector μ) (massVector ν)) := by
  have h := total_variation_eq_sup_event_gap (massVector μ) (massVector ν)
    ((massVector_mem_simplex μ).2.trans (massVector_mem_simplex ν).2.symm)
  simpa only [massVector, sum_measureReal_singleton] using h

theorem actual_test_lower (μ ν : ProbabilityMeasure X) (A : Finset X) :
    1 - totalVariation (massVector μ) (massVector ν) ≤
      (μ : Measure X).real A + (ν : Measure X).real (Aᶜ : Finset X) := by
  have h := D5.S3.Estimation.LeCam.le_cam_two_point_sum
    (massVector μ) (massVector ν) A
    ((massVector_mem_simplex μ).2.trans (massVector_mem_simplex ν).2.symm)
    (massVector_mem_simplex ν).2
  simpa only [massVector, sum_measureReal_singleton] using h

theorem actual_optimal_test (μ ν : ProbabilityMeasure X) :
    ∃ A : Finset X, (μ : Measure X).real A + (ν : Measure X).real (Aᶜ : Finset X) =
      1 - totalVariation (massVector μ) (massVector ν) := by
  classical
  refine ⟨Finset.univ.filter (fun x => massVector μ x ≤ massVector ν x), ?_⟩
  have h := D5.S3.Estimation.LeCamTight.le_cam_two_point_sum_tight
    (massVector μ) (massVector ν)
    ((massVector_mem_simplex μ).2.trans (massVector_mem_simplex ν).2.symm)
    (massVector_mem_simplex ν).2
  simpa only [massVector, sum_measureReal_singleton] using h

-- Public native normalization, independently scoped from finite half-L1.
theorem exact_check_1 (μ ν : ProbabilityMeasure X) :
    (D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction.measurableTotalVariation
      (μ : Measure X) (ν : Measure X)).toReal =
    sSup (Set.range fun A : {A : Set X // MeasurableSet A} =>
      |(μ : Measure X).real A.val - (ν : Measure X).real A.val|) :=
  (D5.S3.Estimation.DataProcessing.DeclaredSourceInverseLimitMinimum.event_tv_normalization μ ν).1

theorem exact_check_2 {Y : Type*} [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (f : X → Y) (μ : ProbabilityMeasure X) :
    massVector (μ.map f) = D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass f
      (massVector μ) := massVector_map f μ

theorem finite_tv_map {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (f : X → Y) (μ ν : ProbabilityMeasure X) :
    totalVariation (massVector (μ.map f)) (massVector (ν.map f)) ≤
      totalVariation (massVector μ) (massVector ν) := by
  classical
  rw [massVector_map, massVector_map]
  let W : X → Y → ℝ := fun x y => if f x = y then 1 else 0
  have hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1 := by
    constructor
    · intro x y; dsimp [W]; split_ifs <;> norm_num
    · intro x; simp [W]
  have hc (p : X → ℝ) :
      D5.S3.Divergence.ClassicalDPI.channelOutput W p =
        D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass f p := by
    funext y
    simp [D5.S3.Divergence.ClassicalDPI.channelOutput, W,
      D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope.pushMass]
  simpa only [hc] using
    D5.S3.TotalVariation.DataProcessing.total_variation_channel_le
      (massVector μ) (massVector ν) W hW

end Finite

-- Exactly the discrete Borel topology and full, unhalved Riesz norm.
theorem exact_check_3 {X : Type*} [Fintype X] [TopologicalSpace X] [DiscreteTopology X]
    [MeasurableSpace X] [BorelSpace X] (p q : X → ℝ) :
    ‖D5.S3.Topology.Measures.NormPreservingLifts.signedFunctional (atomic p - atomic q)‖ =
      ∑ x, |p x - q x| := by
  rw [← (D5.S3.Topology.Measures.SignedRieszRepresentation.signed_riesz_markov_kakutani
    (K := X)).2.1 _ (by infer_instance)]
  exact (difference_variation p q).1

-- Empty carrier is covered by the same construction and bijection.
theorem exact_check_4 : atomic (fun x : Fin 0 => Fin.elim0 x) = 0 := by
  simp [atomic]

-- Signs and actual cancellation after pushforward.
def signedPair : Bool → ℝ := fun b => if b then -3 else 3
theorem exact_check_5 : atomic signedPair {false} = 3 ∧ atomic signedPair {true} = -3 ∧
    (atomic signedPair).totalVariation.real univ = 6 ∧
    (atomic signedPair).map (fun _ : Bool => ()) = 0 := by
  refine ⟨by rw [atomic_singleton]; rfl, by rw [atomic_singleton]; rfl, ?_, ?_⟩
  · rw [full_variation]
    norm_num [atomic_singleton, signedPair]
  · rw [atomic_map]
    simp [signedPair, atomic]

-- Without equal mass even the whole event exceeds the half-L1 quantity.
theorem exact_check_6 :
    let p : Unit → ℝ := fun _ => 2
    let q : Unit → ℝ := fun _ => 0
    totalVariation p q = 1 ∧
      |atomic p (Set.univ : Set Unit) - atomic q Set.univ| = 2 := by
  norm_num [totalVariation, atomic_set]

#check @atomic_set
#check @atomic_map_singleton
#check @atomic_map
#check @atomic_injective
#check @atomic_surjective
#check @difference_variation
#check @probability_difference
#check @actual_event_maximum
#check @actual_optimal_test
#print axioms atomic_set
#print axioms atomic_map_singleton
#print axioms atomic_map
#print axioms atomic_injective
#print axioms atomic_surjective
#print axioms full_variation
#print axioms difference_variation
#print axioms probability_difference
#print axioms probability_coordinates
#print axioms coordinates_probability
#print axioms actual_event_maximum
#print axioms actual_optimal_test
#check @atomic
#print axioms atomic
#check @atomic_singleton
#print axioms atomic_singleton
#check @signed_sum
#print axioms signed_sum
#check @atomic_reconstruct
#print axioms atomic_reconstruct
#check @exact_check_1
#print axioms exact_check_1
#check @exact_check_2
#print axioms exact_check_2
#check @finite_tv_map
#print axioms finite_tv_map
#check @exact_check_3
#print axioms exact_check_3
#check @exact_check_4
#print axioms exact_check_4
#check @signedPair
#print axioms signedPair
#check @exact_check_5
#print axioms exact_check_5
#check @exact_check_6
#print axioms exact_check_6

#check @full_variation
#check @probability_coordinates
#check @coordinates_probability

#check @actual_test_lower
#print axioms actual_test_lower

end AtlasFiniteSignedCheck
