/- GID: D5/S3/Quantum/Measurement/OrderedRootCoordinates
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/OrderedRootCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordered roots describe the exact angular incompatibility interval. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none (the only D5 imports belong to this delivery).
The public content theorem coordinate_change_lintegral uses coordinateMap_surjective.
The inverse witness is explicitly constructed; normalization alone leaves its existence open.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15930
Declaration rows: name | proof_shape | escape_witness | one direct consumer.
Definitions have no proof term; their bind-only label supplies no admission witness.
V | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_V
hYu | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.angularIntegral_measurable
NJM | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.positiveSector
incompProb | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.claim
claim | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.result
measurableSet_V | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.body_measure_fubini
measurableSet_NJM | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_four_sectors
body_fiber | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.body_fiber_volume
body_fiber_volume | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.body_measure_fubini
body_measure_fubini | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_V
one_sub_cube_integral | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.abs_cube_integral
abs_cube_integral | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_V
volume_V | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.incompProb_eq_nine_I
hYu_neg_bias | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.NJM_preimage_second_neg
hYu_neg_vector | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.NJM_preimage_second_neg
NJM_preimage_first_neg | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_first_neg_sector
first_neg_preserves_volume | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_first_neg_sector
volume_NJM_first_neg_sector | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_four_sectors
first_bias_zero_null | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.split_first_bias
second_bias_zero_null | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.split_second_bias
split_first_bias | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_four_sectors
split_second_bias | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_four_sectors
NJM_preimage_second_neg | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_positive_first_second_neg_sector
second_neg_preserves_volume | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_positive_first_second_neg_sector
volume_NJM_positive_first_second_neg_sector | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.volume_NJM_four_sectors
positiveSector | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_ordered
volume_NJM_four_sectors | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_NJM_rootI
body_boundary_null | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_eq_interior
vector_zero_null | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_eq_interior
two_term_sqrt_cauchy | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.angular_volume_ordered
square_interval | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.angular_interval_volume
angular_interval_volume | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.angular_volume_ordered
negative_sector_empty | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.angular_volume_ordered
xCoord | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.coordinateJacobian_pos
rCoord | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.coordinateJacobian_pos
coordinates_in_body | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinateMap_mapsTo
hRadial_coordinates | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.root_coordinates
root_coordinates | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinateMap_injective
radial_coordinate_square | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.angular_volume_ordered
bias_coordinate_square | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.angular_volume_ordered
angular_volume_ordered | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.angularIntegral_coordinates
coordinateMap | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_ordered
coordinateDerivative | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.hasFDerivAt_coordinateMap
hasFDerivAt_coordinateMap | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinate_change_lintegral
det_coordinateDerivative | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinate_change_lintegral
rootDomain | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.coordinateJacobian_pos
radialBody | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinateMap_mapsTo
coordinateMap_injective | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinate_change_lintegral
coordinateMap_surjective | proof_shape: content | escape_witness: coordinateMap_surjective | OrderedRootCoordinates.coordinateMap_image
coordinateMap_mapsTo | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinateMap_image
coordinateMap_image | proof_shape: content | escape_witness: coordinateMap_surjective | OrderedRootCoordinates.coordinate_change_lintegral
measurableSet_rootDomain | proof_shape: bind-only | escape_witness: none | OrderedRootCoordinates.coordinate_change_lintegral
coordinate_change_lintegral | proof_shape: content | escape_witness: coordinateMap_surjective | QubitIncompatibilityRadialReduction.volume_positiveSector_ordered
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
noncomputable section


open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace D5.S3.Quantum.Measurement.OrderedRootCoordinates

def V : Set (ℝ × EuclideanSpace ℝ (Fin 3)) :=
  {p | |p.1| + ‖p.2‖ ≤ 1}

def hYu (x : ℝ) (a : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (Real.sqrt ((1 + x) ^ 2 - ‖a‖ ^ 2) +
    Real.sqrt ((1 - x) ^ 2 - ‖a‖ ^ 2)) / 2

def NJM : Set ((ℝ × EuclideanSpace ℝ (Fin 3)) ×
    (ℝ × EuclideanSpace ℝ (Fin 3))) :=
  {q | q.1 ∈ V ∧ q.2 ∈ V ∧
    (inner ℝ q.1.2 q.2.2 - q.1.1 * q.2.1) ^ 2 <
      (1 - hYu q.1.1 q.1.2 ^ 2 - hYu q.2.1 q.2.2 ^ 2) *
        (1 - q.1.1 ^ 2 / hYu q.1.1 q.1.2 ^ 2 -
          q.2.1 ^ 2 / hYu q.2.1 q.2.2 ^ 2)}

def incompProb : ℝ :=
  (MeasureTheory.volume NJM).toReal / ((MeasureTheory.volume V).toReal ^ 2)

def claim : Prop := incompProb = 1 / 4

private theorem measurableSet_V : MeasurableSet V := by
  exact isClosed_le (continuous_fst.abs.add continuous_snd.norm) continuous_const |>.measurableSet

private theorem measurableSet_NJM : MeasurableSet NJM := by
  unfold NJM V hYu
  measurability

private theorem body_fiber (x : ℝ) :
    {a : EuclideanSpace ℝ (Fin 3) | (x, a) ∈ V} =
      Metric.closedBall 0 (1 - |x|) := by
  ext a
  simp only [V, mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> linarith

private theorem body_fiber_volume (x : ℝ) :
    volume {a : EuclideanSpace ℝ (Fin 3) | (x, a) ∈ V} =
      ENNReal.ofReal (1 - |x|) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [body_fiber, EuclideanSpace.volume_closedBall_fin_three]

private theorem body_measure_fubini :
    volume V = ∫⁻ x : ℝ,
      ENNReal.ofReal (1 - |x|) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply measurableSet_V]
  apply lintegral_congr
  intro x
  exact body_fiber_volume x

private theorem one_sub_cube_integral :
    (∫ x : ℝ in (0 : ℝ)..1, (1 - x) ^ 3) = 1 / 4 := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(1 - y) ^ 4 / 4) ((1 - x) ^ 3) x := by
    intro x
    convert (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow 4).neg.div_const 4 using 1
    all_goals first | rfl | (simp only [Pi.sub_apply, id_eq]; ring)
  have hi : IntervalIntegrable (fun x : ℝ => (1 - x) ^ 3) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => (1 - x) ^ 3)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  norm_num

private theorem abs_cube_integral :
    (∫ x : ℝ in (-1 : ℝ)..1, (1 - |x|) ^ 3) = 1 / 2 := by
  have hc : Continuous (fun x : ℝ => (1 - |x|) ^ 3) := by fun_prop
  have hpos : (∫ x : ℝ in (0 : ℝ)..1, (1 - |x|) ^ 3) = 1 / 4 := by
    rw [← one_sub_cube_integral]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp
    rw [abs_of_nonneg]
    exact (uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1) ▸ hx).1
  have hneg : (∫ x : ℝ in (-1 : ℝ)..0, (1 - |x|) ^ 3) = 1 / 4 := by
    have he := intervalIntegral.integral_comp_neg
      (fun x : ℝ => (1 - |x|) ^ 3) (a := (-1 : ℝ)) (b := 0)
    have he' : (∫ x : ℝ in (-1 : ℝ)..0, (1 - |x|) ^ 3) =
        ∫ x : ℝ in (0 : ℝ)..1, (1 - |x|) ^ 3 := by
      simpa only [abs_neg, neg_zero, neg_neg] using he
    exact he'.trans hpos
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0)
    (hc.intervalIntegrable (μ := volume) 0 1)
  rw [← hs, hneg, hpos]
  norm_num

theorem volume_V : volume V = ENNReal.ofReal (2 * Real.pi / 3) := by
  rw [body_measure_fubini]
  have he : (fun x : ℝ => ENNReal.ofReal (1 - |x|) ^ 3 *
      ENNReal.ofReal (Real.pi * 4 / 3)) =
      (Icc (-1 : ℝ) 1).indicator
        (fun x : ℝ => ENNReal.ofReal ((1 - |x|) ^ 3 * (Real.pi * 4 / 3))) := by
    funext x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx, ENNReal.ofReal_mul,
        ENNReal.ofReal_pow]
      · exact sub_nonneg.mpr (abs_le.mpr hx)
      · exact pow_nonneg (sub_nonneg.mpr (abs_le.mpr hx)) 3
    · rw [indicator_of_notMem hx]
      have hn : 1 - |x| ≤ 0 := by
        by_contra h
        exact hx (abs_le.mp (by linarith))
      simp [ENNReal.ofReal_eq_zero.mpr hn]
  rw [he, lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn
      (fun x : ℝ => (1 - |x|) ^ 3 * (Real.pi * 4 / 3)) (Icc (-1 : ℝ) 1) :=
    (by fun_prop : Continuous _).integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      abs_cube_integral]
    congr 1
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr (abs_le.mpr hx)) 3)
      (by positivity)

private theorem hYu_neg_bias (x : ℝ) (a : EuclideanSpace ℝ (Fin 3)) :
    hYu (-x) a = hYu x a := by
  simp only [hYu, ← sub_eq_add_neg, sub_neg_eq_add]
  ring

private theorem hYu_neg_vector (x : ℝ) (a : EuclideanSpace ℝ (Fin 3)) :
    hYu x (-a) = hYu x a := by
  simp only [hYu, norm_neg]

private theorem NJM_preimage_first_neg :
    (Prod.map (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _) (id : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)) ⁻¹' NJM = NJM := by
  ext q
  simp only [mem_preimage, NJM, V, mem_ofPred_eq, Prod.map, id_eq,
    Prod.fst_neg, Prod.snd_neg, abs_neg, norm_neg, hYu_neg_vector,
    hYu_neg_bias, inner_neg_left, neg_mul, neg_sq]
  have he : (-inner ℝ q.1.2 q.2.2 - -(q.1.1 * q.2.1)) ^ 2 =
      (inner ℝ q.1.2 q.2.2 - q.1.1 * q.2.1) ^ 2 := by ring
  rw [he]

private theorem first_neg_preserves_volume :
    MeasurePreserving
      (Prod.map (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _) (id : (ℝ × EuclideanSpace ℝ (Fin 3)) → _))
      volume volume := by
  rw [Measure.volume_eq_prod]
  have hm : MeasurePreserving
      (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _) volume volume := by
    have hn := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    exact hn
  exact hm.prod (MeasurePreserving.id volume)

private theorem volume_NJM_first_neg_sector :
    volume (NJM ∩ {q | q.1.1 < 0}) = volume (NJM ∩ {q | 0 < q.1.1}) := by
  have hm : MeasurableSet (NJM ∩ {q | 0 < q.1.1}) :=
    measurableSet_NJM.inter (by measurability)
  have he :
      (Prod.map (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _) (id : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)) ⁻¹'
        (NJM ∩ {q | 0 < q.1.1}) = NJM ∩ {q | q.1.1 < 0} := by
    rw [preimage_inter, NJM_preimage_first_neg]
    ext q
    simp
  rw [← he]
  exact first_neg_preserves_volume.measure_preimage hm.nullMeasurableSet


private theorem first_bias_zero_null :
    volume {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) |
      q.1.1 = 0} = 0 := by
  have he : {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) |
      q.1.1 = 0} = ({(0 : ℝ)} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3)))) ×ˢ univ := by
    ext q; simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
  simp

private theorem second_bias_zero_null :
    volume {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) |
      q.2.1 = 0} = 0 := by
  have he : {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) |
      q.2.1 = 0} = univ ×ˢ ({(0 : ℝ)} ×ˢ (univ : Set (EuclideanSpace ℝ (Fin 3)))) := by
    ext q; simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
  simp

private theorem split_first_bias {s : Set ((ℝ × EuclideanSpace ℝ (Fin 3)) ×
      (ℝ × EuclideanSpace ℝ (Fin 3)))} (hs : MeasurableSet s) :
    volume s = volume (s ∩ {q | q.1.1 < 0}) + volume (s ∩ {q | 0 < q.1.1}) := by
  have hne : ∀ᵐ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3)))
      ∂volume, q.1.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using first_bias_zero_null
  have he : s =ᵐ[volume] ((s ∩ {q | q.1.1 < 0}) ∪ (s ∩ {q | 0 < q.1.1}) : Set ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3)))) := by
    filter_upwards [hne] with q hq
    apply propext
    change q ∈ s ↔ ((q ∈ s ∧ q.1.1 < 0) ∨ (q ∈ s ∧ 0 < q.1.1))
    rcases lt_or_gt_of_ne hq with h | h <;> simp [h] <;> tauto
  rw [measure_congr he, measure_union]
  · exact Set.disjoint_left.mpr (by
      intro q h1 h2
      have hn : q.1.1 < 0 := h1.2
      have hp : 0 < q.1.1 := h2.2
      linarith)
  · exact hs.inter (by measurability)

private theorem split_second_bias {s : Set ((ℝ × EuclideanSpace ℝ (Fin 3)) ×
      (ℝ × EuclideanSpace ℝ (Fin 3)))} (hs : MeasurableSet s) :
    volume s = volume (s ∩ {q | q.2.1 < 0}) + volume (s ∩ {q | 0 < q.2.1}) := by
  have hne : ∀ᵐ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3)))
      ∂volume, q.2.1 ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using second_bias_zero_null
  have he : s =ᵐ[volume] ((s ∩ {q | q.2.1 < 0}) ∪ (s ∩ {q | 0 < q.2.1}) : Set ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3)))) := by
    filter_upwards [hne] with q hq
    apply propext
    change q ∈ s ↔ ((q ∈ s ∧ q.2.1 < 0) ∨ (q ∈ s ∧ 0 < q.2.1))
    rcases lt_or_gt_of_ne hq with h | h <;> simp [h] <;> tauto
  rw [measure_congr he, measure_union]
  · exact Set.disjoint_left.mpr (by
      intro q h1 h2
      have hn : q.2.1 < 0 := h1.2
      have hp : 0 < q.2.1 := h2.2
      linarith)
  · exact hs.inter (by measurability)

private theorem NJM_preimage_second_neg :
    (Prod.map (id : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)
      (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)) ⁻¹' NJM = NJM := by
  ext q
  simp only [mem_preimage, NJM, V, mem_ofPred_eq, Prod.map, id_eq,
    Prod.fst_neg, Prod.snd_neg, abs_neg, norm_neg, hYu_neg_vector,
    hYu_neg_bias, inner_neg_right, mul_neg, neg_sq]
  have he : (-inner ℝ q.1.2 q.2.2 - -(q.1.1 * q.2.1)) ^ 2 =
      (inner ℝ q.1.2 q.2.2 - q.1.1 * q.2.1) ^ 2 := by ring
  rw [he]

private theorem second_neg_preserves_volume :
    MeasurePreserving (Prod.map (id : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)
      (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)) volume volume := by
  rw [Measure.volume_eq_prod]
  have hm : MeasurePreserving
      (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _) volume volume := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin 3))))
  exact (MeasurePreserving.id volume).prod hm

private theorem volume_NJM_positive_first_second_neg_sector :
    volume ((NJM ∩ {q | 0 < q.1.1}) ∩ {q | q.2.1 < 0}) =
      volume ((NJM ∩ {q | 0 < q.1.1}) ∩ {q | 0 < q.2.1}) := by
  have hm : MeasurableSet ((NJM ∩ {q | 0 < q.1.1}) ∩ {q | 0 < q.2.1}) :=
    (measurableSet_NJM.inter (by measurability)).inter (by measurability)
  have he : (Prod.map (id : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)
      (Neg.neg : (ℝ × EuclideanSpace ℝ (Fin 3)) → _)) ⁻¹'
        ((NJM ∩ {q | 0 < q.1.1}) ∩ {q | 0 < q.2.1}) =
        ((NJM ∩ {q | 0 < q.1.1}) ∩ {q | q.2.1 < 0}) := by
    rw [preimage_inter, preimage_inter, NJM_preimage_second_neg]
    ext q; simp
  rw [← he]
  exact second_neg_preserves_volume.measure_preimage hm.nullMeasurableSet

def positiveSector := NJM ∩ {q | 0 < q.1.1 ∧ 0 < q.2.1}

theorem volume_NJM_four_sectors : volume NJM = 4 * volume positiveSector := by
  have h1 := split_first_bias measurableSet_NJM
  have h2 := split_second_bias (measurableSet_NJM.inter
    (by measurability : MeasurableSet {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) | 0 < q.1.1}))
  rw [volume_NJM_first_neg_sector] at h1
  rw [volume_NJM_positive_first_second_neg_sector] at h2
  have he : ((NJM ∩ {q | 0 < q.1.1}) ∩ {q | 0 < q.2.1}) = positiveSector := by
    ext q; simp [positiveSector, and_assoc]
  rw [he] at h2
  rw [h2] at h1
  rw [h1]
  ring


theorem body_boundary_null :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 3) | |p.1| + ‖p.2‖ = 1} = 0 := by
  have hm : MeasurableSet {p : ℝ × EuclideanSpace ℝ (Fin 3) | |p.1| + ‖p.2‖ = 1} := by
    measurability
  rw [Measure.volume_eq_prod, Measure.prod_apply hm]
  have he : ∀ x : ℝ, {a : EuclideanSpace ℝ (Fin 3) | |x| + ‖a‖ = 1} =
      Metric.sphere 0 (1 - |x|) := by
    intro x
    ext a
    simp only [mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
    constructor <;> intro h <;> linarith
  have hf : ∀ x : ℝ, volume {a : EuclideanSpace ℝ (Fin 3) | (x, a) ∈
      {p : ℝ × EuclideanSpace ℝ (Fin 3) | |p.1| + ‖p.2‖ = 1}} = 0 := by
    intro x
    change volume {a : EuclideanSpace ℝ (Fin 3) | |x| + ‖a‖ = 1} = 0
    rw [he, Measure.addHaar_sphere volume]
  calc
    _ = ∫⁻ _x : ℝ, (0 : ℝ≥0∞) := by
      apply lintegral_congr
      intro x
      exact hf x
    _ = 0 := by simp

theorem vector_zero_null :
    volume {p : ℝ × EuclideanSpace ℝ (Fin 3) | p.2 = 0} = 0 := by
  have he : {p : ℝ × EuclideanSpace ℝ (Fin 3) | p.2 = 0} =
      univ ×ˢ ({0} : Set (EuclideanSpace ℝ (Fin 3))) := by ext p; simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod]
  simp

end D5.S3.Quantum.Measurement.OrderedRootCoordinates

open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D5.S3.Quantum.Measurement.OrderedRootCoordinates

private theorem two_term_sqrt_cauchy {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin 2))
    (f := ![a, c]) (g := ![b, d]) (by intro i; fin_cases i <;> simp [ha, hc])
    (by intro i; fin_cases i <;> simp [hb, hd])
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sqrt_mul ha, Real.sqrt_mul hc, Real.sqrt_mul (add_nonneg ha hc)] using h

private theorem square_interval {R c d : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hd : 0 < d)
    (hcd : c + d ≤ R) :
    {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ (R * s - c) ^ 2 < d ^ 2} =
      Ioo ((c - d) / R) ((c + d) / R) := by
  ext s
  have hsquare : (R * s - c) ^ 2 < d ^ 2 ↔
      -d < R * s - c ∧ R * s - c < d := by
    rw [sq_lt_sq, abs_of_pos hd, abs_lt]
  rw [mem_ofPred_eq, mem_Ioo, hsquare]
  rw [div_lt_iff₀ hR, lt_div_iff₀ hR]
  constructor
  · rintro ⟨hs0, hs1, hs2, hs3⟩
    constructor <;> nlinarith
  · rintro ⟨hs0, hs1⟩
    have hdR : d ≤ R := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

private theorem angular_interval_volume {R c A B : ℝ} (hR : 0 < R) (hc : 0 ≤ c)
    (hA : 0 < A) (hB : 0 < B) (hcd : c + Real.sqrt (A * B) ≤ R) :
    volume {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ (R * s - c) ^ 2 < A * B} =
      ENNReal.ofReal (2 * Real.sqrt (A * B) / R) := by
  have hAB : 0 < A * B := mul_pos hA hB
  have he := square_interval hR hc (Real.sqrt_pos.mpr hAB) hcd
  rw [Real.sq_sqrt hAB.le] at he
  rw [he, Real.volume_Ioo]
  congr 1
  ring

private theorem negative_sector_empty {R c a b d e : ℝ}
    (hR : 0 ≤ R) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (had : d ≤ a) (hbe : e ≤ b)
    (hR2 : R ^ 2 = (a - d) * (b - e)) (hc2 : c ^ 2 = a * b) :
    {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ (R * s - c) ^ 2 < d * e} = ∅ := by
  have hcs := two_term_sqrt_cauchy (sub_nonneg.mpr had) (sub_nonneg.mpr hbe) hd he
  have hRsqrt : Real.sqrt ((a - d) * (b - e)) = R := by
    rw [← hR2, Real.sqrt_sq hR]
  have hcsqrt : Real.sqrt (a * b) = c := by rw [← hc2, Real.sqrt_sq hc]
  have hadd : a - d + d = a := by ring
  have hbed : b - e + e = b := by ring
  rw [hRsqrt, hadd, hbed, hcsqrt] at hcs
  ext s
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨hs0, hs1, hs2⟩
  have hrs : R * s ≤ R := by nlinarith
  have hs : R * s - c ≤ -Real.sqrt (d * e) := by linarith
  have hsq := Real.sq_sqrt (mul_nonneg hd he)
  have hn := Real.sqrt_nonneg (d * e)
  nlinarith


def xCoord (u v : ℝ) : ℝ := Real.sqrt u * Real.sqrt v

def rCoord (u v : ℝ) : ℝ := Real.sqrt (1 - u) * Real.sqrt (1 - v)

private theorem coordinates_in_body {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1) :
    0 ≤ xCoord u v ∧ 0 ≤ rCoord u v ∧ xCoord u v + rCoord u v ≤ 1 := by
  have hu0 := hv.trans hvu
  have hv1 := hvu.trans hu
  have h := two_term_sqrt_cauchy hu0 hv (sub_nonneg.mpr hu) (sub_nonneg.mpr hv1)
  have he1 : u + (1 - u) = 1 := by ring
  have he2 : v + (1 - v) = 1 := by ring
  rw [he1, he2, one_mul, Real.sqrt_one] at h
  rw [Real.sqrt_mul hu0, Real.sqrt_mul (sub_nonneg.mpr hu)] at h
  exact ⟨by unfold xCoord; positivity, by unfold rCoord; positivity, h⟩

private theorem hRadial_coordinates {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1) :
    (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) (xCoord u v) (rCoord u v) = Real.sqrt u := by
  have hu0 := hv.trans hvu
  have hv1 := hvu.trans hu
  have hx2 : xCoord u v ^ 2 = u * v := by
    rw [xCoord, mul_pow, Real.sq_sqrt hu0, Real.sq_sqrt hv]
  have hr2 : rCoord u v ^ 2 = (1 - u) * (1 - v) := by
    rw [rCoord, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hu), Real.sq_sqrt (sub_nonneg.mpr hv1)]
  have hsu := Real.sq_sqrt hu0
  have hsv := Real.sq_sqrt hv
  have hsum : (1 + xCoord u v) ^ 2 - rCoord u v ^ 2 =
      (Real.sqrt u + Real.sqrt v) ^ 2 := by
    rw [hr2]
    have hx : xCoord u v = Real.sqrt u * Real.sqrt v := rfl
    nlinarith
  have hdiff : (1 - xCoord u v) ^ 2 - rCoord u v ^ 2 =
      (Real.sqrt u - Real.sqrt v) ^ 2 := by
    rw [hr2]
    have hx : xCoord u v = Real.sqrt u * Real.sqrt v := rfl
    nlinarith
  simp only [hYu, PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [hsum, hdiff, Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt u + Real.sqrt v),
    Real.sqrt_sq (sub_nonneg.mpr (Real.sqrt_le_sqrt hvu))]
  ring

theorem root_coordinates {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1)
    (hu0 : 0 < u) :
    (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) (xCoord u v) (rCoord u v) ^ 2 = u ∧
    xCoord u v ^ 2 / (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) (xCoord u v) (rCoord u v) ^ 2 = v := by
  rw [hRadial_coordinates hv hvu hu, Real.sq_sqrt hu0.le]
  constructor
  · rfl
  · rw [xCoord, mul_pow, Real.sq_sqrt hu0.le, Real.sq_sqrt hv]
    field_simp


private theorem radial_coordinate_square {u v : ℝ} (hvu : v ≤ u) (hu : u ≤ 1) :
    rCoord u v ^ 2 = (1 - u) * (1 - v) := by
  rw [rCoord, mul_pow, Real.sq_sqrt (sub_nonneg.mpr hu),
    Real.sq_sqrt (sub_nonneg.mpr (hvu.trans hu))]

private theorem bias_coordinate_square {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    xCoord u v ^ 2 = u * v := by
  rw [xCoord, mul_pow, Real.sq_sqrt (hv.trans hvu), Real.sq_sqrt hv]

theorem angular_volume_ordered {u v U V : ℝ}
    (hv : 0 ≤ v) (hvu : v ≤ u) (hu : u ≤ 1)
    (hV : 0 ≤ V) (hVU : V ≤ U) (hU : U ≤ 1) :
    volume {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧
      (rCoord u v * rCoord U V * s - xCoord u v * xCoord U V) ^ 2 <
        (1 - u - U) * (1 - v - V)} =
    if 0 < 1 - u - U then
      ENNReal.ofReal (2 * Real.sqrt ((1 - u - U) * (1 - v - V)) /
        (rCoord u v * rCoord U V)) else 0 := by
  let A := 1 - u - U
  let B := 1 - v - V
  let a := u * U
  let b := v * V
  let R := rCoord u v * rCoord U V
  let c := xCoord u v * xCoord U V
  have hu0 := hv.trans hvu
  have hU0 := hV.trans hVU
  have hR : 0 ≤ R := by dsimp [R, rCoord]; positivity
  have hc : 0 ≤ c := by dsimp [c, xCoord]; positivity
  have ha : 0 ≤ a := mul_nonneg hu0 hU0
  have hb : 0 ≤ b := mul_nonneg hv hV
  have hBA : A ≤ B := by dsimp [A, B]; linarith
  have hAa : A + a = (1 - u) * (1 - U) := by dsimp [A, a]; ring
  have hBb : B + b = (1 - v) * (1 - V) := by dsimp [B, b]; ring
  have hR2 : R ^ 2 = (A + a) * (B + b) := by
    dsimp [R]
    rw [mul_pow, radial_coordinate_square hvu hu, radial_coordinate_square hVU hU,
      hAa, hBb]
    ring
  have hc2 : c ^ 2 = a * b := by
    dsimp [c, a, b]
    rw [mul_pow, bias_coordinate_square hv hvu, bias_coordinate_square hV hVU]
    ring
  change volume {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ (R * s - c) ^ 2 < A * B} =
    if 0 < A then ENNReal.ofReal (2 * Real.sqrt (A * B) / R) else 0
  by_cases hA : 0 < A
  · rw [if_pos hA]
    have hB : 0 < B := hA.trans_le hBA
    have hcs := two_term_sqrt_cauchy hA.le hB.le ha hb
    have hsR : Real.sqrt ((A + a) * (B + b)) = R := by rw [← hR2, Real.sqrt_sq hR]
    have hsc : Real.sqrt (a * b) = c := by rw [← hc2, Real.sqrt_sq hc]
    rw [hsR, hsc] at hcs
    have hd : 0 < Real.sqrt (A * B) := Real.sqrt_pos.mpr (mul_pos hA hB)
    have hRp : 0 < R := by linarith
    apply angular_interval_volume hRp hc hA hB
    linarith
  · rw [if_neg hA]
    have hA0 : A ≤ 0 := le_of_not_gt hA
    by_cases hB : 0 ≤ B
    · have hAB : A * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA0 hB
      have he : {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ (R * s - c) ^ 2 < A * B} = ∅ := by
        ext s
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨_, _, hh⟩
        nlinarith [sq_nonneg (R * s - c)]
      rw [he, measure_empty]
    · have hBn : B ≤ 0 := (lt_of_not_ge hB).le
      have hAa0 : 0 ≤ A + a := by
        rw [hAa]
        exact mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hU)
      have hBb0 : 0 ≤ B + b := by
        rw [hBb]
        exact mul_nonneg (sub_nonneg.mpr (hvu.trans hu))
          (sub_nonneg.mpr (hVU.trans hU))
      have he := negative_sector_empty hR hc (neg_nonneg.mpr hA0)
        (neg_nonneg.mpr hBn) (by linarith : -A ≤ a) (by linarith : -B ≤ b)
        (by convert hR2 using 1 <;> ring) hc2
      have he' : {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ (R * s - c) ^ 2 < A * B} = ∅ := by
        simpa only [neg_mul_neg] using he
      rw [he', measure_empty]


def coordinateMap (p : ℝ × ℝ) : ℝ × ℝ := (xCoord p.1 p.2, rCoord p.1 p.2)

private def coordinateDerivative (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![Real.sqrt p.2 / (2 * Real.sqrt p.1), Real.sqrt p.1 / (2 * Real.sqrt p.2);
       -Real.sqrt (1 - p.2) / (2 * Real.sqrt (1 - p.1)),
       -Real.sqrt (1 - p.1) / (2 * Real.sqrt (1 - p.2))]).toContinuousLinearMap

private theorem hasFDerivAt_coordinateMap {p : ℝ × ℝ} (hu : 0 < p.1) (hv : 0 < p.2)
    (hu1 : p.1 < 1) (hv1 : p.2 < 1) :
    HasFDerivAt coordinateMap (coordinateDerivative p) p := by
  unfold coordinateDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  have hs1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sqrt hu.ne'
  have hs2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sqrt hv.ne'
  have ht1 := ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).const_sub 1).sqrt
    (by linarith : 1 - p.1 ≠ 0)
  have ht2 := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_sub 1).sqrt
    (by linarith : 1 - p.2 ≠ 0)
  convert! hs1.mul hs2 |>.prodMk (ht1.mul ht2) using 1
  all_goals first | rfl | (ext q <;> simp [ContinuousLinearMap.prod_apply,
      smul_eq_mul,
       smul_smul, add_comm, mul_comm, div_eq_mul_inv])

private theorem det_coordinateDerivative {p : ℝ × ℝ} (hu : 0 < p.1) (hv : 0 < p.2)
    (hu1 : p.1 < 1) (hv1 : p.2 < 1) :
    (coordinateDerivative p).det =
      (p.1 - p.2) / (4 * xCoord p.1 p.2 * rCoord p.1 p.2) := by
  have hsu : Real.sqrt p.1 ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hsv : Real.sqrt p.2 ≠ 0 := (Real.sqrt_pos.mpr hv).ne'
  have htu : Real.sqrt (1 - p.1) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have htv : Real.sqrt (1 - p.2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hsu2 := Real.sq_sqrt hu.le
  have hsv2 := Real.sq_sqrt hv.le
  have htu2 := Real.sq_sqrt (show 0 ≤ 1 - p.1 by linarith)
  have htv2 := Real.sq_sqrt (show 0 ≤ 1 - p.2 by linarith)
  unfold coordinateDerivative xCoord rCoord
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  field_simp
  nlinarith


def rootDomain : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1}

def radialBody : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}

private theorem coordinateMap_injective : Set.InjOn coordinateMap rootDomain := by
  intro p hp q hq he
  have hp' : 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1 := hp
  have hq' : 0 < q.2 ∧ q.2 < q.1 ∧ q.1 < 1 := hq
  have hpu : 0 < p.1 := hp'.1.trans hp'.2.1
  have hqu : 0 < q.1 := hq'.1.trans hq'.2.1
  have hx : xCoord p.1 p.2 = xCoord q.1 q.2 := congrArg Prod.fst he
  have hr : rCoord p.1 p.2 = rCoord q.1 q.2 := congrArg Prod.snd he
  have h1 := root_coordinates hp'.1.le hp'.2.1.le hp'.2.2.le hpu
  have h2 := root_coordinates hq'.1.le hq'.2.1.le hq'.2.2.le hqu
  rw [hx, hr] at h1
  exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)

-- The inverse roots satisfy two quadratic equations with simultaneous radical constraints.
set_option maxHeartbeats 2000000 in
private theorem coordinateMap_surjective : radialBody ⊆ coordinateMap '' rootDomain := by
  intro p hp
  have hp' : 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1 := hp
  let x := p.1
  let r := p.2
  let a := Real.sqrt ((1 + x) ^ 2 - r ^ 2)
  let b := Real.sqrt ((1 - x) ^ 2 - r ^ 2)
  let h := (a + b) / 2
  let g := (a - b) / 2
  have hx : 0 < x := hp'.1
  have hr : 0 < r := hp'.2.1
  have hbody : x + r < 1 := hp'.2.2
  have hx1 : x < 1 := by linarith
  have haArg : 0 < (1 + x) ^ 2 - r ^ 2 := by nlinarith
  have hbArg : 0 < (1 - x) ^ 2 - r ^ 2 := by nlinarith
  have ha : 0 < a := Real.sqrt_pos.mpr haArg
  have hb : 0 < b := Real.sqrt_pos.mpr hbArg
  have ha2 : a ^ 2 = (1 + x) ^ 2 - r ^ 2 := Real.sq_sqrt haArg.le
  have hb2 : b ^ 2 = (1 - x) ^ 2 - r ^ 2 := Real.sq_sqrt hbArg.le
  have hab : b < a := by nlinarith
  have hapos : a < 1 + x := by nlinarith [sq_pos_of_pos hr]
  have hbpos : b < 1 - x := by nlinarith [sq_pos_of_pos hr]
  have hh : 0 < h := by dsimp [h]; linarith
  have hg : 0 < g := by dsimp [g]; linarith
  have hgh : g < h := by dsimp [g, h]; linarith
  have hh1 : h < 1 := by dsimp [h]; linarith
  have hg1 : g < 1 := hgh.trans hh1
  have hxEq : h * g = x := by dsimp [h, g]; nlinarith only [ha2, hb2]
  have hsEq : h ^ 2 + g ^ 2 = 1 + x ^ 2 - r ^ 2 := by dsimp [h, g]; nlinarith only [ha2, hb2]
  have hrEq : (1 - h ^ 2) * (1 - g ^ 2) = r ^ 2 := by
    calc
      (1 - h ^ 2) * (1 - g ^ 2) = 1 - (h ^ 2 + g ^ 2) + (h * g) ^ 2 := by ring
      _ = r ^ 2 := by rw [hxEq, hsEq]; ring
  refine ⟨(h ^ 2, g ^ 2), ?_, ?_⟩
  · change 0 < g ^ 2 ∧ g ^ 2 < h ^ 2 ∧ h ^ 2 < 1
    exact ⟨sq_pos_of_pos hg, by nlinarith, by nlinarith⟩
  · apply Prod.ext
    · change xCoord (h ^ 2) (g ^ 2) = x
      rw [xCoord, Real.sqrt_sq hh.le, Real.sqrt_sq hg.le]
      exact hxEq
    · change rCoord (h ^ 2) (g ^ 2) = r
      unfold rCoord
      rw [← Real.sqrt_mul (by nlinarith : 0 ≤ 1 - h ^ 2), hrEq, Real.sqrt_sq hr.le]


private theorem coordinateMap_mapsTo : MapsTo coordinateMap rootDomain radialBody := by
  intro p hp
  have hp' : 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1 := hp
  have hpu : 0 < p.1 := hp'.1.trans hp'.2.1
  have h := coordinates_in_body hp'.1.le hp'.2.1.le hp'.2.2.le
  have hx : 0 < xCoord p.1 p.2 :=
    mul_pos (Real.sqrt_pos.mpr hpu) (Real.sqrt_pos.mpr hp'.1)
  have hr : 0 < rCoord p.1 p.2 := by
    unfold rCoord
    exact mul_pos (Real.sqrt_pos.mpr (by linarith))
      (Real.sqrt_pos.mpr (by linarith))
  have hx2 := bias_coordinate_square hp'.1.le hp'.2.1.le
  have hr2 := radial_coordinate_square hp'.2.1.le hp'.2.2.le
  have hsu := Real.sq_sqrt hpu.le
  have hsv := Real.sq_sqrt hp'.1.le
  have hdiff : (1 - xCoord p.1 p.2) ^ 2 - rCoord p.1 p.2 ^ 2 =
      (Real.sqrt p.1 - Real.sqrt p.2) ^ 2 := by
    rw [hr2]
    have hxEq : xCoord p.1 p.2 = Real.sqrt p.1 * Real.sqrt p.2 := rfl
    nlinarith only [hx2, hsu, hsv, hxEq]
  have hs : 0 < Real.sqrt p.1 - Real.sqrt p.2 :=
    sub_pos.mpr (Real.sqrt_lt_sqrt hp'.1.le hp'.2.1)
  have hbody : xCoord p.1 p.2 + rCoord p.1 p.2 < 1 := by
    by_contra hn
    have he : xCoord p.1 p.2 + rCoord p.1 p.2 = 1 :=
      le_antisymm h.2.2 (le_of_not_gt hn)
    have hre : rCoord p.1 p.2 = 1 - xCoord p.1 p.2 := by linarith only [he]
    rw [hre] at hdiff
    nlinarith only [hdiff, sq_pos_of_pos hs]
  exact ⟨hx, hr, hbody⟩

private theorem coordinateMap_image : coordinateMap '' rootDomain = radialBody :=
  Subset.antisymm (by rintro q ⟨p, hp, rfl⟩; exact coordinateMap_mapsTo hp)
    coordinateMap_surjective

theorem measurableSet_rootDomain : MeasurableSet rootDomain := by
  unfold rootDomain
  measurability

theorem coordinate_change_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in radialBody, f p) = ∫⁻ p in rootDomain,
      ENNReal.ofReal ((p.1 - p.2) / (4 * xCoord p.1 p.2 * rCoord p.1 p.2)) *
        f (coordinateMap p) := by
  have hd : ∀ p ∈ rootDomain,
      HasFDerivWithinAt coordinateMap (coordinateDerivative p) rootDomain p := by
    intro p hp
    have hp' : 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1 := hp
    exact (hasFDerivAt_coordinateMap (hp'.1.trans hp'.2.1) hp'.1
      hp'.2.2 (hp'.2.1.trans hp'.2.2)).hasFDerivWithinAt
  rw [← coordinateMap_image,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_rootDomain hd
      coordinateMap_injective]
  apply setLIntegral_congr_fun measurableSet_rootDomain
  intro p hp
  have hp' : 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1 := hp
  dsimp only
  rw [det_coordinateDerivative (hp'.1.trans hp'.2.1) hp'.1 hp'.2.2
    (hp'.2.1.trans hp'.2.2), abs_of_nonneg]
  apply div_nonneg (sub_nonneg.mpr hp'.2.1.le)
  unfold xCoord rCoord
  positivity


end D5.S3.Quantum.Measurement.OrderedRootCoordinates
