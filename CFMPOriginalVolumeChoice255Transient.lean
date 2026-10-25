import CFMPOriginalCovolumeNeighborhood251Transient
import Mathlib.Geometry.Euclidean.Volume.Measure

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix BigOperators Topology ENNReal
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalFutureFrame435Transient
open CFMPOriginalCovolumeNeighborhood251Transient

namespace CFMPOriginalVolumeChoice255Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

def originalContract (l : Lengths) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) : Prop :=
  ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l w.val) ᵥ* M ∧
    lorentz y y = -1 ∧ 0 < y 3 ∧
    (f w).coordinates.val = WithLp.toLp 2
      (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))

theorem original_lift (l : Lengths) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (f : cutBody l → HyperbolicThreeSpace) (hf : originalContract l M f)
    (w : cutBody l) : lift (f w) = (radial l w.val) ᵥ* M := by
  obtain ⟨y,hy,hu,ht,hcoord⟩ := hf w
  exact (lift_of_coordinates (f w) y hu ht hcoord).trans hy

theorem original_distance_independent
    (l : Lengths) (M N : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hN : ∀ i j, lorentz (N i) (N j) = lengthGram l i j)
    (f g : cutBody l → HyperbolicThreeSpace)
    (hf : originalContract l M f) (hg : originalContract l N g)
    (u v : cutBody l) : dist (f u) (f v) = dist (g u) (g v) := by
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  have hp : lorentz (lift (f u)) (lift (f v)) =
      lorentz (lift (g u)) (lift (g v)) := by
    rw [original_lift l M f hf u,original_lift l M f hf v,
      original_lift l N g hg u,original_lift l N g hg v,
      frame_pair l M hM,frame_pair l N hN]
  rw [lift_cosh,lift_cosh] at hp
  exact neg_injective hp

theorem normalized_range_measure_eq_of_dist_eq
    {α : Type*} (f g : α → HyperbolicThreeSpace) (hfi : Function.Injective f)
    (hd : ∀ u v, dist (g u) (g v) = dist (f u) (f v)) (d : ℕ) :
    (Measure.euclideanHausdorffMeasure d : Measure HyperbolicThreeSpace) (range f) =
      (Measure.euclideanHausdorffMeasure d : Measure HyperbolicThreeSpace) (range g) := by
  letI : MetricSpace α := MetricSpace.induced f hfi inferInstance
  letI : MeasurableSpace α := borel α
  letI : BorelSpace α := ⟨rfl⟩
  have hIsoF : Isometry f := by
    apply Isometry.of_dist_eq
    intro u v
    rfl
  have hIsoG : Isometry g := by
    apply Isometry.of_dist_eq
    intro u v
    exact hd u v
  have hF := hIsoF.euclideanHausdorffMeasure_image (d := d) (univ : Set α)
  have hG := hIsoG.euclideanHausdorffMeasure_image (d := d) (univ : Set α)
  simpa only [image_univ] using hF.trans hG.symm

theorem original_normalized_volume_independent
    (l : Lengths) (M N : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hN : ∀ i j, lorentz (N i) (N j) = lengthGram l i j)
    (f g : cutBody l → HyperbolicThreeSpace) (hfi : Function.Injective f)
    (hf : originalContract l M f) (hg : originalContract l N g) :
    (Measure.euclideanHausdorffMeasure 3 : Measure HyperbolicThreeSpace) (range f) =
      (Measure.euclideanHausdorffMeasure 3 : Measure HyperbolicThreeSpace) (range g) := by
  exact normalized_range_measure_eq_of_dist_eq f g hfi
    (fun u v => (original_distance_independent l M N hM hN f g hf hg u v).symm) 3

theorem physicalCovolume_eq_of_original_realizations
    (l : Lengths) (M N : Matrix (Fin 4) (Fin 4) ℝ)
    (hM : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (hN : ∀ i j, lorentz (N i) (N j) = lengthGram l i j)
    (F G : RealizationFamily) (hFi : Function.Injective (F l))
    (hF : originalContract l M (F l)) (hG : originalContract l N (G l)) :
    physicalCovolume F l = physicalCovolume G l := by
  have hm := original_normalized_volume_independent l M N hM hN (F l) (G l) hFi hF hG
  simp only [physicalCovolume,physicalVolume,hm]

end CFMPOriginalVolumeChoice255Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPOriginalVolumeChoice255Transient.original_distance_independent,
      ``CFMPOriginalVolumeChoice255Transient.original_normalized_volume_independent,
      ``CFMPOriginalVolumeChoice255Transient.physicalCovolume_eq_of_original_realizations] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP255 source theorem absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP255 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP255 CHECKED {name} axioms={axioms}"
