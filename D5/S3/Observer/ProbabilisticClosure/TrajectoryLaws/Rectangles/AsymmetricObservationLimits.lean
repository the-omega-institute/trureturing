/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/AsymmetricObservationLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual asymmetric erased-bit conditionals converge in both ordered half-line limits. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ErasedExteriorFiltration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function Filter
open scoped Topology Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.AsymmetricObservationLimits

abbrev Visible := ℤ → Bool

/-- Chronological observations with independently chosen left and right lengths. -/
def observation (l r : ℕ) (z : Visible) := (leftWord l z, rightWord r z)

/-- Actual conditional probability under the supplied single visible law. -/
def mean {E : Type*} [MeasurableSpace E] (μ : Measure Visible)
    [IsProbabilityMeasure μ] (o : Visible → E) : Visible → ℝ :=
  bitPredictor μ (fun z => z 0) o ∘ o

/-- Almost-sure and mean-square convergence; the latter is convergence in L². -/
def MeanSquareLimit (μ : Measure Visible) (f : ℕ → Visible → ℝ) (g : Visible → ℝ) : Prop :=
  (∀ᵐ z ∂μ, Tendsto (fun n => f n z) atTop (𝓝 (g z))) ∧
    Tendsto (fun n => ∫ z, (f n z - g z)^2 ∂μ) atTop (𝓝 0)

private def leftField (n : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (leftWord n) inferInstance
private def rightField (n : ℕ) : MeasurableSpace Visible :=
  MeasurableSpace.comap (rightWord n) inferInstance

private theorem pair_field {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (a : Visible → E) (b : Visible → F) :
    MeasurableSpace.comap (fun z => (a z,b z)) inferInstance =
      MeasurableSpace.comap a inferInstance ⊔ MeasurableSpace.comap b inferInstance := by
  simp only [MeasurableSpace.prod, MeasurableSpace.comap_sup,
    MeasurableSpace.comap_comp, Function.comp_def]

private theorem left_mono : Monotone leftField := by
  apply monotone_nat_of_le_succ
  intro n
  apply MeasurableSpace.comap_le_comap_of_eq_comp
    (fun w : Fin (n+1) → Bool => fun i : Fin n => w i.succ) (by fun_prop)
  funext z i
  dsimp [leftWord]
  apply congrArg z
  push_cast
  omega

private theorem right_mono : Monotone rightField := by
  apply monotone_nat_of_le_succ
  intro n
  exact MeasurableSpace.comap_le_comap_of_eq_comp
    (fun w : Fin (n+1) → Bool => fun i : Fin n => w i.castSucc) (by fun_prop) rfl

private theorem left_sup : (⨆ n, leftField n) = MeasurableSpace.comap before inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (fun w : ℕ → Bool => fun i : Fin n => w (n-1-i.val)) (by fun_prop)
    funext z i
    dsimp [leftWord,before]
    apply congrArg z
    have hi := i.isLt
    omega
  · have hm (n : ℕ) : @Measurable Visible Bool (⨆ n, leftField n) inferInstance
        (fun z => before z n) := by
      have h : Measurable[leftField (n+1)] (fun z => leftWord (n+1) z 0) :=
        (measurable_pi_apply 0).comp (Measurable.of_comap_le le_rfl)
      convert h.mono (le_iSup leftField (n+1)) le_rfl using 1
      funext z
      dsimp [leftWord,before]
      congr 1
    letI : MeasurableSpace Visible := ⨆ n, leftField n
    exact (Measurable.of_eval hm).comap_le

private theorem right_sup : (⨆ n, rightField n) = MeasurableSpace.comap after inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun w : ℕ → Bool => fun i : Fin n => w i.val) (by fun_prop) rfl
  · have hm (n : ℕ) : @Measurable Visible Bool (⨆ n, rightField n) inferInstance
        (fun z => after z n) := by
      have h : Measurable[rightField (n+1)] (fun z => rightWord (n+1) z (Fin.last n)) :=
        (measurable_pi_apply (Fin.last n)).comp (Measurable.of_comap_le le_rfl)
      exact h.mono (le_iSup rightField (n+1)) le_rfl
    letI : MeasurableSpace Visible := ⨆ n, rightField n
    exact (Measurable.of_eval hm).comap_le

private theorem mean_bounds {E : Type*} [MeasurableSpace E]
    (μ : Measure Visible) [IsProbabilityMeasure μ] (o : Visible → E) (z : Visible) :
    0 ≤ mean μ o z ∧ mean μ o z ≤ 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

private theorem observation_limit {E : ℕ → Type*} [∀ n, MeasurableSpace (E n)]
    {F : Type*} [MeasurableSpace F] (μ : Measure Visible) [IsProbabilityMeasure μ]
    (o : ∀ n, Visible → E n) (v : Visible → F) (ho : ∀ n, Measurable (o n))
    (hv : Measurable v)
    (hmono : Monotone (fun n => MeasurableSpace.comap (o n) inferInstance))
    (hsup : (⨆ n, MeasurableSpace.comap (o n) inferInstance) =
      MeasurableSpace.comap v inferInstance) :
    MeanSquareLimit μ (fun n => mean μ (o n)) (mean μ v) := by
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Visible) :=
    ⟨fun n => MeasurableSpace.comap (o n) inferInstance,hmono,fun n => (ho n).comap_le⟩
  have hp (n : ℕ) := bitPredictor_condExp μ (fun z : Visible => z 0) (o n)
    (measurable_pi_apply 0) (ho n)
  have hq := bitPredictor_condExp μ (fun z : Visible => z 0) v
    (measurable_pi_apply 0) hv
  have hc := tendsto_ae_condExp (μ := μ) (ℱ := ℱ) erasedBit
  have ha : ∀ᵐ z ∂μ, Tendsto (fun n => mean μ (o n) z) atTop (𝓝 (mean μ v z)) := by
    have hall := ae_all_iff.mpr hp
    filter_upwards [hc,hall,hq] with z hz hpz hqz
    change Tendsto (fun n => μ[erasedBit | MeasurableSpace.comap (o n) inferInstance] z)
      atTop (𝓝 (μ[erasedBit | ⨆ n, MeasurableSpace.comap (o n) inferInstance] z)) at hz
    rw [hsup] at hz
    exact (hz.congr (fun n => (hpz n).symm)).trans (by simpa only [mean,Function.comp_apply] using tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun _ => hqz.symm))
  refine ⟨ha,?_⟩
  have hd := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n z => (mean μ (o n) z-mean μ v z)^2) (f := fun _ => (0 : ℝ))
    (fun _ => (1 : ℝ))
    (fun n => (((bitPredictor_measurable μ _ _).comp (ho n)).sub
      ((bitPredictor_measurable μ _ _).comp hv)).pow_const 2 |>.aestronglyMeasurable)
    (integrable_const 1) (fun n => Filter.Eventually.of_forall fun z => by
      obtain ⟨ha,hb⟩ := mean_bounds μ (o n) z
      obtain ⟨hc,hd⟩ := mean_bounds μ v z
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [mul_nonneg ha hc, mul_nonneg (1-hb) (1-hd)])
    (ha.mono fun z hz => by simpa using (hz.sub tendsto_const_nhds).pow 2)
  simpa using hd

/-- Both ordered completions use actual conditional distributions under one law.
The finite-side length may be zero; the opposite complete half-line is retained. -/
theorem ordered_half_line_limits (μ : Measure Visible) [IsProbabilityMeasure μ] (j : ℕ) :
    (∀ n : ℕ, MeanSquareLimit μ (fun k => mean μ (observation k n))
      (mean μ (rightObservation n))) ∧
    (∀ n : ℕ, MeanSquareLimit μ (fun k => mean μ (observation n k))
      (mean μ (leftObservation n))) ∧
    MeanSquareLimit μ (fun n => mean μ (rightObservation n)) (mean μ exterior) ∧
    MeanSquareLimit μ (fun n => mean μ (leftObservation n)) (mean μ exterior) ∧
    MeanSquareLimit μ (fun n => mean μ (observation j n)) (mean μ (leftObservation j)) ∧
    MeanSquareLimit μ (fun n => mean μ (observation n j)) (mean μ (rightObservation j)) := by
  have hfield (l r : ℕ) : MeasurableSpace.comap (observation l r) inferInstance =
      leftField l ⊔ rightField r := pair_field _ _
  have hL (n : ℕ) : MeasurableSpace.comap (leftObservation n) inferInstance =
      leftField n ⊔ MeasurableSpace.comap after inferInstance := pair_field _ _
  have hR (n : ℕ) : MeasurableSpace.comap (rightObservation n) inferInstance =
      MeasurableSpace.comap before inferInstance ⊔ rightField n := pair_field _ _
  have hE : MeasurableSpace.comap exterior inferInstance =
      MeasurableSpace.comap before inferInstance ⊔ MeasurableSpace.comap after inferInstance :=
    pair_field _ _
  have hfiniteL (n : ℕ) := observation_limit μ (fun k => observation k n) (rightObservation n)
    (fun k => by unfold observation leftWord rightWord; fun_prop)
    (by unfold rightObservation before rightWord; fun_prop)
    (by intro a b hab; simp only [hfield]; exact sup_le_sup (left_mono hab) le_rfl)
    (by simp only [hfield,hR,iSup_sup_eq,left_sup,iSup_const])
  have hfiniteR (n : ℕ) := observation_limit μ (fun k => observation n k) (leftObservation n)
    (fun k => by unfold observation leftWord rightWord; fun_prop)
    (by unfold leftObservation after leftWord; fun_prop)
    (by intro a b hab; simp only [hfield]; exact sup_le_sup le_rfl (right_mono hab))
    (by simp only [hfield,hL,iSup_sup_eq,right_sup,iSup_const])
  refine ⟨hfiniteL,hfiniteR,?_,?_,hfiniteR j,hfiniteL j⟩
  · exact observation_limit μ rightObservation exterior
      (fun n => by unfold rightObservation before rightWord; fun_prop)
      (by unfold exterior before after; fun_prop)
      (by intro a b hab; simp only [hR]; exact sup_le_sup le_rfl (right_mono hab))
      (by simp only [hR,hE,iSup_sup_eq,right_sup,iSup_const])
  · exact observation_limit μ leftObservation exterior
      (fun n => by unfold leftObservation after leftWord; fun_prop)
      (by unfold exterior before after; fun_prop)
      (by intro a b hab; simp only [hL]; exact sup_le_sup (left_mono hab) le_rfl)
      (by simp only [hL,hE,iSup_sup_eq,left_sup,iSup_const])

#print axioms ordered_half_line_limits
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.AsymmetricObservationLimits
