/- GID: D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus
   generality: G
   mirror-B: D5/B/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual smooth periodic density and characteristic transport -/
import D5.S3.Geometry.ProbabilityTransport.PeriodicDensityModel

/-!
# PeriodicDensityCalculus

Actual smooth periodic density transport on the closed time slab.
-/

set_option maxHeartbeats 2000000


/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the verbatim lean-pool-LICENSE archive in Blueprint/D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport.scribe.cs.
Authors: Scott Armstrong and Vlad Vicol; Scott Armstrong and Tuomo Kuusi
Portions from CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining),
commit c7ddd76, as recorded in the supplier file headers.
MODIFIED 2026-10-20: selected declarations only, Mathlib imports substituted.
Supplier bodies retained except the documented exact diagnostic API repair.
Selected supplier bodies are consumed by the actual density proof below.
-/
noncomputable section
open MeasureTheory Set intervalIntegral
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

private theorem hasDerivAt_insertNth {n : ℕ} (i : Fin (n + 1)) (z : Vec n) (t₀ : ℝ) :
    HasDerivAt (fun t => (i.insertNth t z : Vec (n + 1))) (basisVec i) t₀ := by
  have hfun : (fun t : ℝ => (i.insertNth t z : Vec (n + 1)))
      = fun t => t • (basisVec i) + i.insertNth 0 z := by
    funext t
    funext j
    rcases eq_or_ne j i with h | h
    · subst h
      simp [Fin.insertNth_apply_same, basisVec]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
      simp [Fin.insertNth_apply_succAbove, basisVec, Fin.succAbove_ne]
  rw [hfun]
  simpa using ((hasDerivAt_id t₀).smul_const (basisVec i)).add_const (i.insertNth 0 z)

end Homogenization
open Homogenization
namespace AVenhance.Infra.Torus

def unitCellAt (d : ℕ) (a : Fin d → ℝ) : Set (Vec d) :=
  {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}

def unitCell (d : ℕ) : Set (Vec d) := unitCellAt d (fun _ => 0)

private theorem measurableSet_unitCellAt (d : ℕ) (a : Fin d → ℝ) :
    MeasurableSet (unitCellAt d a) := by
  simpa [unitCellAt] using MeasurableSet.univ_pi'
    (fun i => (measurableSet_Ioc : MeasurableSet (Set.Ioc (a i) (a i + 1))))

private theorem measurableSet_unitCell (d : ℕ) : MeasurableSet (unitCell d) := by
  rw [unitCell]
  exact measurableSet_unitCellAt d (fun _ => 0)

def intVector {d : ℕ} (k : Fin d → ℤ) : Vec d := fun i => (k i : ℝ)

def IsZdPeriodic {d : ℕ} {α : Type*} (f : Vec d → α) : Prop :=
  ∀ k : Fin d → ℤ, ∀ x : Vec d, f (x + intVector k) = f x

def toUnitTorus (d : ℕ) (x : Vec d) : UnitAddTorus (Fin d) :=
  fun i => (x i : UnitAddCircle)

def fromUnitTorus {d : ℕ} {α : Type*}
    (f : UnitAddTorus (Fin d) → α) : Vec d → α :=
  fun x => f (toUnitTorus d x)

private theorem isZdPeriodic_fromUnitTorus {d : ℕ} {α : Type*} (f : UnitAddTorus (Fin d) → α)
    : IsZdPeriodic (fromUnitTorus f) := by
  intro k x
  unfold fromUnitTorus
  congr 1
  funext i
  change ((x i + (k i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hk : ((k i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k i, by simp⟩
  rw [hk, add_zero]

private theorem integral_peel_coord {n : ℕ} (i : Fin (n + 1)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec (n + 1) → E}
    (hf : Integrable f (volume : Measure (Vec (n + 1)))) :
    (∫ x, f x ∂(volume : Measure (Vec (n + 1)))) =
      ∫ z : Vec n, ∫ t : ℝ, f (i.insertNth t z)
        ∂(volume : Measure ℝ) ∂(volume : Measure (Vec n)) := by
  classical
  let μ : ∀ _ : Fin (n + 1), Measure ℝ := fun _ => volume
  have hmp := measurePreserving_piFinSuccAbove μ i
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  have hvol : (volume : Measure (Vec (n + 1))) = Measure.pi μ := volume_pi
  have hf' : Integrable (fun p => f (e.symm p))
      ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))) := by
    have hpi : Integrable f (Measure.pi μ) := by rw [← hvol]; exact hf
    exact hmp.symm.integrable_comp_of_integrable hpi
  rw [hvol, ← hmp.symm.integral_comp' f, integral_prod_symm _ hf']
  rfl

private theorem mem_unitCell_insertNth_iff {n : ℕ} (i : Fin (n + 1)) (t : ℝ)
    (z : Vec n) :
    i.insertNth t z ∈ unitCell (n + 1) ↔ t ∈ Set.Ioc (0 : ℝ) 1 ∧ z ∈ unitCell n := by
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, i.forall_iff_succAbove,
    i.insertNth_apply_same, i.insertNth_apply_succAbove, zero_add]

private theorem integral_unitCell_peel_coord {n : ℕ} (i : Fin (n + 1))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec (n + 1) → E}
    (hf : IntegrableOn f (unitCell (n + 1))) :
    (∫ x in unitCell (n + 1), f x) =
      ∫ z in unitCell n, ∫ t in Set.Ioc (0 : ℝ) 1, f (i.insertNth t z) := by
  let g : Vec (n + 1) → E := (unitCell (n + 1)).indicator f
  have hg : Integrable g (volume : Measure (Vec (n + 1))) :=
    hf.integrable_indicator (measurableSet_unitCell (n + 1))
  calc
    ∫ x in unitCell (n + 1), f x = ∫ x, g x := by
      symm
      exact integral_indicator (measurableSet_unitCell (n + 1))
    _ = ∫ z : Vec n, ∫ t : ℝ, g (i.insertNth t z) :=
      integral_peel_coord i hg
    _ = ∫ z in unitCell n, ∫ t in Set.Ioc (0 : ℝ) 1, f (i.insertNth t z) := by
      have hpoint (z : Vec n) (t : ℝ) :
          g (i.insertNth t z) =
          (unitCell n).indicator
              (fun z => (Set.Ioc (0 : ℝ) 1).indicator
                (fun t => f (i.insertNth t z)) t) z := by
        classical
        simp only [g, Set.indicator_apply, mem_unitCell_insertNth_iff]
        by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1 <;>
          by_cases hz : z ∈ unitCell n <;> simp [ht, hz]
      calc
        ∫ z : Vec n, ∫ t : ℝ, g (i.insertNth t z) =
            ∫ z, ∫ t,
              (unitCell n).indicator
                (fun z => (Set.Ioc (0 : ℝ) 1).indicator
                  (fun t => f (i.insertNth t z)) t) z := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with z
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          exact hpoint z t
        _ = ∫ z in unitCell n, ∫ t,
              (Set.Ioc (0 : ℝ) 1).indicator
                (fun t => f (i.insertNth t z)) t := by
          rw [integral_integral_indicator _ (measurableSet_unitCell n)]
        _ = ∫ z in unitCell n, ∫ t in Set.Ioc (0 : ℝ) 1,
              f (i.insertNth t z) := by
          apply setIntegral_congr_ae (measurableSet_unitCell n)
          filter_upwards with z
          intro _hz
          exact integral_indicator measurableSet_Ioc

noncomputable def coordDeriv {d : ℕ} (i : Fin d) (f : Vec d → ℂ) (x : Vec d) : ℂ :=
  fderiv ℝ f x (basisVec i)

def Calculus.closedUnitCell (d : ℕ) : Set (Vec d) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

private theorem Calculus.isCompact_closedUnitCell (d : ℕ) : IsCompact (Calculus.closedUnitCell d) := by
  simpa [Calculus.closedUnitCell] using
    (isCompact_univ_pi fun _ : Fin d => isCompact_Icc)

private theorem Calculus.unitCell_subset_closedUnitCell (d : ℕ) :
    unitCell d ⊆ Calculus.closedUnitCell d := by
  intro x hx
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [Calculus.closedUnitCell, Set.mem_pi, mem_univ, forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, (hx i).2⟩

private theorem Calculus.continuous_integrableOn_unitCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Vec d → E} (hf : Continuous f) : IntegrableOn f (unitCell d) := by
  exact (hf.continuousOn.integrableOn_compact (Calculus.isCompact_closedUnitCell d)).mono_set
    (Calculus.unitCell_subset_closedUnitCell d)

private theorem Calculus.insertNth_one_eq_integerTranslate {n : ℕ} (i : Fin (n + 1))
    (z : Vec n) :
    i.insertNth 1 z = i.insertNth 0 z +
      intVector (fun j => if j = i then (1 : ℤ) else 0) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [intVector, Fin.insertNth_apply_same]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp [intVector, Fin.insertNth_apply_succAbove, hji]

private theorem Calculus.periodic_insertNth_endpoints {n : ℕ} (i : Fin (n + 1))
    (z : Vec n) {f : Vec (n + 1) → ℂ} (hf : IsZdPeriodic f) :
    f (i.insertNth 1 z) = f (i.insertNth 0 z) := by
  simpa [Calculus.insertNth_one_eq_integerTranslate] using
    hf (fun j => if j = i then (1 : ℤ) else 0) (i.insertNth 0 z)

private theorem Calculus.hasDerivAt_comp_insertNth_complex {n : ℕ}
    {f : Vec (n + 1) → ℂ} (hf : Differentiable ℝ f)
    (i : Fin (n + 1)) (z : Vec n) (t : ℝ) :
    HasDerivAt (fun s => f (i.insertNth s z))
      (coordDeriv i f (i.insertNth t z)) t := by
  exact (hf (i.insertNth t z)).hasFDerivAt.comp_hasDerivAt t
    (Homogenization.hasDerivAt_insertNth i z t)

private theorem Calculus.line_integral_ibp {n : ℕ} (i : Fin (n + 1))
    {f g : Vec (n + 1) → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hpf : IsZdPeriodic f) (hpg : IsZdPeriodic g) (z : Vec n) :
    (∫ t in Set.Ioc (0 : ℝ) 1,
        f (i.insertNth t z) * coordDeriv i g (i.insertNth t z)) =
      -∫ t in Set.Ioc (0 : ℝ) 1,
        coordDeriv i f (i.insertNth t z) * g (i.insertNth t z) := by
  let u : ℝ → ℂ := fun t => f (i.insertNth t z)
  let v : ℝ → ℂ := fun t => g (i.insertNth t z)
  let u' : ℝ → ℂ := fun t => coordDeriv i f (i.insertNth t z)
  let v' : ℝ → ℂ := fun t => coordDeriv i g (i.insertNth t z)
  have hdF : Differentiable ℝ f := hf.differentiable (by simp)
  have hdG : Differentiable ℝ g := hg.differentiable (by simp)
  have hu : ∀ t, HasDerivAt u (u' t) t := fun t =>
    Calculus.hasDerivAt_comp_insertNth_complex hdF i z t
  have hv : ∀ t, HasDerivAt v (v' t) t := fun t =>
    Calculus.hasDerivAt_comp_insertNth_complex hdG i z t
  have hline : Continuous (fun t : ℝ => (i.insertNth t z : Vec (n + 1))) :=
    continuous_iff_continuousAt.2 fun t =>
      (Homogenization.hasDerivAt_insertNth i z t).continuousAt
  have hu'c : Continuous u' := by
    change Continuous (fun t => coordDeriv i f (i.insertNth t z))
    exact ((hf.continuous_fderiv (by simp)).comp hline).clm_apply continuous_const
  have hv'c : Continuous v' := by
    change Continuous (fun t => coordDeriv i g (i.insertNth t z))
    exact ((hg.continuous_fderiv (by simp)).comp hline).clm_apply continuous_const
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun x _ => hu x) (fun x _ => hv x)
    (hu'c.intervalIntegrable 0 1) (hv'c.intervalIntegrable 0 1)
  have hendF : u 1 = u 0 := by
    exact Calculus.periodic_insertNth_endpoints i z hpf
  have hendG : v 1 = v 0 := by
    exact Calculus.periodic_insertNth_endpoints i z hpg
  rw [hendF, hendG] at hIBP
  simpa [u, v, u', v', intervalIntegral.integral_of_le h01] using hIBP

private theorem integral_unitCell_coord_ibp {n : ℕ} (i : Fin (n + 1))
    {f g : Vec (n + 1) → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hpf : IsZdPeriodic f) (hpg : IsZdPeriodic g) :
    (∫ x in unitCell (n + 1), f x * coordDeriv i g x) =
      -∫ x in unitCell (n + 1), coordDeriv i f x * g x := by
  have hDf : Continuous (fun x => coordDeriv i f x) := by
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDg : Continuous (fun x => coordDeriv i g x) := by
    exact (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hfg : IntegrableOn (fun x => f x * coordDeriv i g x) (unitCell (n + 1)) :=
    Calculus.continuous_integrableOn_unitCell (hf.continuous.mul hDg)
  have hgf : IntegrableOn (fun x => coordDeriv i f x * g x) (unitCell (n + 1)) :=
    Calculus.continuous_integrableOn_unitCell (hDf.mul hg.continuous)
  rw [integral_unitCell_peel_coord i hfg, integral_unitCell_peel_coord i hgf]
  rw [← MeasureTheory.integral_neg]
  apply setIntegral_congr_ae (measurableSet_unitCell n)
  filter_upwards with z _hz
  exact Calculus.line_integral_ibp i hf hg hpf hpg z

end AVenhance.Infra.Torus

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the verbatim TauCeti-LICENSE archive in Blueprint/D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel.scribe.cs.
Authors: The Tau Ceti contributors
MODIFIED 2026-10-20: convex-set declarations and their one compact-integrability
helper extracted; unused open-set/interval theorems and Normed helper omitted.
These parameter-integration lemmas are consumed by the closed-slab density calculus.
-/
noncomputable section
universe u v
open MeasureTheory Filter Set
open scoped Topology
namespace TauCeti
variable {E : Type u} {P α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace α] [CompactSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} {ι : α → P} {g : α → ℝ} {W : Set (E × P)}
omit [NormedSpace ℝ E] [NormedSpace ℝ P] in
private theorem integrable_smul_of_continuousOn {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : E × P → H} (hg : Integrable g μ) (hι : Continuous ι) (hF : ContinuousOn F W) {x : E}
    (hx : ∀ y, (x, ι y) ∈ W) :
    Integrable (fun y ↦ g y • F (x, ι y)) μ := by
  have hφ : Continuous fun y ↦ F (x, ι y) := hF.comp_continuous (continuous_const.prodMk hι) hx
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact hg.smul_bdd C hφ.aestronglyMeasurable (ae_of_all _ fun y ↦ hC y (mem_univ y))

variable {s : Set E}

theorem _root_.Convex.hasFDerivWithinAt_integral_smul_of_contDiffOn {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hs : Convex ℝ s) (hW : UniqueDiffOn ℝ W) (hF : ContDiffOn ℝ 1 F W)
    (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) {x₀ : E} (hx₀ : x₀ ∈ s)
    (hsu : UniqueDiffWithinAt ℝ s x₀) :
    HasFDerivWithinAt (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ)
      (∫ y, g y • fderivWithin ℝ (fun x ↦ F (x, ι y)) s x₀ ∂μ) s x₀ := by
  -- the partial derivative in `x`, continuous on `W`
  set D : E × P → E →L[ℝ] G := fun p ↦ (fderivWithin ℝ F W p).comp (.inl ℝ E P)
  have hD : ContinuousOn D W :=
    (ContinuousLinearMap.precomp G (.inl ℝ E P)).continuous.comp_continuousOn
      (hF.continuousOn_fderivWithin hW le_rfl)
  have hderiv (x : E) (hx : x ∈ s) (y : α) :
      HasFDerivWithinAt (fun x ↦ F (x, ι y)) (D (x, ι y)) s x :=
    (hF.differentiableOn one_ne_zero _ (hsW x hx y)).hasFDerivWithinAt.comp x
      (hasFDerivAt_prodMk_left x (ι y)).hasFDerivWithinAt fun x' hx' ↦ hsW x' hx' y
  -- the partial derivative is uniformly close to its value at `x₀` for `x` near `x₀` in `s`
  have hunif (ε : ℝ) (hε : 0 < ε) :
      ∃ v ∈ 𝓝[s] x₀, ∀ x ∈ v, ∀ y ∈ univ, dist (D (x, ι y)) (D (x₀, ι y)) < ε :=
    isCompact_univ.mem_uniformity_of_prod (f := fun x y ↦ D (x, ι y))
      (hD.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
        fun p hp ↦ hsW _ hp.1 _) hx₀ (Metric.dist_mem_uniformity hε)
  rw [show (∫ y, g y • fderivWithin ℝ (fun x ↦ F (x, ι y)) s x₀ ∂μ) = ∫ y, g y • D (x₀, ι y) ∂μ
    from integral_congr_ae (ae_of_all _ fun y ↦ by
      dsimp only
      rw [(hderiv x₀ hx₀ y).fderivWithin hsu]),
    hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  set ε := c / ((∫ y, ‖g y‖ ∂μ) + 1)
  have hgn : 0 ≤ ∫ y, ‖g y‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  have hε : 0 < ε := div_pos hc (by linarith)
  obtain ⟨v, hv, hvD⟩ := hunif ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hv
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hδ)]
    with x hx hxδ
  -- the mean value inequality on the convex set `s ∩ ball x₀ δ`, for each parameter `y`
  have hsδ : Convex ℝ (s ∩ Metric.ball x₀ δ) := hs.inter (convex_ball x₀ δ)
  have hvD' (z : E) (hz : z ∈ s ∩ Metric.ball x₀ δ) (y : α) :
      ‖D (z, ι y) - D (x₀, ι y)‖ < ε := by
    simpa only [dist_eq_norm] using hvD z (hball ⟨hz.2, hz.1⟩) y (mem_univ y)
  have hpt (y : α) : ‖F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)‖ ≤ ε * ‖x - x₀‖ :=
    hsδ.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := fun z ↦ F (z, ι y))
      (f' := fun z ↦ D (z, ι y))
      (fun z (hz : z ∈ s ∩ Metric.ball x₀ δ) ↦ (hderiv z hz.1 y).mono inter_subset_left)
      (fun z hz ↦ (hvD' z hz y).le)
      ⟨hx₀, Metric.mem_ball_self hδ⟩ ⟨hx, hxδ⟩
  have hDx : ContinuousOn (fun p ↦ D p (x - x₀)) W :=
    (ContinuousLinearMap.apply ℝ G (x - x₀)).continuous.comp_continuousOn hD
  calc ‖(∫ y, g y • F (x, ι y) ∂μ) - (∫ y, g y • F (x₀, ι y) ∂μ) -
        (∫ y, g y • D (x₀, ι y) ∂μ) (x - x₀)‖
      = ‖∫ y, g y • (F (x, ι y) - F (x₀, ι y) - D (x₀, ι y) (x - x₀)) ∂μ‖ := by
        have hFx := integrable_smul_of_continuousOn hg hι hF.continuousOn (hsW x hx)
        have hFx₀ := integrable_smul_of_continuousOn hg hι hF.continuousOn (hsW x₀ hx₀)
        rw [ContinuousLinearMap.integral_apply
          (integrable_smul_of_continuousOn hg hι hD (hsW x₀ hx₀))]
        simp only [smul_apply, smul_sub]
        rw [integral_sub (by exact hFx.sub hFx₀ :
            Integrable (fun y ↦ g y • F (x, ι y) - g y • F (x₀, ι y)) μ)
          (integrable_smul_of_continuousOn hg hι hDx (hsW x₀ hx₀)), integral_sub hFx hFx₀]
    _ ≤ ∫ y, ‖g y‖ * (ε * ‖x - x₀‖) ∂μ := by
        refine norm_integral_le_of_norm_le ((hg.norm.mul_const _)) (ae_of_all _ fun y ↦ ?_)
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hpt y) (norm_nonneg _)
    _ = (∫ y, ‖g y‖ ∂μ) * ε * ‖x - x₀‖ := by rw [integral_mul_const, mul_assoc]
    _ ≤ c * ‖x - x₀‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith

private theorem _root_.Convex.contDiffOn_integral_smul_nat {G : Type max u v}
    [NormedAddCommGroup G] [NormedSpace ℝ G] (m : ℕ) {F : E × P → G} (hg : Integrable g μ)
    (hι : Continuous ι) (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hW : UniqueDiffOn ℝ W)
    (hF : ContDiffOn ℝ m F W) (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ m (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) s := by
  induction m generalizing G with
  | zero =>
      have hc : ContinuousOn (fun p : E × α ↦ F (p.1, ι p.2)) (s ×ˢ univ) :=
        hF.continuousOn.comp (continuous_fst.prodMk (hι.comp continuous_snd)).continuousOn
          fun p hp ↦ hsW _ hp.1 _
      refine contDiffOn_zero.2 <|
        (continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
          (ContinuousLinearMap.lsmul ℝ ℝ) isCompact_univ (f := fun x y ↦ F (x, ι y)) hc
          (fun _ _ _ h ↦ absurd (mem_univ _) h) hg.integrableOn).congr fun x _ ↦ by simp
  | succ m ih =>
      have hF' : ContDiffOn ℝ ((m : WithTop ℕ∞) + 1) F W := by exact_mod_cast hF
      have hderiv := fun x hx ↦ hs.hasFDerivWithinAt_integral_smul_of_contDiffOn hg hι hW
        (hF'.of_le le_add_self) hsW hx (hsu x hx)
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderivWithin hsu]
      refine ⟨fun x hx ↦ (hderiv x hx).differentiableWithinAt, fun h ↦ absurd h (by simp), ?_⟩
      refine (ih (F := fun p ↦ (fderivWithin ℝ F W p).comp (.inl ℝ E P))
        (((ContinuousLinearMap.precomp G (.inl ℝ E P)).contDiff.comp_contDiffOn
          (hF'.fderivWithin hW le_rfl)).congr fun _ _ ↦ by simp)).congr fun x hx ↦ ?_
      rw [(hderiv x hx).fderivWithin (hsu x hx)]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      have hpart : HasFDerivWithinAt (fun x ↦ F (x, ι y))
          ((fderivWithin ℝ F W (x, ι y)).comp (.inl ℝ E P)) s x :=
        ((hF'.of_le le_add_self).differentiableOn one_ne_zero _
          (hsW x hx y)).hasFDerivWithinAt.comp x
            (hasFDerivAt_prodMk_left x (ι y)).hasFDerivWithinAt fun x' hx' ↦ hsW x' hx' y
      dsimp only
      rw [hpart.fderivWithin (hsu x hx)]

theorem _root_.Convex.contDiffOn_integral_smul_of_contDiffOn {G : Type v} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {n : ℕ∞} {F : E × P → G} (hg : Integrable g μ) (hι : Continuous ι)
    (hs : Convex ℝ s) (hsu : UniqueDiffOn ℝ s) (hW : UniqueDiffOn ℝ W) (hF : ContDiffOn ℝ n F W)
    (hsW : ∀ x ∈ s, ∀ y, (x, ι y) ∈ W) :
    ContDiffOn ℝ n (fun x ↦ ∫ y, g y • F (x, ι y) ∂μ) s := by
  let eG : Type max u v := ULift.{u} G
  let isoG : eG ≃L[ℝ] G := ContinuousLinearEquiv.ulift
  have he : ContDiffOn ℝ n (fun x ↦ ∫ y, g y • isoG.symm (F (x, ι y)) ∂μ) s := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m hm
    exact hs.contDiffOn_integral_smul_nat m hg hι hsu hW
      (isoG.symm.contDiff.comp_contDiffOn (hF.of_le (by exact_mod_cast hm))) hsW
  refine (isoG.contDiff.comp_contDiffOn he).congr fun x _ ↦ ?_
  have hsmul : ∀ y, g y • isoG.symm (F (x, ι y)) = isoG.symm (g y • F (x, ι y)) :=
    fun y ↦ (map_smul _ _ _).symm
  simp only [Function.comp_apply, hsmul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.apply_symm_apply]

end TauCeti

end



noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport
local notation "PC" => AVenhance.Infra.Torus.coordDeriv

theorem periodic_haar_ibp {d : ℕ} (f : Torus d → ℝ) (V : Torus d → Euclid d)
    (hf : ContDiff ℝ 1 (fun a : Euclid d => f (quotient d a)))
    (hV : ContDiff ℝ 1 (fun a : Euclid d => V (quotient d a))) :
    (∫ x, f x * divergence V x ∂haar d) =
      -(∫ x, inner ℝ (gradient f x) (V x) ∂haar d) := by
  classical
  cases d with
  | zero => simp [divergence, PiLp.inner_apply]
  | succ n =>
    let P : (Fin (n + 1) → ℝ) ≃L[ℝ] Euclid (n + 1) :=
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm
    have hcell (g : Torus (n + 1) → ℝ) :
        (∫ x, g x ∂haar (n + 1)) =
          ∫ z in AVenhance.Infra.Torus.unitCell (n + 1), g (quotient (n + 1) (P z)) := by
      simpa only [P, PiLp.coe_symm_continuousLinearEquiv,
        AVenhance.Infra.Torus.unitCell, AVenhance.Infra.Torus.unitCellAt, zero_add] using
        (exact14_haar_pullback g)
    have hcoord (g : Torus (n + 1) → ℝ)
        (hg : ContDiff ℝ 1 (fun a : Euclid (n + 1) => g (quotient (n + 1) a)))
        (i : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
        PC i (fun y => (g (quotient (n + 1) (P y)) : ℂ)) z =
          (gradient g (quotient (n + 1) (P z)) i : ℂ) := by
      have H := Complex.ofRealCLM.hasFDerivAt.comp z
        (((hg.differentiable (by simp)) (P z)).hasFDerivAt.comp z P.hasFDerivAt)
      simp only [Function.comp_def, Complex.ofRealCLM_apply] at H
      unfold AVenhance.Infra.Torus.coordDeriv
      rw [H.fderiv, gradient_at_quotient hg]
      simp [liftedGradient, P, basisVector, Homogenization.basisVec]
    have hscalar (g : Torus (n + 1) → ℝ)
        (hg : ContDiff ℝ 1 (fun a : Euclid (n + 1) => g (quotient (n + 1) a)))
        (i : Fin (n + 1)) :
        (∫ x, f x * gradient g x i ∂haar (n + 1)) =
          -(∫ x, gradient f x i * g x ∂haar (n + 1)) := by
      have hF : ContDiff ℝ 1 (fun z => (f (quotient (n + 1) (P z)) : ℂ)) :=
        (Complex.ofRealCLM.contDiff.comp (hf.comp P.contDiff)).of_le (by simp)
      have hG : ContDiff ℝ 1 (fun z => (g (quotient (n + 1) (P z)) : ℂ)) :=
        (Complex.ofRealCLM.contDiff.comp (hg.comp P.contDiff)).of_le (by simp)
      have hpf : AVenhance.Infra.Torus.IsZdPeriodic
          (fun z => (f (quotient (n + 1) (P z)) : ℂ)) :=
        AVenhance.Infra.Torus.isZdPeriodic_fromUnitTorus (fun x => (f x : ℂ))
      have hpg : AVenhance.Infra.Torus.IsZdPeriodic
          (fun z => (g (quotient (n + 1) (P z)) : ℂ)) :=
        AVenhance.Infra.Torus.isZdPeriodic_fromUnitTorus (fun x => (g x : ℂ))
      have H := AVenhance.Infra.Torus.integral_unitCell_coord_ibp i hF hG hpf hpg
      simp_rw [hcoord g hg i, hcoord f hf i] at H
      apply Complex.ofReal_injective
      rw [hcell (fun x => f x * gradient g x i),
        hcell (fun x => gradient f x i * g x)]
      simpa only [← Complex.ofReal_mul, integral_complex_ofReal,
        Complex.ofReal_neg] using H
    have hVi (i : Fin (n + 1)) :
        ContDiff ℝ 1 (fun a : Euclid (n + 1) => V (quotient (n + 1) a) i) :=
      contDiff_pi.mp
        ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).contDiff.comp hV) i
    have hfc : Continuous f := continuous_of_lift hf.continuous
    have hvc : Continuous V := continuous_of_lift hV.continuous
    have hLc (i : Fin (n + 1)) :
        Continuous (fun x => f x * gradient (fun y => V y i) x i) :=
      hfc.mul ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp (continuous_gradient_C1 (hVi i)))
    have hRc (i : Fin (n + 1)) :
        Continuous (fun x => gradient f x i * V x i) :=
      ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp (continuous_gradient_C1 hf)).mul
        ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).comp hvc)
    letI : IsProbabilityMeasure (haar (n + 1)) := by unfold haar; infer_instance
    have hLint (i : Fin (n + 1)) :
        Integrable (fun x => f x * gradient (fun y => V y i) x i) (haar (n + 1)) :=
      compact_integrable (hLc i)
    have hRint (i : Fin (n + 1)) :
        Integrable (fun x => gradient f x i * V x i) (haar (n + 1)) :=
      compact_integrable (hRc i)
    have heach (i : Fin (n + 1)) :
        (∫ x, f x * gradient (fun y => V y i) x i ∂haar (n + 1)) =
          -(∫ x, gradient f x i * V x i ∂haar (n + 1)) :=
      hscalar (fun y => V y i) (hVi i) i
    calc
      (∫ x, f x * divergence V x ∂haar (n + 1)) =
          ∫ x, ∑ i : Fin (n + 1), f x * gradient (fun y => V y i) x i
            ∂haar (n + 1) := by
        congr 1
        funext x
        simp [divergence, gradient, liftedGradient, Finset.mul_sum]
      _ = ∑ i : Fin (n + 1), ∫ x, f x * gradient (fun y => V y i) x i
          ∂haar (n + 1) := integral_finsetSum _ (fun i _ => hLint i)
      _ = -(∑ i : Fin (n + 1), ∫ x, gradient f x i * V x i ∂haar (n + 1)) := by
        simp_rw [heach]
        rw [Finset.sum_neg_distrib]
      _ = -(∫ x, inner ℝ (gradient f x) (V x) ∂haar (n + 1)) := by
        congr 1
        rw [← integral_finsetSum _ (fun i _ => hRint i)]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by simp [PiLp.inner_apply, mul_comm])

end SmoothDensityTransport

end



noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace SmoothDensityTransport

def fpRHS {d : ℕ} (U : Torus d → ℝ) (τ : ℝ)
    (ρ : ℝ → Torus d → ℝ) (t : ℝ) (x : Torus d) : ℝ :=
  divergence (fun y => ρ t y • gradient U y) x + τ * laplacian (ρ t) x

theorem chemicalPotential_smooth {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => chemicalPotential U τ ρ t (quotient d a)) := by
  exact h.potential_smooth.add
    (contDiff_const.mul
      ((h.spatial_smooth t ht).log (fun a => (h.positive t ht (quotient d a)).ne')))

private theorem density_mul_chemicalGradient {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Torus d) :
    ρ t x • gradient (chemicalPotential U τ ρ t) x =
      ρ t x • gradient U x + τ • gradient (ρ t) x := by
  let a := representative d x
  have hq : quotient d a = x := quotient_representative d x
  have hU := (h.potential_smooth.differentiable (by simp)) a
  have hr := ((h.spatial_smooth t ht).differentiable (by simp)) a
  have hp : ρ t (quotient d a) ≠ 0 := (h.positive t ht _).ne'
  have hl := hr.log hp
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).injective
  funext i
  change ρ t x *
      fderiv ℝ (fun b : Euclid d => U (quotient d b) + τ * Real.log (ρ t (quotient d b))) a
        (basisVector d i) =
    ρ t x * fderiv ℝ (fun b : Euclid d => U (quotient d b)) a (basisVector d i) +
      τ * fderiv ℝ (fun b : Euclid d => ρ t (quotient d b)) a (basisVector d i)
  rw [fderiv_fun_add hU (hl.const_mul τ), fderiv_const_mul hl τ, fderiv.log hr hp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hq]
  field_simp [(h.positive t ht x).ne']
  <;> ring

theorem flux_divergence {d : ℕ} {T τ : ℝ} {U : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (h : SmoothFP d T τ U ρ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Torus d) :
    divergence (fun y => ρ t y • gradient (chemicalPotential U τ ρ t) y) x =
      fpRHS U τ ρ t x := by
  let A : Torus d → Euclid d := fun y => ρ t y • gradient U y
  let B : Torus d → Euclid d := gradient (ρ t)
  have hA : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => A (quotient d a)) :=
    (h.spatial_smooth t ht).smul (smooth_gradient_lift h.potential_smooth)
  have hB : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Euclid d => B (quotient d a)) :=
    smooth_gradient_lift (h.spatial_smooth t ht)
  have hFlux : (fun y => ρ t y • gradient (chemicalPotential U τ ρ t) y) =
      fun y => A y + τ • B y := funext (density_mul_chemicalGradient h ht)
  rw [hFlux]
  change (∑ i : Fin d,
      fderiv ℝ (fun a : Euclid d => (A (quotient d a) + τ • B (quotient d a)) i)
        (representative d x) (basisVector d i)) =
    (∑ i : Fin d, fderiv ℝ (fun a : Euclid d => A (quotient d a) i)
      (representative d x) (basisVector d i)) +
    τ * (∑ i : Fin d, fderiv ℝ (fun a : Euclid d => B (quotient d a) i)
      (representative d x) (basisVector d i))
  have ha (i : Fin d) :=
    ((contDiff_pi.mp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff.comp hA) i).differentiable
      (by simp)) (representative d x)
  have hb (i : Fin d) :=
    ((contDiff_pi.mp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).contDiff.comp hB) i).differentiable
      (by simp)) (representative d x)
  have hterm (i : Fin d) :
      fderiv ℝ (fun a : Euclid d => (A (quotient d a) + τ • B (quotient d a)) i)
        (representative d x) (basisVector d i) =
      fderiv ℝ (fun a : Euclid d => A (quotient d a) i) (representative d x) (basisVector d i) +
        τ * fderiv ℝ (fun a : Euclid d => B (quotient d a) i)
          (representative d x) (basisVector d i) := by
    change fderiv ℝ (fun a => A (quotient d a) i + τ * B (quotient d a) i)
      (representative d x) (basisVector d i) = _
    have hai : DifferentiableAt ℝ (fun a : Euclid d => A (quotient d a) i)
        (representative d x) := ha i
    have hbi : DifferentiableAt ℝ (fun a : Euclid d => B (quotient d a) i)
        (representative d x) := hb i
    rw [fderiv_fun_add hai (hbi.const_mul τ), fderiv_const_mul hbi τ]
    simp
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

end SmoothDensityTransport

end



noncomputable section
open Set MeasureTheory
namespace SmoothDensityTransport

def closedCell (d : ℕ) : Set (Fin d → ℝ) := Icc 0 1
def cellMeasure (d : ℕ) : Measure (closedCell d) :=
  (volume : Measure (Fin d → ℝ)).comap Subtype.val

instance compact_closedCell (d : ℕ) : CompactSpace (closedCell d) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

instance finite_cellMeasure (d : ℕ) : IsFiniteMeasure (cellMeasure d) := by
  constructor
  have H : cellMeasure d (univ : Set (closedCell d)) ≤
      (volume : Measure (Fin d → ℝ))
        ((Subtype.val : closedCell d → (Fin d → ℝ)) '' univ) :=
    Measure.comap_apply_le (Subtype.val : closedCell d → (Fin d → ℝ))
      (volume : Measure (Fin d → ℝ))
      (s := (univ : Set (closedCell d))) nullMeasurableSet_univ
  have hb : (volume : Measure (Fin d → ℝ)) (closedCell d) < ⊤ := isCompact_Icc.measure_lt_top
  have hle : cellMeasure d univ ≤ (volume : Measure (Fin d → ℝ)) (closedCell d) := by
    simpa only [cellMeasure, image_univ, Subtype.range_coe] using H
  exact hle.trans_lt hb

/-- Exact normalized Haar to compact closed-cell transfer. Face sets have zero
product Lebesgue measure; in dimension zero both cells are the singleton. -/
theorem haar_integral_closedCell {d : ℕ} (g : Torus d → ℝ) :
    (∫ x, g x ∂haar d) =
      ∫ z : closedCell d, g (quotient d (WithLp.toLp 2 z.1)) ∂cellMeasure d := by
  have H : (∫ x, g x ∂haar d) =
    ∫ z in {z : Fin d → ℝ | ∀ i, z i ∈ Ioc (0 : ℝ) 1},
      g (quotient d (WithLp.toLp 2 z)) := by
    exact exact14_haar_pullback g
  rw [H]
  unfold cellMeasure
  rw [integral_subtype_comap (μ := (volume : Measure (Fin d → ℝ)))
    (show MeasurableSet (closedCell d) from measurableSet_Icc)
    (fun z : Fin d → ℝ => g (quotient d (WithLp.toLp 2 z)))]
  apply setIntegral_congr_set
  have hset : {z : Fin d → ℝ | ∀ i, z i ∈ Ioc (0 : ℝ) 1} =
      Set.pi univ (fun _ : Fin d => Ioc (0 : ℝ) 1) := by
    ext z
    simp only [mem_setOf_eq, mem_pi, mem_univ, forall_true_left]
  rw [hset, volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc

end SmoothDensityTransport

end



noncomputable section
open Set MeasureTheory
namespace SmoothDensityTransport

end SmoothDensityTransport

end



open Set MeasureTheory
open SmoothDensityTransport

/-
Complete supplier legal archive (each artifact retains its exact original bytes):
licenses/CoarseGraining-LICENSE -> Blueprint/D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus.scribe.cs
licenses/TauCeti-LICENSE -> Blueprint/D5/S3/Geometry/ProbabilityTransport/PeriodicDensityModel.scribe.cs
licenses/lean-pool-LICENSE -> Blueprint/D5/S3/Geometry/ProbabilityTransport/SmoothDensityWeakTransport.scribe.cs
licenses/lean-pool-NOTICE -> Blueprint/D5/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics.scribe.cs
licenses/lean-pool-NOTICE.extra.yml -> Blueprint/D5/S3/Geometry/ProbabilityTransport/SmoothDensityEulerConsistency.scribe.cs
The five supplied legal artifacts total 80,454 bytes and accompany this delivery.
-/

