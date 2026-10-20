/- GID: D5/S3/Geometry/Riemannian/ACTangentSpeed
   generality: G
   mirror-B: D5/B/S3/Geometry/Riemannian/ACTangentSpeed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.AbsolutelyContinuous, mathlib/module/Mathlib.Analysis.BoundedVariation]
   utility: none
   digest: Chart absolute continuity, almost-everywhere tangent derivative and intrinsic metric speed. -/

import D5.S3.Geometry.Riemannian.ChartComparison
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual chart AC, tangent derivative, and intrinsic metric speed. -/

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle Topology ContDiff ENNReal NNReal

noncomputable section
namespace Original172

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [ConnectedSpace M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]

local notation "𝕀" => 𝓘(ℝ, E)
local notation "IR" => 𝓘(ℝ, ℝ)
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/- Every metric telescope below explicitly uses this fixed canonical metric.
   It is not registered as an instance: E is supplied at each use. Each AC
   premise and result share a single local g. No metric parameter is assumed. -/
@[instance_reducible] private def sourceMetric : MetricSpace M :=
  canonicalMetric (E := E) (M := M)

/- The continuity bridge reuses Mathlib's metric Lipschitz composition and
   real-valued AC continuity; the original metric is used throughout. -/
private theorem metric_AC_continuousOn {X : Type*} [PseudoMetricSpace X]
    {f : ℝ → X} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ContinuousOn f (uIcc a b) := by
  intro t ht
  have hd : AbsolutelyContinuousOnInterval (fun s => dist (f s) (f t)) a b :=
    (LipschitzWith.dist_left (f t)).comp_absolutelyContinuousOnInterval hf
  have hc := hd.continuousOn t ht
  change Tendsto f (𝓝[uIcc a b] t) (𝓝 (f t))
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [ContinuousWithinAt, dist_self] using hc

/- The lower half of the proved C1 estimate gives a genuine chart Lipschitz bound.
   No metric/chart comparison is supplied as a premise. -/
set_option backward.isDefEq.respectTransparency false in
private theorem chart_lipschitz (p : M) :
    let g : MetricSpace M := sourceMetric (E := E) (M := M)
    letI : MetricSpace M := g
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ (extChartAt 𝕀 p).source ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (extChartAt 𝕀 p) U := by
  let g : MetricSpace M := sourceMetric (E := E) (M := M)
  letI : MetricSpace M := g
  obtain ⟨U, hUo, hpU, hUs, hpair⟩ :=
    canonical_pairwise_local_comparison (E := E) p (1/2) (by norm_num) (by norm_num)
  let A := mfderiv 𝕀 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p p)
  let B := mfderiv 𝕀 𝕀 (extChartAt 𝕀 p)
    ((extChartAt 𝕀 p).symm (extChartAt 𝕀 p p))
  have hBA : B ∘L A =
      ContinuousLinearMap.id ℝ (TangentSpace 𝕀 (extChartAt 𝕀 p p)) := by
    simpa only [A, B, show range (𝕀 : E → E) = univ by ext; simp,
      mfderivWithin_univ] using
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝕀)
        ((extChartAt 𝕀 p).map_source (mem_extChartAt_source p)))
  refine ⟨U, hUo, hpU, hUs, ⟨2 * ‖B‖, by positivity⟩, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hN := (hpair x hx y hy).1
  have hnorm := B.le_opNorm (A (extChartAt 𝕀 p y - extChartAt 𝕀 p x))
  have hid : B (A (extChartAt 𝕀 p y - extChartAt 𝕀 p x)) =
      extChartAt 𝕀 p y - extChartAt 𝕀 p x := by
    have heval := congrArg
      (fun L => L (extChartAt 𝕀 p y - extChartAt 𝕀 p x)) hBA
    change B (A (extChartAt 𝕀 p y - extChartAt 𝕀 p x)) =
      extChartAt 𝕀 p y - extChartAt 𝕀 p x at heval
    exact heval
  rw [hid] at hnorm
  rw [dist_eq_norm, norm_sub_rev]
  change ‖extChartAt 𝕀 p y - extChartAt 𝕀 p x‖ ≤ (2 * ‖B‖) * dist x y
  dsimp [A] at hnorm hN ⊢
  have hm := mul_le_mul_of_nonneg_left hN (norm_nonneg B)
  nlinarith [norm_nonneg B]

/- An eventually constant monotone sequence is a finite partition, with its final
   point repeated. Every interval is subordinate to an actual chart. -/
private theorem chart_AC_partition {T : ℝ} (hT : 0 < T) {z : ℝ → M}
    :
    let g : MetricSpace M := sourceMetric (E := E) (M := M)
    letI : MetricSpace M := g
    AbsolutelyContinuousOnInterval z 0 T →
    ∃ τ : ℕ → Icc (0 : ℝ) T, (τ 0 : ℝ) = 0 ∧ Monotone τ ∧
      (∃ m, ∀ n ≥ m, (τ n : ℝ) = T) ∧
      ∃ p : ℕ → M, ∃ U : ℕ → Set M, ∃ K : ℕ → ℝ≥0,
        ∀ n, IsOpen (U n) ∧ U n ⊆ (extChartAt 𝕀 (p n)).source ∧
          LipschitzOnWith (K n) (extChartAt 𝕀 (p n)) (U n) ∧
          MapsTo z (Icc (τ n : ℝ) (τ (n+1))) (U n) ∧
          AbsolutelyContinuousOnInterval (extChartAt 𝕀 (p n) ∘ z) (τ n) (τ (n+1)) := by
  intro g hz
  let _ : MetricSpace M := g
  choose U hUo hpU hUs K hK using (chart_lipschitz (E := E) (M := M))
  let c : M → Set (Icc (0 : ℝ) T) := fun p =>
    (fun t : Icc (0 : ℝ) T => z t) ⁻¹' U p
  have hzu : ContinuousOn z (uIcc (0 : ℝ) T) := metric_AC_continuousOn hz
  have hzc : ContinuousOn z (Icc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT.le] using hzu
  have hc : Continuous (fun t : Icc (0 : ℝ) T => z t) := hzc.domRestrict
  obtain ⟨τ, h0, hmono, hend, hsub⟩ := exists_monotone_Icc_subset_open_cover_Icc
    hT.le (c := c) (fun p => (hUo p).preimage hc) (by
      intro t _
      exact mem_iUnion.mpr ⟨z t, hpU (z t)⟩)
  choose p hp using hsub
  refine ⟨τ, h0, hmono, hend, p, (fun n => U (p n)), (fun n => K (p n)), ?_⟩
  intro n
  have hm : MapsTo z (Icc (τ n : ℝ) (τ (n+1))) (U (p n)) := by
    intro t ht
    exact hp n (show (⟨t, le_trans (τ n).2.1 ht.1,
      le_trans ht.2 (τ (n+1)).2.2⟩ : Icc (0 : ℝ) T) ∈
        Icc (τ n) (τ (n+1)) from ht)
  refine ⟨hUo _, hUs _, hK _, hm, ?_⟩
  apply (hK _).comp_absolutelyContinuousOnInterval
  · simpa only [uIcc_of_le (show (τ n : ℝ) ≤ τ (n+1) from hmono (Nat.le_succ n))] using hm
  · apply hz.mono
    rw [uIcc_of_le hT.le, uIcc_of_le (show (τ n : ℝ) ≤ τ (n+1) from hmono (Nat.le_succ n))]
    exact Icc_subset_Icc (τ n).2.1 (τ (n+1)).2.2

private theorem interior_partition_interval {T t : ℝ}
    (τ : ℕ → Icc (0 : ℝ) T) (h0 : (τ 0 : ℝ) = 0)
    (hend : ∃ m, ∀ n ≥ m, (τ n : ℝ) = T)
    (ht : t ∈ Ioo (0 : ℝ) T) (hne : ∀ n, t ≠ (τ n : ℝ)) :
    ∃ n, t ∈ Ioo (τ n : ℝ) (τ (n+1)) := by
  have hex : ∃ k, t < (τ k : ℝ) := by
    obtain ⟨m, hm⟩ := hend
    exact ⟨m, by simpa [hm m le_rfl] using ht.2⟩
  let k := Nat.find hex
  have hk : t < (τ k : ℝ) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, h0] at hk
    exact (not_lt_of_ge ht.1.le) hk
  obtain ⟨n, hkn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hnlt : n < Nat.find hex := by change n < k; omega
  have hn : ¬ t < (τ n : ℝ) := Nat.find_min hex hnlt
  refine ⟨n, lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm (hne n)), ?_⟩
  simpa only [hkn] using hk

set_option backward.isDefEq.respectTransparency false in
private theorem ae_actual_mdifferentiable {T : ℝ} (hT : 0 < T) {z : ℝ → M}
    :
    let g : MetricSpace M := sourceMetric (E := E) (M := M)
    letI : MetricSpace M := g
    AbsolutelyContinuousOnInterval z 0 T →
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), MDifferentiableAt IR 𝕀 z t := by
  intro g hz
  let _ : MetricSpace M := g
  obtain ⟨τ, h0, hmono, hend, p, U, K, hpart⟩ := chart_AC_partition hT hz
  have hdiff : ∀ᵐ t ∂volume, ∀ n,
      t ∈ uIcc (τ n : ℝ) (τ (n+1)) →
        DifferentiableAt ℝ (extChartAt 𝕀 (p n) ∘ z) t := by
    rw [ae_all_iff]
    intro n
    exact (hpart n).2.2.2.2.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  have hne : ∀ᵐ t ∂volume, ∀ n, t ≠ (τ n : ℝ) := by
    rw [ae_all_iff]
    intro n
    simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Icc, hdiff.filter_mono
    (ae_mono Measure.restrict_le_self), hne.filter_mono (ae_mono Measure.restrict_le_self)]
      with t ht hd hn
  have hti : t ∈ Ioo (0 : ℝ) T := by
    obtain ⟨m, hm⟩ := hend
    constructor
    · exact lt_of_le_of_ne ht.1 (by simpa [h0] using (hn 0).symm)
    · exact lt_of_le_of_ne ht.2 (by simpa [hm m le_rfl] using hn m)
  obtain ⟨n, htn⟩ := interior_partition_interval τ h0 hend hti hn
  have hs := (hpart n).2.1 ((hpart n).2.2.2.1 ⟨htn.1.le, htn.2.le⟩)
  have hzu : ContinuousOn z (uIcc (0 : ℝ) T) := metric_AC_continuousOn hz
  have hzc : ContinuousOn z (Icc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT.le] using hzu
  have hc : ContinuousAt z t :=
    (hzc t ht).continuousAt (Icc_mem_nhds hti.1 hti.2)
  have hsource : z t ∈ (chartAt E (p n)).source := by
    simpa only [extChartAt_source] using hs
  have htnu : t ∈ uIcc (τ n : ℝ) (τ (n+1)) := by
    rw [uIcc_of_le (show (τ n : ℝ) ≤ τ (n+1) from hmono (Nat.le_succ n))]
    exact ⟨htn.1.le, htn.2.le⟩
  have hcoord : MDifferentiableAt IR 𝕀 (extChartAt 𝕀 (p n) ∘ z) t :=
    mdifferentiableAt_iff_differentiableAt.mpr (hd n htnu)
  exact (mdifferentiableAt_iff_target_of_mem_source (I := IR) (I' := 𝕀)
    (f := z) (y := p n) hsource).2 ⟨hc, hcoord⟩

set_option backward.isDefEq.respectTransparency false in
private theorem actual_tangent_formula {z : ℝ → M} {t : ℝ}
    (hz : MDifferentiableAt IR 𝕀 z t) (p : M)
    (hp : z t ∈ (extChartAt 𝕀 p).source) :
    DifferentiableAt ℝ (extChartAt 𝕀 p ∘ z) t ∧
      mfderiv IR 𝕀 z t 1 =
        mfderiv 𝕀 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p (z t))
          (deriv (extChartAt 𝕀 p ∘ z) t) := by
  have hsource : z t ∈ (chartAt E p).source := by
    simpa only [extChartAt_source] using hp
  have hphi : MDifferentiableAt 𝕀 𝕀 (extChartAt 𝕀 p) (z t) :=
    mdifferentiableAt_extChartAt (I := 𝕀) (x := p) (y := z t) hsource
  have hdiff := mdifferentiableAt_iff_differentiableAt.mp (MDifferentiableAt.comp t hphi hz)
  refine ⟨hdiff, ?_⟩
  have hc := congrArg (fun L => L 1) (mfderiv_comp t hphi hz)
  have he (u w : E) : (NormedSpace.fromTangentSpace (𝕜 := ℝ) u).symm w = w := by rfl
  have hr (u w : ℝ) : NormedSpace.fromTangentSpace (𝕜 := ℝ) u w = w := by rfl
  have hcoord : deriv (extChartAt 𝕀 p ∘ z) t =
      mfderiv 𝕀 𝕀 (extChartAt 𝕀 p) (z t) (mfderiv IR 𝕀 z t 1) := by
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, he, hr] at hc
    change (fderiv ℝ (extChartAt 𝕀 p ∘ z) t) 1 =
      (show E from mfderiv 𝕀 𝕀 (extChartAt 𝕀 p) (z t)
        (mfderiv IR 𝕀 z t 1)) at hc
    simpa only [fderiv_apply_one_eq_deriv] using hc
  rw [hcoord]
  have hinv := congrArg (fun L => L (mfderiv IR 𝕀 z t 1))
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝕀) hp)
  simp only [show range (𝕀 : E → E) = univ by ext; simp,
    mfderivWithin_univ, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.id_apply] at hinv
  change @Eq (TangentSpace 𝕀 (z t))
    (show TangentSpace 𝕀 (z t) from
      mfderiv 𝕀 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p (z t))
        (mfderiv 𝕀 𝕀 (extChartAt 𝕀 p) (z t) (mfderiv IR 𝕀 z t 1)))
    (mfderiv IR 𝕀 z t 1) at hinv
  exact hinv.symm

/- The sharp comparison is used for every epsilon at the moving point z(t).
   This constructs the actual metric quotient limit, including zero velocity. -/
set_option backward.isDefEq.respectTransparency false in
private theorem actual_metric_speed_at {z : ℝ → M} {t : ℝ}
    (hz : MDifferentiableAt IR 𝕀 z t) :
    let g : MetricSpace M := sourceMetric (E := E) (M := M)
    letI : MetricSpace M := g
    Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 ‖mfderiv IR 𝕀 z t 1‖) := by
  let g : MetricSpace M := sourceMetric (E := E) (M := M)
  letI : MetricSpace M := g
  let p := z t
  let phi := extChartAt 𝕀 p
  let A := mfderiv 𝕀 𝕀 phi.symm (phi p)
  let r : ℝ := ‖mfderiv IR 𝕀 z t 1‖
  obtain ⟨hd, hv⟩ := actual_tangent_formula hz p (mem_extChartAt_source p)
  have hi : phi.symm (phi p) = p := phi.left_inv (mem_extChartAt_source p)
  have hnorm : ‖A (deriv (phi ∘ z) t)‖ = r := by
    have hn (v : E) :
        ‖(show TangentSpace 𝕀 (phi.symm (phi p)) from v)‖ =
          ‖(show TangentSpace 𝕀 p from v)‖ :=
      congrArg (fun q : M => ‖(show TangentSpace 𝕀 q from v)‖) hi
    change ‖(show TangentSpace 𝕀 (phi.symm (phi p)) from
      A (deriv (phi ∘ z) t))‖ = r
    rw [hn]
    exact congrArg (fun v : TangentSpace 𝕀 p => ‖v‖) hv.symm
  have hq : Tendsto (fun h : ℝ => ‖A (phi (z (t+h)) - phi p)‖ / |h|)
      (𝓝[≠] (0 : ℝ)) (𝓝 r) := by
    have hh := (A.continuous.tendsto (deriv (phi ∘ z) t)).comp
      (hasDerivAt_iff_tendsto_slope_zero.mp hd.hasDerivAt)
    have hn := hh.norm
    simpa only [Function.comp_apply, p, map_smul, norm_smul, Real.norm_eq_abs,
      abs_inv, div_eq_inv_mul, hnorm] using hn
  apply Metric.tendsto_nhds.2
  intro delta hdelta
  let eps := min (1/2 : ℝ) (delta / (4 * (r+1)))
  have hr : 0 ≤ r := norm_nonneg _
  have heps : 0 < eps := lt_min (by norm_num) (by positivity)
  have heps1 : eps < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have herror : eps * (r+1) ≤ delta/4 := by
    have h := min_le_right (1/2 : ℝ) (delta / (4 * (r+1)))
    dsimp [eps]
    apply (le_div_iff₀ (by positivity : 0 < r+1)).mp
    convert h using 1 <;> field_simp [ne_of_gt (show 0 < r+1 by linarith)] <;> ring
  obtain ⟨U, hUo, hpU, hUs, hpair⟩ :=
    canonical_pairwise_local_comparison (E := E) p eps heps heps1
  have hU : ∀ᶠ h in 𝓝[≠] (0 : ℝ), z (t+h) ∈ U := by
    have hconst : Tendsto (fun _ : ℝ => t) (𝓝[≠] (0 : ℝ)) (𝓝 t) :=
      tendsto_const_nhds
    have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have htadd : Tendsto (fun h : ℝ => t+h) (𝓝[≠] (0 : ℝ)) (𝓝 t) := by
      simpa only [add_zero] using hconst.add hid
    exact (hz.continuousAt.tendsto.comp htadd).eventually (hUo.mem_nhds hpU)
  have hclose : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      dist (‖A (phi (z (t+h)) - phi p)‖ / |h|) r < min (delta/4) 1 :=
    hq.eventually (ball_mem_nhds r (lt_min (by positivity) zero_lt_one))
  filter_upwards [hU, hclose, self_mem_nhdsWithin] with h hh hc hnz
  have hpos : 0 < |h| := abs_pos.mpr hnz
  let Q := ‖A (phi (z (t+h)) - phi p)‖ / |h|
  let D := dist (z (t+h)) (z t) / |h|
  obtain ⟨hl, hu⟩ := hpair p hpU (z (t+h)) hh
  have hl' := div_le_div_of_nonneg_right hl hpos.le
  have hu' := div_le_div_of_nonneg_right hu hpos.le
  change (1-eps) * ‖A (phi (z (t+h)) - phi p)‖ / |h| ≤ dist p (z (t+h)) / |h| at hl'
  change dist p (z (t+h)) / |h| ≤ (1+eps) * ‖A (phi (z (t+h)) - phi p)‖ / |h| at hu'
  rw [mul_div_assoc, dist_comm] at hl' hu'
  have hL : (1-eps)*Q ≤ D := hl'
  have hR : D ≤ (1+eps)*Q := hu'
  have hQ : 0 ≤ Q := by positivity
  have hQr : |Q-r| < min (delta/4) 1 := by simpa only [Real.dist_eq] using hc
  have hQr1 : |Q-r| < 1 := hQr.trans_le (min_le_right _ _)
  have hQrD : |Q-r| < delta/4 := hQr.trans_le (min_le_left _ _)
  have hQbound : Q ≤ r+1 := by linarith [le_abs_self (Q-r)]
  have hmul : eps*Q ≤ delta/4 :=
    (mul_le_mul_of_nonneg_left hQbound heps.le).trans herror
  have hDQ : |D-Q| ≤ eps*Q := abs_le.mpr ⟨by nlinarith [hL], by nlinarith [hR]⟩
  change dist D r < delta
  rw [Real.dist_eq]
  have htri : |D-r| ≤ |D-Q|+|Q-r| := by
    convert abs_add_le (D-Q) (Q-r) using 1 <;> ring_nf
  linarith

private theorem actual_speed_aemeasurable {T : ℝ} (hT : 0 < T) {z : ℝ → M}
    :
    let g : MetricSpace M := sourceMetric (E := E) (M := M)
    letI : MetricSpace M := g
    AbsolutelyContinuousOnInterval z 0 T →
    AEMeasurable (fun t => ‖mfderiv IR 𝕀 z t 1‖ₑ)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  intro g hz
  let _ : MetricSpace M := g
  have hzu : ContinuousOn z (uIcc (0 : ℝ) T) := metric_AC_continuousOn hz
  have hzc : ContinuousOn z (Icc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT.le] using hzu
  have hrestricted : Continuous (fun u : Icc (0 : ℝ) T => z u) := hzc.domRestrict
  have hprojection : Continuous (projIcc (0 : ℝ) T hT.le) := continuous_projIcc
  let c : ℝ → M := (fun u : Icc (0 : ℝ) T => z u) ∘ projIcc 0 T hT.le
  have hc : Continuous c := hrestricted.comp hprojection

  let f : ℕ → ℝ → ℝ := fun n t =>
    ((n : ℝ)+1) * dist (c (t + (((n : ℝ)+1)⁻¹))) (c t)
  have hf : ∀ n, AEMeasurable (f n) (volume.restrict (Icc (0 : ℝ) T)) := by
    intro n
    have hshift : Continuous (fun t : ℝ => t + (((n : ℝ)+1)⁻¹)) :=
      continuous_id.add continuous_const
    have hdist : Continuous (fun t : ℝ => dist (c (t + (((n : ℝ)+1)⁻¹))) (c t)) :=
      (hc.comp hshift).dist hc
    have hfn : Continuous (f n) :=
      (continuous_const : Continuous (fun _ : ℝ => (n : ℝ)+1)).mul hdist
    exact hfn.measurable.aemeasurable
  have hlim : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun n => f n t) atTop (𝓝 ‖mfderiv IR 𝕀 z t 1‖) := by
    have hinner : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), t ∈ Ioo (0 : ℝ) T := by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        (show ∀ᵐ t : ℝ ∂volume, t ≠ 0 from by simp [ae_iff]).filter_mono (ae_mono Measure.restrict_le_self),
        (show ∀ᵐ t : ℝ ∂volume, t ≠ T from by simp [ae_iff]).filter_mono (ae_mono Measure.restrict_le_self)] with t ht h0 h1
      exact ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩
    filter_upwards [ae_actual_mdifferentiable hT hz, hinner] with t hd ht
    have heq : c =ᶠ[𝓝 t] z := by
      filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
      simp only [c, Function.comp_apply, projIcc_of_mem hT.le hu]
    have hzero : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      by simpa only [one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hpunct : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨hzero, .of_forall (fun n => by simp; positivity)⟩
    have hlimz := (actual_metric_speed_at hd).comp hpunct
    apply hlimz.congr'
    have hshift : Tendsto (fun n : ℕ => t+((n : ℝ)+1)⁻¹) atTop (𝓝 t) := by
      have hconst : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
      simpa only [add_zero] using hconst.add hzero
    have hnear := heq.comp_tendsto hshift
    filter_upwards [hnear] with n hn
    dsimp only [Function.comp_apply] at hn
    dsimp [f]
    rw [hn, heq.eq_of_nhds]
    rw [abs_of_pos (by positivity : 0 < ((n : ℝ)+1)⁻¹), div_inv_eq_mul, mul_comm]
  have hr : AEMeasurable (fun t => ‖mfderiv IR 𝕀 z t 1‖)
      (volume.restrict (Icc (0 : ℝ) T)) := by
    exact (aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hf n).aestronglyMeasurable) hlim).aemeasurable
  simpa only [ofReal_norm] using hr.ennreal_ofReal

/- Full named C2/C3 target. The metric instance is the proved C0 construction.
   Repeated final partition points encode a finite partition without a new
   positive-dimensional or finite-energy hypothesis. -/
theorem actual_chart_AC_tangent_and_metric_speed {T : ℝ} (hT : 0 < T)
    (z : ℝ → M) (hz : letI : MetricSpace M := canonicalMetric (E := E) (M := M)
    AbsolutelyContinuousOnInterval z 0 T) :
    letI : MetricSpace M := canonicalMetric (E := E) (M := M)
    (∃ τ : ℕ → Icc (0 : ℝ) T, (τ 0 : ℝ) = 0 ∧ Monotone τ ∧
      (∃ m, ∀ n ≥ m, (τ n : ℝ) = T) ∧
      ∃ p : ℕ → M, ∃ U : ℕ → Set M, ∃ K : ℕ → ℝ≥0,
        ∀ n, IsOpen (U n) ∧ U n ⊆ (extChartAt 𝕀 (p n)).source ∧
          LipschitzOnWith (K n) (extChartAt 𝕀 (p n)) (U n) ∧
          MapsTo z (Icc (τ n : ℝ) (τ (n+1))) (U n) ∧
          AbsolutelyContinuousOnInterval (extChartAt 𝕀 (p n) ∘ z) (τ n) (τ (n+1))) ∧
    (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      MDifferentiableAt IR 𝕀 z t ∧
      (∀ p : M, z t ∈ (extChartAt 𝕀 p).source →
        DifferentiableAt ℝ (extChartAt 𝕀 p ∘ z) t ∧
          mfderiv IR 𝕀 z t 1 =
            mfderiv 𝕀 𝕀 (extChartAt 𝕀 p).symm (extChartAt 𝕀 p (z t))
              (deriv (extChartAt 𝕀 p ∘ z) t)) ∧
      Tendsto (fun h : ℝ => dist (z (t+h)) (z t) / |h|)
        (𝓝[≠] (0 : ℝ)) (𝓝 ‖mfderiv IR 𝕀 z t 1‖)) ∧
    AEMeasurable (fun t => ‖mfderiv IR 𝕀 z t 1‖ₑ)
      (volume.restrict (Icc (0 : ℝ) T)) := by
  let g : MetricSpace M := sourceMetric (E := E) (M := M)
  letI : MetricSpace M := g
  refine ⟨chart_AC_partition hT hz, ?_, actual_speed_aemeasurable hT hz⟩
  filter_upwards [ae_actual_mdifferentiable hT hz] with t ht
  exact ⟨ht, fun p hp => actual_tangent_formula ht p hp, actual_metric_speed_at ht⟩

end Original172
