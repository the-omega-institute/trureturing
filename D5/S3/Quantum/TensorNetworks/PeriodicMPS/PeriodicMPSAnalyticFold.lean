/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticFold
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticBranchSeparation]
   utility: none
   digest: A residual analytic readout that separates a pair arbitrarily near a strict fold gives an open dense singleton-fiber locus on a neighborhood. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSLocalObservationGraph
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSAnalyticBranchSeparation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.GDelta.Basic

/-! A strict analytic fold in straightened coordinates and separation by a residual readout. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSAnalyticFold

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Partial differentiation in the last coordinate. -/
noncomputable def verticalDeriv (h : E × ℝ → ℝ) (x : E × ℝ) : ℝ :=
  fderiv ℝ h x (0, 1)

private theorem analyticAt_verticalDeriv {h : E × ℝ → ℝ} {x : E × ℝ}
    (hh : AnalyticAt ℝ h x) : AnalyticAt ℝ (verticalDeriv h) x :=
  AnalyticAt.comp ((ContinuousLinearMap.apply ℝ ℝ ((0, 1) : E × ℝ)).analyticAt _) hh.fderiv

private theorem analyticAt_slice (u : E) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (u, s)) t :=
  analyticAt_const.prod analyticAt_id

private theorem deriv_slice {h : E × ℝ → ℝ} {u : E} {t : ℝ}
    (hh : AnalyticAt ℝ h (u, t)) : deriv (fun s => h (u, s)) t = verticalDeriv h (u, t) := by
  have ht : HasDerivAt (fun s : ℝ => (u, s)) (0, 1) t :=
    (hasDerivAt_const t u).prodMk (hasDerivAt_id t)
  exact (hh.differentiableAt.hasFDerivAt.comp_hasDerivAt t ht).deriv

private theorem split_linear (L : E × ℝ →L[ℝ] ℝ) (u : E) (t : ℝ) :
    L (u, t) = L (u, 0) + t * L (0, 1) := by
  have hp : (u, t) = (u, 0) + t • ((0, 1) : E × ℝ) := by simp
  calc
    L (u, t) = L ((u, 0) + t • ((0, 1) : E × ℝ)) := congrArg L hp
    _ = _ := by rw [map_add, map_smul, smul_eq_mul]

private noncomputable def triangularEquiv (L : E × ℝ →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) where
  toFun x := (x.1, L x)
  invFun x := (x.1, (x.2 - L (x.1, 0)) / L (0, 1))
  left_inv x := by
    refine Prod.ext rfl ?_
    change (L x - L (x.1, 0)) / L (0, 1) = x.2
    rw [div_eq_iff hL]
    exact sub_eq_of_eq_add (by simpa only [Prod.eta, add_comm] using split_linear L x.1 x.2)
  right_inv x := by
    refine Prod.ext rfl ?_
    change L (x.1, (x.2 - L (x.1, 0)) / L (0, 1)) = x.2
    rw [split_linear, div_mul_cancel₀ _ hL]
    ring
  map_add' x y := by simp
  map_smul' a x := by simp
  continuous_toFun := continuous_fst.prodMk L.continuous
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub (L.continuous.comp (continuous_fst.prodMk continuous_const))).div_const _)

private theorem hasFDerivAt_triangular {h : E × ℝ → ℝ} {x : E × ℝ}
    (hh : AnalyticAt ℝ h x) (hD : verticalDeriv h x ≠ 0) :
    HasFDerivAt (fun p => (p.1, h p))
      (triangularEquiv (fderiv ℝ h x) hD : (E × ℝ) →L[ℝ] (E × ℝ)) x := by
  have hL : (triangularEquiv (fderiv ℝ h x) hD : (E × ℝ) →L[ℝ] (E × ℝ)) =
      (ContinuousLinearMap.fst ℝ E ℝ).prod (fderiv ℝ h x) := by
    ext p <;> rfl
  rw [hL]
  exact (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.prodMk hh.differentiableAt.hasFDerivAt

section Inverse

variable [CompleteSpace E]

/-- A uniquely selected scalar root in an open region is analytic wherever its vertical
derivative is nonzero. The parameter and level may themselves be analytic functions. -/
private theorem analyticAt_selected_root {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {h : E × ℝ → ℝ} {Ω : Set (E × ℝ)} (hΩ : IsOpen Ω)
    {base : Y → E} {level root : Y → ℝ} {y : Y}
    (hb : AnalyticAt ℝ base y) (hl : AnalyticAt ℝ level y)
    (hm : (base y, root y) ∈ Ω) (he : h (base y, root y) = level y)
    (hh : AnalyticAt ℝ h (base y, root y))
    (hd : verticalDeriv h (base y, root y) ≠ 0)
    (hu : ∀ᶠ z in 𝓝 y, ∀ t : ℝ, (base z, t) ∈ Ω → h (base z, t) = level z → t = root z) :
    AnalyticAt ℝ root y := by
  let T : E × ℝ → E × ℝ := fun x => (x.1, h x)
  let N : E × ℝ → ℝ := fun x => x.2
  let x := (base y, root y)
  let F : Y → E × ℝ := fun z => (base z, level z)
  have hF : AnalyticAt ℝ F y := hb.prod hl
  have hFy : F y = T x := Prod.ext rfl he.symm
  have hT : AnalyticAt ℝ T x := AnalyticAt.prod ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt x) hh
  have hN : AnalyticAt ℝ N x := (ContinuousLinearMap.snd ℝ E ℝ).analyticAt x
  obtain ⟨e, V, g, heT, hx, ho, hTx, hV, hi, hg, hgraph⟩ :=
    PeriodicMPSLocalObservationGraph.exists_analytic_graph T N x hT hN
      (triangularEquiv (fderiv ℝ h x) hd) (hasFDerivAt_triangular hh hd)
  have h_inv : AnalyticAt ℝ (e.symm ∘ F) y := hi.comp_of_eq hF hFy
  have hxy : (e.symm ∘ F) y = x := by
    change e.symm (F y) = x
    rw [hFy, ← heT]
    exact e.left_inv hx
  have h_in : ∀ᶠ z in 𝓝 y, (e.symm ∘ F) z ∈ Ω :=
    h_inv.continuousAt (hΩ.mem_nhds (hxy.symm ▸ hm))
  have h_target : ∀ᶠ z in 𝓝 y, F z ∈ V :=
    hF.continuousAt (ho.mem_nhds (hFy.symm ▸ hTx))
  refine ((hg _ hTx).comp_of_eq hF hFy).congr ?_
  filter_upwards [h_in, h_target, hu] with z hz hzV hzUnique
  have hpair := hgraph (F z) hzV
  have hfirst : (e.symm (F z)).1 = base z := congrArg (fun p => p.1.1) hpair
  have hlevel : h (e.symm (F z)) = level z := congrArg (fun p => p.1.2) hpair
  have hroot : (e.symm (F z)).2 = root z := by
    apply hzUnique
    · simpa only [Function.comp_apply, ← hfirst, Prod.eta] using hz
    · simpa only [← hfirst, Prod.eta] using hlevel
  exact (congrArg Prod.snd hpair).symm.trans hroot

end Inverse

private theorem strictMono_verticalDeriv {h : E × ℝ → ℝ} {u : E} {a b : ℝ}
    (ha : ∀ t ∈ Icc a b, AnalyticAt ℝ h (u, t))
    (hp : ∀ t ∈ Icc a b, 0 < verticalDeriv (verticalDeriv h) (u, t)) :
    StrictMonoOn (fun t => verticalDeriv h (u, t)) (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · intro t ht
    exact ((analyticAt_verticalDeriv (ha t ht)).comp (analyticAt_slice u t)).continuousAt.continuousWithinAt
  · intro t ht
    have htc := interior_subset ht
    rw [deriv_slice (analyticAt_verticalDeriv (ha t htc))]
    exact hp t htc

private theorem strictAnti_left {h : E × ℝ → ℝ} {u : E} {a b c : ℝ}
    (hc : c ∈ Icc a b) (ha : ∀ t ∈ Icc a b, AnalyticAt ℝ h (u, t))
    (hm : StrictMonoOn (fun t => verticalDeriv h (u, t)) (Icc a b))
    (hz : verticalDeriv h (u, c) = 0) :
    StrictAntiOn (fun t => h (u, t)) (Icc a c) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a c)
  · intro t ht
    exact ((ha t ⟨ht.1, ht.2.trans hc.2⟩).comp
      (analyticAt_slice u t)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2.le.trans hc.2⟩
    rw [deriv_slice (ha t ht'), ← hz]
    exact hm ht' hc ht.2

private theorem strictMono_right {h : E × ℝ → ℝ} {u : E} {a b c : ℝ}
    (hc : c ∈ Icc a b) (ha : ∀ t ∈ Icc a b, AnalyticAt ℝ h (u, t))
    (hm : StrictMonoOn (fun t => verticalDeriv h (u, t)) (Icc a b))
    (hz : verticalDeriv h (u, c) = 0) :
    StrictMonoOn (fun t => h (u, t)) (Icc c b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc c b)
  · intro t ht
    exact ((ha t ⟨hc.1.trans ht.1, ht.2⟩).comp
      (analyticAt_slice u t)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have ht' : t ∈ Icc a b := ⟨hc.1.trans ht.1.le, ht.2.le⟩
    rw [deriv_slice (ha t ht'), ← hz]
    exact hm hc ht' ht.1

/-- The closed vertical strip includes both endpoints used in the intermediate value
argument. The open source chart cuts each strip fiber at height `height` above its minimum. -/
structure FoldChart (h : E × ℝ → ℝ) (w : E × ℝ) where
  U : Set E
  open_U : IsOpen U
  convex_U : Convex ℝ U
  mem_U : w.1 ∈ U
  left : ℝ
  right : ℝ
  height : ℝ
  height_pos : 0 < height
  critical : E → ℝ
  critical_at : critical w.1 = w.2
  critical_analytic : AnalyticOnNhd ℝ critical U
  critical_mem : ∀ u ∈ U, critical u ∈ Ioo left right
  critical_zero : ∀ u ∈ U, verticalDeriv h (u, critical u) = 0
  strip_analytic : AnalyticOnNhd ℝ h (U ×ˢ Icc left right)
  strip_pos : ∀ x ∈ U ×ˢ Icc left right, 0 < verticalDeriv (verticalDeriv h) x
  left_gap : ∀ u ∈ U, height < h (u, left) - h (u, critical u)
  right_gap : ∀ u ∈ U, height < h (u, right) - h (u, critical u)

/-- Strict positive vertical curvature gives a fold chart in any prescribed neighborhood. -/
theorem exists_foldChart_pos [CompleteSpace E] {h : E × ℝ → ℝ} {w : E × ℝ}
    (hh : AnalyticAt ℝ h w) (hzero : verticalDeriv h w = 0)
    (hpos : 0 < verticalDeriv (verticalDeriv h) w) {W : Set (E × ℝ)} (hW : W ∈ 𝓝 w) :
    ∃ C : FoldChart h w, C.U ×ˢ Icc C.left C.right ⊆ W := by
  let k := verticalDeriv h
  let T : E × ℝ → E × ℝ := fun x => (x.1, k x)
  let N : E × ℝ → ℝ := fun x => x.2
  have hk : AnalyticAt ℝ k w := analyticAt_verticalDeriv hh
  have hT : AnalyticAt ℝ T w := AnalyticAt.prod ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt w) hk
  have hN : AnalyticAt ℝ N w := (ContinuousLinearMap.snd ℝ E ℝ).analyticAt w
  obtain ⟨e, V, g, he, hw, hV, hwV, -, -, hg, hgraph⟩ :=
    PeriodicMPSLocalObservationGraph.exists_analytic_graph T N w hT hN
      (triangularEquiv (fderiv ℝ k w) hpos.ne') (hasFDerivAt_triangular hk hpos.ne')
  have hTw : T w = (w.1, 0) := Prod.ext rfl hzero
  let c : E → ℝ := fun u => g (u, 0)
  have hwc : c w.1 = w.2 := by
    have h := congrArg Prod.snd (hgraph (T w) hwV)
    rw [← he, e.left_inv hw] at h
    rw [he, hTw] at h
    exact h.symm
  have hc_chart : ∀ᶠ u in 𝓝 w.1, (u, (0 : ℝ)) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt (hV.mem_nhds (hTw ▸ hwV))
  have hc_data : ∀ᶠ u in 𝓝 w.1, AnalyticAt ℝ c u ∧ k (u, c u) = 0 := by
    filter_upwards [hc_chart] with u hu
    have hpair : AnalyticAt ℝ (fun v : E => (v, (0 : ℝ))) u :=
      analyticAt_id.prod analyticAt_const
    refine ⟨(hg _ hu).comp_of_eq hpair rfl, ?_⟩
    have h := hgraph (u, 0) hu
    have hbase : (e.symm (u, 0)).1 = u := congrArg (fun p => p.1.1) h
    have hlevel : k (e.symm (u, 0)) = 0 := congrArg (fun p => p.1.2) h
    have hcrit : (e.symm (u, 0)).2 = c u := congrArg Prod.snd h
    exact (congrArg k (Prod.ext hbase hcrit).symm).trans hlevel
  have hc : AnalyticAt ℝ c w.1 := (hc_data.self_of_nhds).1
  have hnear : ∀ᶠ x in 𝓝 w, AnalyticAt ℝ h x ∧ 0 < verticalDeriv k x ∧ x ∈ W :=
    hh.eventually_analyticAt.and (ContinuousAt.eventually_lt continuousAt_const
      (analyticAt_verticalDeriv hk).continuousAt hpos |>.and hW)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let a := w.2 - r / 2
  let b := w.2 + r / 2
  have hac : a < w.2 := by dsimp [a]; linarith
  have hcb : w.2 < b := by dsimp [b]; linarith
  have hstrip : Metric.ball w.1 r ×ˢ Icc a b ⊆ Metric.ball w r := by
    intro x hx
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨hx.1, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hlo : a ≤ x.2 := hx.2.1
    have hhi : x.2 ≤ b := hx.2.2
    dsimp [a, b] at hlo hhi
    constructor <;> linarith
  have hslice : ∀ t ∈ Icc a b, AnalyticAt ℝ h (w.1, t) := fun t ht =>
    (hball (hstrip (a := (w.1, t)) ⟨Metric.mem_ball_self hr, ht⟩)).1
  have hp : ∀ t ∈ Icc a b, 0 < verticalDeriv k (w.1, t) := fun t ht =>
    (hball (hstrip (a := (w.1, t)) ⟨Metric.mem_ball_self hr, ht⟩)).2.1
  have hwcc : w.2 ∈ Icc a b := ⟨hac.le, hcb.le⟩
  have hm := strictMono_verticalDeriv hslice hp
  have hab := hac.le.trans hcb.le
  have hleft := strictAnti_left hwcc hslice hm hzero ⟨le_rfl, hac.le⟩
    ⟨hac.le, le_rfl⟩ hac
  have hright := strictMono_right hwcc hslice hm hzero ⟨le_rfl, hcb.le⟩
    ⟨hcb.le, le_rfl⟩ hcb
  let ε := min (h (w.1, a) - h w) (h (w.1, b) - h w) / 2
  have hmin : 0 < min (h (w.1, a) - h w) (h (w.1, b) - h w) :=
    lt_min (sub_pos.mpr hleft) (sub_pos.mpr hright)
  have hepos : 0 < ε := by dsimp [ε]; linarith
  have hεl : ε < h (w.1, a) - h w :=
    (half_lt_self hmin).trans_le (min_le_left _ _)
  have hεr : ε < h (w.1, b) - h w :=
    (half_lt_self hmin).trans_le (min_le_right _ _)
  have hcrit_height : AnalyticAt ℝ (fun u => h (u, c u)) w.1 :=
    hh.comp_of_eq (analyticAt_id.prod hc) (Prod.ext rfl hwc)
  have hgap (t : ℝ) (ht : t ∈ Icc a b) (ht' : ε < h (w.1, t) - h w) :
      ∀ᶠ u in 𝓝 w.1, ε < h (u, t) - h (u, c u) := by
    have hh' : AnalyticAt ℝ (fun u => h (u, t)) w.1 :=
      (hslice t ht).comp_of_eq
        (show AnalyticAt ℝ (fun v : E => (v, t)) w.1 from
          analyticAt_id.prod analyticAt_const) rfl
    exact ContinuousAt.eventually_lt continuousAt_const (hh'.sub hcrit_height).continuousAt
      (by simpa only [hwc, Prod.eta] using ht')
  have hcentre : ∀ᶠ u in 𝓝 w.1, c u ∈ Ioo a b :=
    hc.continuousAt (isOpen_Ioo.mem_nhds (hwc.symm ▸ (show w.2 ∈ Ioo a b from ⟨hac, hcb⟩)))
  have hbase : ∀ᶠ u in 𝓝 w.1, u ∈ Metric.ball w.1 r := Metric.ball_mem_nhds _ hr
  obtain ⟨R, hR, hsmall⟩ := Metric.mem_nhds_iff.mp
    (hbase.and (hc_data.and (hcentre.and
      ((hgap a (left_mem_Icc.mpr hab) hεl).and (hgap b (right_mem_Icc.mpr hab) hεr)))))
  refine ⟨⟨Metric.ball w.1 R, Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hR,
    a, b, ε, hepos, c, hwc, fun u hu => (hsmall hu).2.1.1,
    fun u hu => (hsmall hu).2.2.1, fun u hu => (hsmall hu).2.1.2,
    ?_, ?_, fun u hu => (hsmall hu).2.2.2.1, fun u hu => (hsmall hu).2.2.2.2⟩, ?_⟩
  · intro x hx
    exact (hball (hstrip ⟨(hsmall hx.1).1, hx.2⟩)).1
  · intro x hx
    exact (hball (hstrip ⟨(hsmall hx.1).1, hx.2⟩)).2.1
  · intro x hx
    exact (hball (hstrip ⟨(hsmall hx.1).1, hx.2⟩)).2.2

namespace FoldChart

variable {h : E × ℝ → ℝ} {w : E × ℝ} (C : FoldChart h w)

/-- Output height measured from the critical value in that vertical fiber. -/
noncomputable def level (x : E × ℝ) : ℝ := h x - h (x.1, C.critical x.1)

def source : Set (E × ℝ) :=
  {x | x ∈ C.U ×ˢ Ioo C.left C.right ∧ C.level x < C.height}

def target : Set (E × ℝ) := C.U ×ˢ Ioo 0 C.height

noncomputable def forward (x : E × ℝ) : E × ℝ := (x.1, C.level x)

private theorem analyticAt_criticalValue {u : E} (hu : u ∈ C.U) :
    AnalyticAt ℝ (fun v => h (v, C.critical v)) u :=
  (C.strip_analytic _ ⟨hu, Ioo_subset_Icc_self (C.critical_mem u hu)⟩).comp
    (analyticAt_id.prod (C.critical_analytic u hu))

private theorem analyticAt_level {x : E × ℝ} (hx : x ∈ C.U ×ˢ Icc C.left C.right) :
    AnalyticAt ℝ C.level x :=
  (C.strip_analytic x hx).sub
    ((C.analyticAt_criticalValue hx.1).comp ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt x))

theorem open_source : IsOpen C.source := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hh := (C.analyticAt_level ⟨hx.1.1, Ioo_subset_Icc_self hx.1.2⟩).continuousAt
  have hstrip : ∀ᶠ z in 𝓝 x, z ∈ C.U ×ˢ Ioo C.left C.right :=
    (C.open_U.prod isOpen_Ioo).mem_nhds hx.1
  exact hstrip.and (hh.eventually_lt continuousAt_const hx.2)

theorem mem_source : w ∈ C.source := by
  refine ⟨⟨C.mem_U, ?_⟩, ?_⟩
  · rw [← C.critical_at]
    exact C.critical_mem _ C.mem_U
  · simpa only [level, C.critical_at, Prod.eta, sub_self] using C.height_pos

theorem open_target : IsOpen C.target := C.open_U.prod isOpen_Ioo

theorem connected_target : IsConnected C.target := by
  refine ⟨⟨(w.1, C.height / 2), C.mem_U, ?_⟩,
    (C.convex_U.prod (convex_Ioo _ _)).isPreconnected⟩
  exact ⟨half_pos C.height_pos, half_lt_self C.height_pos⟩

theorem continuousOn_forward : ContinuousOn C.forward C.source := by
  intro x hx
  exact (continuous_fst.continuousAt.prodMk
    (C.analyticAt_level ⟨hx.1.1, Ioo_subset_Icc_self hx.1.2⟩).continuousAt).continuousWithinAt

private theorem strictMono_deriv {u : E} (hu : u ∈ C.U) :
    StrictMonoOn (fun t => verticalDeriv h (u, t)) (Icc C.left C.right) :=
  strictMono_verticalDeriv (fun t ht => C.strip_analytic (u, t) ⟨hu, ht⟩)
    (fun t ht => C.strip_pos (u, t) ⟨hu, ht⟩)

private theorem anti_left {u : E} (hu : u ∈ C.U) :
    StrictAntiOn (fun t => h (u, t)) (Icc C.left (C.critical u)) :=
  strictAnti_left (Ioo_subset_Icc_self (C.critical_mem u hu))
    (fun t ht => C.strip_analytic (u, t) ⟨hu, ht⟩) (C.strictMono_deriv hu) (C.critical_zero u hu)

private theorem mono_right {u : E} (hu : u ∈ C.U) :
    StrictMonoOn (fun t => h (u, t)) (Icc (C.critical u) C.right) :=
  strictMono_right (Ioo_subset_Icc_self (C.critical_mem u hu))
    (fun t ht => C.strip_analytic (u, t) ⟨hu, ht⟩) (C.strictMono_deriv hu) (C.critical_zero u hu)

theorem level_pos_iff {x : E × ℝ} (hx : x ∈ C.U ×ˢ Icc C.left C.right) :
    0 < C.level x ↔ x.2 ≠ C.critical x.1 := by
  have hc := C.critical_mem x.1 hx.1
  have ht := hx.2
  change 0 < h (x.1, x.2) - h (x.1, C.critical x.1) ↔ _
  rw [sub_pos]
  constructor
  · intro hlt he
    rw [he] at hlt
    exact (lt_irrefl _) hlt
  · intro hne
    rcases lt_or_gt_of_ne hne with hl | hr
    · exact C.anti_left hx.1 ⟨ht.1, hl.le⟩ ⟨hc.1.le, le_rfl⟩ hl
    · exact C.mono_right hx.1 ⟨le_rfl, hc.2.le⟩ ⟨hr.le, ht.2⟩ hr

/-- In the closed strip the critical value is attained exactly at the critical point. -/
theorem level_eq_zero_iff {x : E × ℝ} (hx : x ∈ C.U ×ˢ Icc C.left C.right) :
    C.level x = 0 ↔ x.2 = C.critical x.1 := by
  constructor
  · intro hz
    by_contra hn
    have hp := (C.level_pos_iff hx).mpr hn
    rw [hz] at hp
    exact (lt_irrefl _) hp
  · intro hc
    have he : (x.1, C.critical x.1) = x := Prod.ext rfl hc.symm
    simp only [level, he, sub_self]

private theorem exists_left_root {y : E × ℝ} (hy : y ∈ C.target) :
    ∃ t ∈ Ioo C.left (C.critical y.1), h (y.1, t) = y.2 + h (y.1, C.critical y.1) := by
  have hc := C.critical_mem y.1 hy.1
  have hy' := hy.2
  have hh : ContinuousOn (fun t => h (y.1, t)) (Icc C.left (C.critical y.1)) := by
    intro t ht
    exact ((C.strip_analytic (y.1, t) ⟨hy.1, ht.1, ht.2.trans hc.2.le⟩).comp
      (analyticAt_slice _ _)).continuousAt.continuousWithinAt
  have hlow : h (y.1, C.critical y.1) < y.2 + h (y.1, C.critical y.1) := by
    linarith [hy'.1]
  have hhigh : y.2 + h (y.1, C.critical y.1) < h (y.1, C.left) := by
    linarith [hy'.2, C.left_gap y.1 hy.1]
  obtain ⟨t, ht, he⟩ :=
    intermediate_value_Icc' hc.1.le hh (show _ ∈ Icc _ _ from ⟨hlow.le, hhigh.le⟩)
  exact ⟨t, ⟨ht.1.lt_of_ne (fun eq => hhigh.ne (by simpa only [eq] using he.symm)),
    ht.2.lt_of_ne (fun eq => hlow.ne (by simpa only [eq] using he))⟩, he⟩

private theorem exists_right_root {y : E × ℝ} (hy : y ∈ C.target) :
    ∃ t ∈ Ioo (C.critical y.1) C.right, h (y.1, t) = y.2 + h (y.1, C.critical y.1) := by
  have hc := C.critical_mem y.1 hy.1
  have hy' := hy.2
  have hh : ContinuousOn (fun t => h (y.1, t)) (Icc (C.critical y.1) C.right) := by
    intro t ht
    exact ((C.strip_analytic (y.1, t) ⟨hy.1, hc.1.le.trans ht.1, ht.2⟩).comp
      (analyticAt_slice _ _)).continuousAt.continuousWithinAt
  have hlow : h (y.1, C.critical y.1) < y.2 + h (y.1, C.critical y.1) := by
    linarith [hy'.1]
  have hhigh : y.2 + h (y.1, C.critical y.1) < h (y.1, C.right) := by
    linarith [hy'.2, C.right_gap y.1 hy.1]
  obtain ⟨t, ht, he⟩ :=
    intermediate_value_Icc hc.2.le hh (show _ ∈ Icc _ _ from ⟨hlow.le, hhigh.le⟩)
  exact ⟨t, ⟨ht.1.lt_of_ne (fun eq => hlow.ne (by simpa only [← eq] using he)),
    ht.2.lt_of_ne (fun eq => hhigh.ne (by simpa only [eq] using he.symm))⟩, he⟩

private def leftSide : Set (E × ℝ) :=
  {x | x.1 ∈ C.U ∧ C.left < x.2 ∧ x.2 < C.critical x.1}

private def rightSide : Set (E × ℝ) :=
  {x | x.1 ∈ C.U ∧ C.critical x.1 < x.2 ∧ x.2 < C.right}

private theorem open_leftSide : IsOpen C.leftSide := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hu : ∀ᶠ z in 𝓝 x, z.1 ∈ C.U :=
    continuous_fst.continuousAt (C.open_U.mem_nhds hx.1)
  have hc : ContinuousAt (C.critical ∘ Prod.fst) x :=
    (C.critical_analytic _ hx.1).continuousAt.comp continuous_fst.continuousAt
  exact hu.and ((ContinuousAt.eventually_lt continuousAt_const continuous_snd.continuousAt hx.2.1).and
    (continuous_snd.continuousAt.eventually_lt hc hx.2.2))

private theorem open_rightSide : IsOpen C.rightSide := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hu : ∀ᶠ z in 𝓝 x, z.1 ∈ C.U :=
    continuous_fst.continuousAt (C.open_U.mem_nhds hx.1)
  have hc : ContinuousAt (C.critical ∘ Prod.fst) x :=
    (C.critical_analytic _ hx.1).continuousAt.comp continuous_fst.continuousAt
  exact hu.and ((hc.eventually_lt continuous_snd.continuousAt hx.2.1).and
    (continuous_snd.continuousAt.eventually_lt continuousAt_const hx.2.2))

/-- The two scalar inverse branches of a chart, with their ordering and equations. -/
structure Branches where
  lower : E × ℝ → ℝ
  upper : E × ℝ → ℝ
  lower_analytic : AnalyticOnNhd ℝ lower C.target
  upper_analytic : AnalyticOnNhd ℝ upper C.target
  lower_mem : ∀ y ∈ C.target, lower y ∈ Ioo C.left (C.critical y.1)
  upper_mem : ∀ y ∈ C.target, upper y ∈ Ioo (C.critical y.1) C.right
  lower_eq : ∀ y ∈ C.target, h (y.1, lower y) = y.2 + h (y.1, C.critical y.1)
  upper_eq : ∀ y ∈ C.target, h (y.1, upper y) = y.2 + h (y.1, C.critical y.1)

/-- Intermediate values give the two roots. Strict monotonicity selects them uniquely,
so the analytic inverses at regular points agree with these selections. -/
theorem exists_branches [CompleteSpace E] : Nonempty C.Branches := by
  classical
  have hl_ex : ∀ y ∈ C.target, ∃ t ∈ Ioo C.left (C.critical y.1),
      h (y.1, t) = y.2 + h (y.1, C.critical y.1) := fun _ => C.exists_left_root
  have hr_ex : ∀ y ∈ C.target, ∃ t ∈ Ioo (C.critical y.1) C.right,
      h (y.1, t) = y.2 + h (y.1, C.critical y.1) := fun _ => C.exists_right_root
  choose! l hl hle using hl_ex
  choose! r hr hre using hr_ex
  let k : E × ℝ → ℝ := fun y => y.2 + h (y.1, C.critical y.1)
  have hk (y : E × ℝ) (hy : y ∈ C.target) : AnalyticAt ℝ k y :=
    AnalyticAt.add ((ContinuousLinearMap.snd ℝ E ℝ).analyticAt y)
      ((C.analyticAt_criticalValue hy.1).comp ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt y))
  refine ⟨⟨l, r, ?_, ?_, hl, hr, hle, hre⟩⟩
  · intro y hy
    have hc := C.critical_mem y.1 hy.1
    have hm : (y.1, l y) ∈ C.U ×ˢ Icc C.left C.right :=
      ⟨hy.1, (hl y hy).1.le, (hl y hy).2.le.trans hc.2.le⟩
    refine analyticAt_selected_root C.open_leftSide
      ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt y) (hk y hy)
      ⟨hy.1, hl y hy⟩ (hle y hy) (C.strip_analytic _ hm) ?_ ?_
    · have hlt := C.strictMono_deriv hy.1 hm.2 (Ioo_subset_Icc_self hc) (hl y hy).2
      exact (hlt.trans_eq (C.critical_zero _ hy.1)).ne
    · filter_upwards [C.open_target.mem_nhds hy] with z hz t ht he
      exact (C.anti_left hz.1).injOn ⟨ht.2.1.le, ht.2.2.le⟩
        (Ioo_subset_Icc_self (hl z hz)) (he.trans (hle z hz).symm)
  · intro y hy
    have hc := C.critical_mem y.1 hy.1
    have hm : (y.1, r y) ∈ C.U ×ˢ Icc C.left C.right :=
      ⟨hy.1, hc.1.le.trans (hr y hy).1.le, (hr y hy).2.le⟩
    refine analyticAt_selected_root C.open_rightSide
      ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt y) (hk y hy)
      ⟨hy.1, hr y hy⟩ (hre y hy) (C.strip_analytic _ hm) ?_ ?_
    · have hlt := C.strictMono_deriv hy.1 (Ioo_subset_Icc_self hc) hm.2 (hr y hy).1
      exact ((C.critical_zero _ hy.1).symm.trans_lt hlt).ne'
    · filter_upwards [C.open_target.mem_nhds hy] with z hz t ht he
      exact (C.mono_right hz.1).injOn ⟨ht.2.1.le, ht.2.2.le⟩
        (Ioo_subset_Icc_self (hr z hz)) (he.trans (hre z hz).symm)

namespace Branches

variable {C} (B : C.Branches)

/-- Exactly two roots, even if candidates are allowed throughout the closed strip. -/
theorem root_iff {y : E × ℝ} (hy : y ∈ C.target) {t : ℝ} (ht : t ∈ Icc C.left C.right) :
    h (y.1, t) = y.2 + h (y.1, C.critical y.1) ↔ t = B.lower y ∨ t = B.upper y := by
  constructor
  · intro he
    rcases le_total t (C.critical y.1) with htc | hct
    · exact Or.inl ((C.anti_left hy.1).injOn ⟨ht.1, htc⟩
        (Ioo_subset_Icc_self (B.lower_mem y hy)) (he.trans (B.lower_eq y hy).symm))
    · exact Or.inr ((C.mono_right hy.1).injOn ⟨hct, ht.2⟩
        (Ioo_subset_Icc_self (B.upper_mem y hy)) (he.trans (B.upper_eq y hy).symm))
  · rintro (rfl | rfl)
    · exact B.lower_eq y hy
    · exact B.upper_eq y hy

theorem lower_lt_upper {y : E × ℝ} (hy : y ∈ C.target) : B.lower y < B.upper y :=
  (B.lower_mem y hy).2.trans (B.upper_mem y hy).1

theorem lower_source {y : E × ℝ} (hy : y ∈ C.target) : (y.1, B.lower y) ∈ C.source := by
  have hc := C.critical_mem y.1 hy.1
  refine ⟨⟨hy.1, (B.lower_mem y hy).1, (B.lower_mem y hy).2.trans hc.2⟩, ?_⟩
  simpa only [level, B.lower_eq y hy, add_sub_cancel_right] using hy.2.2

theorem upper_source {y : E × ℝ} (hy : y ∈ C.target) : (y.1, B.upper y) ∈ C.source := by
  have hc := C.critical_mem y.1 hy.1
  refine ⟨⟨hy.1, hc.1.trans (B.upper_mem y hy).1, (B.upper_mem y hy).2⟩, ?_⟩
  simpa only [level, B.upper_eq y hy, add_sub_cancel_right] using hy.2.2

theorem forward_lower {y : E × ℝ} (hy : y ∈ C.target) :
    C.forward (y.1, B.lower y) = y :=
  Prod.ext rfl (by simp only [forward, level, B.lower_eq y hy, add_sub_cancel_right])

theorem forward_upper {y : E × ℝ} (hy : y ∈ C.target) :
    C.forward (y.1, B.upper y) = y :=
  Prod.ext rfl (by simp only [forward, level, B.upper_eq y hy, add_sub_cancel_right])

/-- The fiber over a point in the positive output region is exactly the two sheets. -/
theorem forward_eq_iff {y x : E × ℝ} (hy : y ∈ C.target) (hx : x ∈ C.source) :
    C.forward x = y ↔ x = (y.1, B.lower y) ∨ x = (y.1, B.upper y) := by
  constructor
  · intro he
    have hu : x.1 = y.1 := by
      have hp := congrArg Prod.fst he
      exact hp
    have ht : x.2 ∈ Icc C.left C.right := Ioo_subset_Icc_self hx.1.2
    have hh : h (y.1, x.2) = y.2 + h (y.1, C.critical y.1) := by
      have hv : h x - h (x.1, C.critical x.1) = y.2 := by
        have hp := congrArg Prod.snd he
        exact hp
      rw [← hu, Prod.eta]
      exact (sub_eq_iff_eq_add).mp hv
    exact ((B.root_iff hy ht).mp hh).imp (Prod.ext hu) (Prod.ext hu)
  · rintro (rfl | rfl)
    · exact B.forward_lower hy
    · exact B.forward_upper hy

private noncomputable def sheet (i : Bool) (y : E × ℝ) : E × ℝ :=
  (y.1, if i then B.upper y else B.lower y)

private theorem sheet_analytic (i : Bool) : AnalyticOnNhd ℝ (B.sheet i) C.target := by
  intro y hy
  cases i
  · exact AnalyticAt.prod ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt y) (B.lower_analytic y hy)
  · exact AnalyticAt.prod ((ContinuousLinearMap.fst ℝ E ℝ).analyticAt y) (B.upper_analytic y hy)

private theorem sheet_source (i : Bool) {y : E × ℝ} (hy : y ∈ C.target) :
    B.sheet i y ∈ C.source := by
  cases i
  · exact B.lower_source hy
  · exact B.upper_source hy

private theorem forward_sheet (i : Bool) {y : E × ℝ} (hy : y ∈ C.target) :
    C.forward (B.sheet i y) = y := by
  cases i
  · exact B.forward_lower hy
  · exact B.forward_upper hy

private theorem exists_sheet {x y : E × ℝ} (hx : x ∈ C.source) (hy : y ∈ C.target)
    (he : C.forward x = y) : ∃ i, x = B.sheet i y := by
  rcases (B.forward_eq_iff hy hx).mp he with hl | hr
  · exact ⟨false, hl⟩
  · exact ⟨true, hr⟩

/-- One differing residual pair on the connected target makes separation open and dense. -/
theorem residual_separates {j : E × ℝ → ℝ} (hj : AnalyticOnNhd ℝ j C.source)
    (hpair : ∃ y ∈ C.target, j (y.1, B.lower y) ≠ j (y.1, B.upper y)) :
    IsOpen {y : C.target | j (y.val.1, B.lower y) ≠ j (y.val.1, B.upper y)} ∧
    Dense {y : C.target | j (y.val.1, B.lower y) ≠ j (y.val.1, B.upper y)} := by
  let f : Bool → (E × ℝ) → ℝ := fun i => j ∘ B.sheet i
  have hf (i : Bool) : AnalyticOnNhd ℝ (f i) C.target := fun y hy =>
    (hj _ (B.sheet_source i hy)).comp (B.sheet_analytic i y hy)
  obtain ⟨y, hy, hne⟩ := hpair
  have hneq (i k : Bool) (hik : i ≠ k) : ¬ EqOn (f i) (f k) C.target := by
    intro he
    have hh := he hy
    cases i <;> cases k
    · exact hik rfl
    · exact hne hh
    · exact hne hh.symm
    · exact hik rfl
  have hinj :=
    PeriodicMPSAnalyticBranchSeparation.generic_injective_graph_values C.target C.open_target
      C.connected_target.isPreconnected f hf hneq
  have he : {y : C.target | Function.Injective (fun i => f i y)} =
      {y : C.target | j (y.val.1, B.lower y) ≠ j (y.val.1, B.upper y)} := by
    ext z
    change Function.Injective (fun i => f i z) ↔ f false z ≠ f true z
    constructor
    · intro h eq
      exact Bool.false_ne_true (h eq)
    · intro h i k eq
      cases i <;> cases k
      · rfl
      · exact (h eq).elim
      · exact (h eq.symm).elim
      · rfl
  rwa [he] at hinj

theorem residual_coincidence_nowhereDense {j : E × ℝ → ℝ}
    (hj : AnalyticOnNhd ℝ j C.source)
    (hpair : ∃ y ∈ C.target, j (y.1, B.lower y) ≠ j (y.1, B.upper y)) :
    IsClosed {y : C.target | j (y.val.1, B.lower y) = j (y.val.1, B.upper y)} ∧
    IsNowhereDense {y : C.target | j (y.val.1, B.lower y) = j (y.val.1, B.upper y)} := by
  simpa only [isClosed_isNowhereDense_iff_compl, compl_ofPred, mem_ofPred_eq] using
    B.residual_separates hj hpair

end Branches

theorem forward_eq_forward_iff {x z : E × ℝ} :
    C.forward x = C.forward z ↔ (x.1, h x) = (z.1, h z) := by
  constructor <;> intro he
  · have hu : x.1 = z.1 := by
      have hp := congrArg Prod.fst he
      exact hp
    have hv : C.level x = C.level z := congrArg Prod.snd he
    simp only [level, hu] at hv
    exact Prod.ext hu (by linarith)
  · have hu := congrArg Prod.fst he
    have hh := congrArg Prod.snd he
    change x.1 = z.1 at hu
    change h x = h z at hh
    exact Prod.ext hu (by simp only [forward, level, hh, hu])

private theorem forward_mem_target {x : E × ℝ} (hx : x ∈ C.source)
    (hne : x.2 ≠ C.critical x.1) : C.forward x ∈ C.target :=
  ⟨hx.1.1, (C.level_pos_iff ⟨hx.1.1, Ioo_subset_Icc_self hx.1.2⟩).mpr hne, hx.2⟩

private theorem exists_regular_mem {V : Set C.source} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ x ∈ V, C.forward x.val ∈ C.target := by
  obtain ⟨x, hx⟩ := hne
  by_cases he : x.val.2 = C.critical x.val.1
  · let W : Set (E × ℝ) := Subtype.val '' V
    have hW := C.open_source.isOpenMap_subtype_val _ hV
    have hW' : IsOpen ((fun t : ℝ => (x.val.1, t)) ⁻¹' W) :=
      hW.preimage (continuous_const.prodMk continuous_id)
    have hxW : x.val.2 ∈ (fun t : ℝ => (x.val.1, t)) ⁻¹' W := by
      exact ⟨x, hx, Prod.eta _ |>.symm⟩
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW'.mem_nhds hxW)
    let t := x.val.2 + r / 2
    have ht : t ∈ Metric.ball x.val.2 r := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      dsimp only [t]
      constructor <;> linarith
    have htW : (x.val.1, t) ∈ W := hball ht
    obtain ⟨z, hz, hez⟩ := htW
    refine ⟨z, hz, C.forward_mem_target z.property ?_⟩
    rw [hez]
    change t ≠ C.critical x.val.1
    rw [← he]
    dsimp only [t]
    exact ne_of_gt (by linarith)
  · exact ⟨x, hx, C.forward_mem_target x.property he⟩

namespace Branches

variable {C} (B : C.Branches)

/-- A differing pair makes the full observation have singleton fibers on a relatively
open dense subset of the source chart. Competitors range over the entire source chart. -/
theorem generic_singleton_fibers {j : E × ℝ → ℝ} (hj : AnalyticOnNhd ℝ j C.source)
    (hpair : ∃ y ∈ C.target, j (y.1, B.lower y) ≠ j (y.1, B.upper y)) :
    ∃ G : Set C.source, IsOpen G ∧ Dense G ∧
      ∀ x ∈ G, ∀ z : C.source, (z.val.1, h z.val, j z.val) =
        (x.val.1, h x.val, j x.val) → z = x := by
  let D : Set C.target := {y | j (y.val.1, B.lower y) ≠ j (y.val.1, B.upper y)}
  have hD : IsOpen D ∧ Dense D := B.residual_separates hj hpair
  let G : Set C.source := (C.forward ∘ Subtype.val) ⁻¹' (Subtype.val '' D)
  refine ⟨G, (C.open_target.isOpenMap_subtype_val _ hD.1).preimage
    C.continuousOn_forward.domRestrict, ?_, ?_⟩
  · refine dense_iff_inter_open.mpr ?_
    intro V hV hne
    obtain ⟨x, hx, hxT⟩ := C.exists_regular_mem hV hne
    let y : C.target := ⟨C.forward x, hxT⟩
    obtain ⟨i, hi⟩ := B.exists_sheet x.property hxT rfl
    let S : C.target → C.source := fun z => ⟨B.sheet i z, B.sheet_source i z.property⟩
    have hS : Continuous S :=
      (B.sheet_analytic i).continuousOn.domRestrict.subtype_mk _
    have hy : y ∈ S ⁻¹' V := by
      have he : S y = x := Subtype.ext hi.symm
      change S y ∈ V
      rw [he]
      exact hx
    obtain ⟨z, hzV, hzD⟩ := dense_iff_inter_open.mp hD.2 _ (hV.preimage hS) ⟨y, hy⟩
    exact ⟨S z, hzV, ⟨z, hzD, (B.forward_sheet i z.property).symm⟩⟩
  · intro x hx z he
    obtain ⟨y, hyD, hy⟩ := hx
    have hxF : C.forward x.val = y.val := hy.symm
    have hzF : C.forward z.val = y.val := by
      apply Eq.trans (C.forward_eq_forward_iff.mpr ?_) hxF
      exact congrArg (fun p => (p.1, p.2.1)) he
    have hjEq : j z.val = j x.val := congrArg (fun p => p.2.2) he
    apply Subtype.ext
    rcases (B.forward_eq_iff y.property x.property).mp hxF with hxL | hxR <;>
      rcases (B.forward_eq_iff y.property z.property).mp hzF with hzL | hzR
    · exact hzL.trans hxL.symm
    · exact (hyD (by simpa only [hxL, hzR] using hjEq.symm)).elim
    · exact (hyD (by simpa only [hxR, hzL] using hjEq)).elim
    · exact hzR.trans hxR.symm

/-- A certificate can be given directly by two points with the same first outputs and
different residuals. The critical fiber is a singleton, so this pair lies over a positive level. -/
theorem generic_singleton_fibers_of_pair [CompleteSpace E] {j : E × ℝ → ℝ}
    (hj : AnalyticOnNhd ℝ j C.source)
    (hpair : ∃ x ∈ C.source, ∃ z ∈ C.source,
      (x.1, h x) = (z.1, h z) ∧ j x ≠ j z) :
    ∃ G : Set C.source, IsOpen G ∧ Dense G ∧
      ∀ x ∈ G, ∀ z : C.source, (z.val.1, h z.val, j z.val) =
        (x.val.1, h x.val, j x.val) → z = x := by
  obtain ⟨B⟩ := C.exists_branches
  obtain ⟨x, hx, z, hz, he, hjne⟩ := hpair
  have hF := C.forward_eq_forward_iff.mpr he
  have hu := congrArg Prod.fst he
  have hv : C.level x = C.level z := congrArg Prod.snd hF
  have hxne : x.2 ≠ C.critical x.1 := by
    intro hec
    have hx0 := (C.level_eq_zero_iff ⟨hx.1.1, Ioo_subset_Icc_self hx.1.2⟩).mpr hec
    have hzc := (C.level_eq_zero_iff ⟨hz.1.1, Ioo_subset_Icc_self hz.1.2⟩).mp
      (hv.symm.trans hx0)
    exact hjne (congrArg j (Prod.ext hu (hec.trans ((congrArg C.critical hu).trans hzc.symm))))
  have hy := C.forward_mem_target hx hxne
  refine B.generic_singleton_fibers hj ⟨C.forward x, hy, ?_⟩
  rcases (B.forward_eq_iff hy hx).mp rfl with hxL | hxR <;>
    rcases (B.forward_eq_iff hy hz).mp hF.symm with hzL | hzR
  · exact (hjne (congrArg j (hxL.trans hzL.symm))).elim
  · intro he
    exact hjne ((congrArg j hxL).trans (he.trans (congrArg j hzR).symm))
  · intro he
    exact hjne ((congrArg j hxR).trans (he.symm.trans (congrArg j hzL).symm))
  · exact (hjne (congrArg j (hxR.trans hzR.symm))).elim

end Branches
end FoldChart

private theorem verticalDeriv_neg (h : E × ℝ → ℝ) :
    verticalDeriv (-h) = -verticalDeriv h := by
  funext x
  rw [verticalDeriv, fderiv_neg]
  rfl

/-- Either sign of nonzero vertical curvature gives the same fold after a possible sign
change of the scalar output. The entire closed strip can be placed in any given neighborhood. -/
theorem exists_foldChart [CompleteSpace E] {h : E × ℝ → ℝ} {w : E × ℝ}
    (hh : AnalyticAt ℝ h w) (hzero : verticalDeriv h w = 0)
    (hne : verticalDeriv (verticalDeriv h) w ≠ 0) {W : Set (E × ℝ)} (hW : W ∈ 𝓝 w) :
    ∃ g : E × ℝ → ℝ, (g = h ∨ g = -h) ∧
      ∃ C : FoldChart g w, C.U ×ˢ Icc C.left C.right ⊆ W := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨-h, Or.inr rfl, exists_foldChart_pos hh.neg ?_ ?_ hW⟩
    · rw [verticalDeriv_neg, Pi.neg_apply, hzero, neg_zero]
    · rw [verticalDeriv_neg, verticalDeriv_neg, Pi.neg_apply]
      exact neg_pos.mpr hneg
  · exact ⟨h, Or.inl rfl, exists_foldChart_pos hh hzero hpos hW⟩

/-- A nondegenerate fold has two analytic inverse sheets in any prescribed neighborhood
of the witness. The target and the exact fibers are described by `FoldChart` and
`FoldChart.Branches`. -/
theorem exists_analytic_fold [CompleteSpace E] {h : E × ℝ → ℝ} {w : E × ℝ}
    (hh : AnalyticAt ℝ h w) (hzero : verticalDeriv h w = 0)
    (hne : verticalDeriv (verticalDeriv h) w ≠ 0) {W : Set (E × ℝ)} (hW : W ∈ 𝓝 w) :
    ∃ g : E × ℝ → ℝ, (g = h ∨ g = -h) ∧ ∃ C : FoldChart g w,
      C.U ×ˢ Icc C.left C.right ⊆ W ∧ Nonempty C.Branches := by
  obtain ⟨g, hg, C, hC⟩ := exists_foldChart hh hzero hne hW
  exact ⟨g, hg, C, hC, C.exists_branches⟩

/-- When differing paired points can be certified arbitrarily close to the witness, every
neighborhood contains an open chart with a relatively open dense subset of singleton fibers. -/
theorem exists_generic_singleton_fibers [CompleteSpace E] {h j : E × ℝ → ℝ} {w : E × ℝ}
    (hh : AnalyticAt ℝ h w) (hj : AnalyticAt ℝ j w) (hzero : verticalDeriv h w = 0)
    (hne : verticalDeriv (verticalDeriv h) w ≠ 0)
    (hpair : ∀ W : Set (E × ℝ), W ∈ 𝓝 w → ∃ x ∈ W, ∃ z ∈ W,
      (x.1, h x) = (z.1, h z) ∧ j x ≠ j z)
    {W : Set (E × ℝ)} (hW : W ∈ 𝓝 w) :
    ∃ S : Set (E × ℝ), IsOpen S ∧ w ∈ S ∧ S ⊆ W ∧
      ∃ G : Set S, IsOpen G ∧ Dense G ∧
        ∀ x ∈ G, ∀ z : S, (z.val.1, h z.val, j z.val) =
          (x.val.1, h x.val, j x.val) → z = x := by
  have hnear : ∀ᶠ p in 𝓝 w, p ∈ W := hW
  obtain ⟨g, hg, C, hC⟩ := exists_foldChart hh hzero hne (hnear.and hj.eventually_analyticAt)
  have hsub : C.source ⊆ W ∩ {x | AnalyticAt ℝ j x} := fun _ hx =>
    hC ⟨hx.1.1, Ioo_subset_Icc_self hx.1.2⟩
  have heq {x z : E × ℝ} (he : (x.1, h x) = (z.1, h z)) :
      (x.1, g x) = (z.1, g z) := by
    rcases hg with hgh | hgh
    · simpa only [hgh] using he
    · rw [hgh]
      exact congrArg (fun p : E × ℝ => (p.1, -p.2)) he
  obtain ⟨x, hx, z, hz, hp, hjne⟩ := hpair C.source (C.open_source.mem_nhds C.mem_source)
  obtain ⟨G, ho, hd, hinj⟩ := FoldChart.Branches.generic_singleton_fibers_of_pair
    (C := C) (fun p hp => (hsub hp).2) ⟨x, hx, z, hz, heq hp, hjne⟩
  refine ⟨C.source, C.open_source, C.mem_source, fun p hp => (hsub hp).1, G, ho, hd, ?_⟩
  intro p hp q hobs
  have hfirst := heq (congrArg (fun a => (a.1, a.2.1)) hobs)
  have hlast := congrArg (fun a => a.2.2) hobs
  have hu := congrArg Prod.fst hfirst
  have hhg := congrArg Prod.snd hfirst
  exact hinj p hp q (Prod.ext hu (Prod.ext hhg hlast))

end D5.S3.Quantum.TensorNetworks.PeriodicMPSAnalyticFold
