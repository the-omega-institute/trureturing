/- GID: D5/S3/Geometry/Lorentz/SachsJacobsonEinstein4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/SachsJacobsonEinstein4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Null optics, focusing, and the local horizon equation of state. -/

import D5.S0.Certificates.MinkowskiNullConeRigidity
import D5.S3.Geometry.Lorentz.WeylNullScreen
import D5.S3.Quantum.Analysis.NullConeGravity.NullConeClockAreaBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix

namespace D5.S3.Geometry.Lorentz.SachsJacobsonEinstein4D
open D5.S3.Geometry.Lorentz
-- The Ricci term is the full screen trace R(k,k), and equals twice the Newman–Penrose Φ₀₀.
structure OpticalData where
  expansion : ℝ → ℝ
  shear : ℝ → ℂ
  radius : ℝ → ℝ
  ricciTerm : ℝ → ℝ
  tideTerm : ℝ → ℂ
def focusing (o : OpticalData) (t : ℝ) : ℝ :=
  (Complex.normSq (o.shear t) + o.ricciTerm t) / 2
structure SolvesOn (o : OpticalData) (I : Set ℝ) : Prop where
  expansion' : ∀ t ∈ I, HasDerivAt o.expansion
    (-((o.expansion t)^2 / 2) - Complex.normSq (o.shear t) - o.ricciTerm t) t
  shear' : ∀ t ∈ I, HasDerivAt o.shear
    (-(o.expansion t : ℂ) * o.shear t - o.tideTerm t) t
  radius' : ∀ t ∈ I, HasDerivAt o.radius (o.expansion t * o.radius t / 2) t
def area (o : OpticalData) (t : ℝ) : ℝ := o.radius t ^ 2
def radiusSlope (o : OpticalData) (t : ℝ) : ℝ := o.expansion t * o.radius t / 2
/-- The logarithmic area derivative. -/
theorem hasDerivAt_area {o : OpticalData} {I : Set ℝ} (h : SolvesOn o I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (area o) (o.expansion t * area o t) t := by
  convert (h.radius' t ht).pow 2 using 1
  · rfl
  · unfold area
    ring
/-- The linear second-order optical equation follows by cancellation of the expansion square. -/
theorem hasDerivAt_radiusSlope {o : OpticalData} {I : Set ℝ} (h : SolvesOn o I)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (radiusSlope o) (-focusing o t * o.radius t) t := by
  convert ((h.expansion' t ht).mul (h.radius' t ht)).div_const 2 using 1
  · rfl
  · unfold focusing
    ring
theorem area_radius_focusing {o : OpticalData} {I : Set ℝ} (h : SolvesOn o I)
    (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) :
    deriv (deriv o.radius) t + focusing o t * o.radius t = 0 := by
  have he : deriv o.radius =ᶠ[𝓝 t] radiusSlope o := by
    filter_upwards [hI.mem_nhds ht] with x hx
    exact (h.radius' x hx).deriv
  rw [he.deriv_eq, (hasDerivAt_radiusSlope h ht).deriv]
  ring
private theorem antitone_of_derivs {f f' : ℝ → ℝ} {I : Set ℝ} (hI : Convex ℝ I)
    (h : ∀ t ∈ I, HasDerivAt f (f' t) t) (hn : ∀ t ∈ I, f' t ≤ 0) : AntitoneOn f I :=
  antitoneOn_of_deriv_nonpos hI (fun t ht => (h t ht).continuousAt.continuousWithinAt)
    (fun t ht => (h t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(h t (interior_subset ht)).deriv]; exact hn t (interior_subset ht))
/-- NEC makes the expansion antitone, the radius slope antitone, and the radius concave
where the radius is nonnegative. -/
theorem optical_nec_bounds {o : OpticalData} {I : Set ℝ} (h : SolvesOn o I)
    (hI : Convex ℝ I) (hn : ∀ t ∈ I, 0 ≤ o.ricciTerm t)
    (hr : ∀ t ∈ I, 0 ≤ o.radius t) :
    (∀ t ∈ I, 0 ≤ focusing o t ∧ -focusing o t * o.radius t ≤ 0 ∧
      deriv o.expansion t ≤ -(o.expansion t)^2 / 2) ∧
    AntitoneOn o.expansion I ∧ AntitoneOn (radiusSlope o) I ∧ ConcaveOn ℝ I o.radius := by
  have hf (t : ℝ) (ht : t ∈ I) : 0 ≤ focusing o t :=
    div_nonneg (add_nonneg (Complex.normSq_nonneg _) (hn t ht)) (by norm_num)
  have ha : AntitoneOn (radiusSlope o) I :=
    antitone_of_derivs hI (fun t ht => hasDerivAt_radiusSlope h ht)
      (fun t ht => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hf t ht)) (hr t ht))
  refine ⟨fun t ht => ⟨hf t ht, mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hf t ht)) (hr t ht), ?_⟩,
    antitone_of_derivs hI h.expansion' (fun t ht => ?_), ha, ?_⟩
  · rw [(h.expansion' t ht).deriv]
    linarith [Complex.normSq_nonneg (o.shear t), hn t ht]
  · nlinarith [Complex.normSq_nonneg (o.shear t), hn t ht, sq_nonneg (o.expansion t)]
  · apply AntitoneOn.concaveOn_of_deriv hI (fun t ht => (h.radius' t ht).continuousAt.continuousWithinAt)
      (fun t ht => (h.radius' t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro x hx y hy hxy
    rw [(h.radius' x (interior_subset hx)).deriv, (h.radius' y (interior_subset hy)).deriv]
    exact ha (interior_subset hx) (interior_subset hy) hxy
/-- A initially contracting congruence has increasing inverse expansion. -/
theorem reciprocal_expansion_bound {o : OpticalData} {t : ℝ} (ht : 0 ≤ t)
    (h : SolvesOn o (Icc 0 t)) (hn : ∀ x ∈ Icc 0 t, 0 ≤ o.ricciTerm x)
    (h₀ : o.expansion 0 < 0) :
    o.expansion t < 0 ∧ (o.expansion 0)⁻¹ + t / 2 ≤ (o.expansion t)⁻¹ := by
  have hanti := antitone_of_derivs (convex_Icc (0 : ℝ) t) h.expansion'
    (fun x hx => by nlinarith [Complex.normSq_nonneg (o.shear x), hn x hx, sq_nonneg (o.expansion x)])
  have hneg (x : ℝ) (hx : x ∈ Icc 0 t) : o.expansion x < 0 :=
    (hanti ⟨le_rfl, ht⟩ hx hx.1).trans_lt h₀
  let f := fun x : ℝ => (o.expansion x)⁻¹ - x / 2
  have hd (x : ℝ) (hx : x ∈ Icc 0 t) :
      HasDerivAt f (-(-((o.expansion x)^2 / 2) -
        Complex.normSq (o.shear x) - o.ricciTerm x) / (o.expansion x)^2 - 1/2) x := by
    convert ((h.expansion' x hx).inv (hneg x hx).ne).sub ((hasDerivAt_id x).div_const 2) using 1
    rfl
  have hm : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    have hsq := sq_pos_of_ne_zero (hneg x (interior_subset hx)).ne
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hsq).2
    linarith [Complex.normSq_nonneg (o.shear x), hn x (interior_subset hx)]
  refine ⟨hneg t ⟨ht, le_rfl⟩, ?_⟩
  have hh := hm (show 0 ∈ Icc (0 : ℝ) t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩) ht
  dsimp [f] at hh
  linarith
/-- The exact finite-affine upper bound for a regular NEC optical solution. -/
theorem no_positive_optics_through_focal_bound {o : OpticalData} {L : ℝ}
    (h : SolvesOn o (Ico 0 L)) (hn : ∀ x ∈ Ico 0 L, 0 ≤ o.ricciTerm x)
    (h₀ : o.expansion 0 < 0) : L ≤ 2 / |o.expansion 0| := by
  by_contra! hh
  let t : ℝ := 2 / |o.expansion 0|
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs (x : ℝ) (hx : x ∈ Icc 0 t) : x ∈ Ico 0 L := ⟨hx.1, hx.2.trans_lt hh⟩
  obtain ⟨hneg, hrec⟩ := reciprocal_expansion_bound ht
    ⟨fun x hx => h.expansion' x (hs x hx), fun x hx => h.shear' x (hs x hx),
      fun x hx => h.radius' x (hs x hx)⟩ (fun x hx => hn x (hs x hx)) h₀
  have hzero : (o.expansion 0)⁻¹ + t / 2 = 0 := by
    dsimp [t]
    rw [abs_of_neg h₀]
    field_simp [h₀.ne]
    ring
  rw [hzero] at hrec
  exact (not_le_of_gt (inv_lt_zero'.mpr hneg)) hrec
/-- A continuous radius propagated by the optical equations while positive has a zero by the focal bound. -/
theorem radius_zero_le_focal_bound {o : OpticalData} (h₀ : o.expansion 0 < 0)
    (hr : 0 < o.radius 0) :
    let t := 2 / |o.expansion 0|
    ContinuousOn o.radius (Icc 0 t) → SolvesOn o {x ∈ Icc 0 t | 0 < o.radius x} →
    (∀ x ∈ {x ∈ Icc 0 t | 0 < o.radius x}, 0 ≤ o.ricciTerm x) →
    ∃ a ∈ Ioc 0 t, o.radius a = 0 := by
  intro t hc ho hn
  have ht : 0 ≤ t := by dsimp [t]; positivity
  by_contra! hz
  have hs (x : ℝ) (hx : x ∈ Icc 0 t) : x ∈ {x ∈ Icc 0 t | 0 < o.radius x} := by
    refine ⟨hx, ?_⟩
    by_contra! hneg
    obtain ⟨a,ha,he⟩ := intermediate_value_Icc' hx.1 (hc.mono (Icc_subset_Icc_right hx.2))
      (show 0 ∈ Icc (o.radius x) (o.radius 0) from ⟨hneg, hr.le⟩)
    exact hz a ⟨lt_of_le_of_ne ha.1 (fun e => hr.ne' (e ▸ he)),ha.2.trans hx.2⟩ he
  obtain ⟨hneg,hrec⟩ := reciprocal_expansion_bound ht
    ⟨fun x hx => ho.expansion' x (hs x hx), fun x hx => ho.shear' x (hs x hx),
      fun x hx => ho.radius' x (hs x hx)⟩ (fun x hx => hn x (hs x hx)) h₀
  have he : (o.expansion 0)⁻¹ + t/2 = 0 := by dsimp [t]; rw [abs_of_neg h₀]; field_simp [h₀.ne]; ring
  exact (not_le_of_gt (inv_lt_zero'.mpr hneg)) (he ▸ hrec)
/-- Difference between the tangent radius and the propagated radius. -/
def tangentDelay (o : OpticalData) (t : ℝ) : ℝ :=
  o.radius 0 + t * radiusSlope o 0 - o.radius t
theorem tangent_delay_nonneg {o : OpticalData} {t : ℝ} (ht : 0 ≤ t)
    (h : SolvesOn o (Icc 0 t)) (hn : ∀ x ∈ Icc 0 t, 0 ≤ o.ricciTerm x)
    (hr : ∀ x ∈ Icc 0 t, 0 ≤ o.radius x) : 0 ≤ tangentDelay o t := by
  have ha := (optical_nec_bounds h (convex_Icc _ _) hn hr).2.2.1
  have hd (x : ℝ) (hx : x ∈ Icc 0 t) :
      HasDerivAt (tangentDelay o) (radiusSlope o 0 - radiusSlope o x) x := by
    convert ((hasDerivAt_const x (o.radius 0)).add
      ((hasDerivAt_id x).mul_const (radiusSlope o 0))).sub (h.radius' x hx) using 1
    · rfl
    · simp [radiusSlope]
  have hm := antitone_of_derivs (convex_Icc (0 : ℝ) t)
    (fun x hx => (hd x hx).neg) (fun x hx => neg_nonpos.mpr
      (sub_nonneg.mpr (ha ⟨le_rfl, ht⟩ hx hx.1)))
  have hle := hm (show 0 ∈ Icc (0 : ℝ) t from ⟨le_rfl, ht⟩)
    (show t ∈ Icc (0 : ℝ) t from ⟨ht, le_rfl⟩) ht
  simpa [tangentDelay] using hle
/-- Nonzero Weyl driving at a shear zero generates nonzero shear in a deleted neighborhood. -/
theorem weyl_generates_shear {o : OpticalData} {I : Set ℝ} (h : SolvesOn o I)
    {t : ℝ} (ht : t ∈ I) (hs : o.shear t = 0) (hw : o.tideTerm t ≠ 0) :
    ∀ᶠ x in 𝓝[≠] t, o.shear x ≠ 0 ∧
      (x ∈ I → 0 ≤ o.ricciTerm x → 0 < o.radius x →
        HasDerivAt (radiusSlope o) (-focusing o x * o.radius x) x ∧
          -focusing o x * o.radius x < 0) := by
  have hd : HasDerivAt o.shear (-o.tideTerm t) t := by simpa [hs] using h.shear' t ht
  have hn := hd.tendsto_slope (isOpen_ne.mem_nhds (neg_ne_zero.mpr hw))
  filter_upwards [hn] with x hx
  have hx' : o.shear x ≠ 0 := by
    intro he
    apply hx
    simp [slope, he, hs]
  refine ⟨hx', fun hi hn hr => ⟨hasDerivAt_radiusSlope h hi, ?_⟩⟩
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos
    (div_pos (add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr hx') hn) (by norm_num))) hr
/-- A positive-radius NEC congruence supplies the nonnegative delays in the frozen clock bound. -/
theorem clock_deficit_of_optics {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (o : ι → OpticalData) (t : ι → ℝ) (ε : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (ht : ∀ i ∈ s, 0 ≤ t i)
    (ho : ∀ i ∈ s, SolvesOn (o i) (Icc 0 (t i)))
    (hn : ∀ i ∈ s, ∀ x ∈ Icc 0 (t i), 0 ≤ (o i).ricciTerm x)
    (hr : ∀ i ∈ s, ∀ x ∈ Icc 0 (t i), 0 < (o i).radius x) (hε : ε < 1) :
    let ρ := fun i => (o i).radius (t i)
    let δ := fun i => tangentDelay (o i) (t i)
    let M := ∑ i ∈ s, w i
    let A := ∑ i ∈ s, w i * ρ i ^ 2
    let C := D5.S3.Quantum.Analysis.NullConeGravity.NullConeClockAreaBound.shearDelayedClock s w ρ δ ε
    (1 - ε) * Real.sqrt (A / M) ≤ C ∧
      (C = (1 - ε) * Real.sqrt (A / M) ↔
        (∀ i ∈ s, δ i = 0) ∧ (∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j)) := by
  intro ρ δ M A C
  have hδ : ∀ i ∈ s, 0 ≤ δ i := fun i hi =>
    tangent_delay_nonneg (ht i hi) (ho i hi) (hn i hi) (fun x hx => (hr i hi x hx).le)
  obtain ⟨he, h₁, h₂, hc⟩ :=
    D5.S3.Quantum.Analysis.NullConeGravity.NullConeClockAreaBound.shear_clock_deficit_and_rigidity
      s hs w ρ δ ε hw (fun i hi => hr i hi _ ⟨ht i hi, le_rfl⟩) hδ hε
  exact ⟨by apply sub_nonneg.mp; change 0 ≤ C - (1 - ε) * Real.sqrt (A / M); linarith, hc⟩
/-- Evaluation of a covariant bilinear tensor on two vectors. -/
def evalMat (S : Matrix (Fin 4) (Fin 4) ℝ) (u v : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, S i j * u i * v j
/-- The real screen trace equals the Ricci contraction, and the complex tide is
the trace-free screen tide. The scale is the squared affine generator scale. -/
theorem screen_trace_and_tide (R : WeylNullScreen.AlgebraicCurvature4)
    (r : WeylNullScreen.FutureNullRay) (a : ℝ) :
    let T := fun Q i j => a ^ 2 * WeylNullScreen.tidal Q (WeylNullScreen.nullGenerator r)
      (WeylNullScreen.screenFrame r i) (WeylNullScreen.screenFrame r j)
    let C := (WeylNullScreen.curvature_ricci_split R).1
    let k := fun i => a * WeylNullScreen.nullGenerator r i
    let Rkk := evalMat (WeylNullScreen.ricci R) k k
    T R 0 0 + T R 1 1 = Rkk ∧
    (∀ i j, T R i j = T C.val i j + (if i = j then 1 else 0) * Rkk / 2) ∧
    (a ^ 2 : ℝ) * WeylNullScreen.complexTide C.val r =
      2 * ((T C.val 0 0 : ℂ) + Complex.I * (T C.val 0 1 : ℂ)) := by
  intro T C k Rkk
  let U := fun Q i j => WeylNullScreen.tidal Q (WeylNullScreen.nullGenerator r)
    (WeylNullScreen.screenFrame r i) (WeylNullScreen.screenFrame r j)
  let q := evalMat (WeylNullScreen.ricci R) (WeylNullScreen.nullGenerator r)
    (WeylNullScreen.nullGenerator r)
  have h₀ : U R 0 0 = U C.val 0 0 + q/2 ∧
      U R 0 0 - (U R 0 0 + U R 1 1)/2 = U C.val 0 0 := by
    have h := WeylNullScreen.null_tidal_ricci_invariance R r 0 0
    change U R 0 0 = U C.val 0 0 + (if (0 : Fin 2) = 0 then 1 else 0) * q / 2 ∧
      U R 0 0 - (if (0 : Fin 2) = 0 then 1 else 0) * (U R 0 0 + U R 1 1) / 2 =
        U C.val 0 0 at h
    simpa only [↓reduceIte, one_mul] using h
  have htrace : U R 0 0 + U R 1 1 = q := by linarith [h₀.1, h₀.2]
  have hscale : Rkk = a^2 * q := by
    dsimp [Rkk, k, q, evalMat]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨?_, fun i j => ?_, ?_⟩
  · rw [hscale]
    change a^2 * U R 0 0 + a^2 * U R 1 1 = a^2 * q
    rw [← mul_add, htrace]
  · rw [hscale]
    have hh : U R i j = U C.val i j + (if i = j then 1 else 0) * q / 2 :=
      (WeylNullScreen.null_tidal_ricci_invariance R r i j).1
    change a^2 * U R i j = a^2 * U C.val i j + (if i = j then 1 else 0) * (a^2 * q) / 2
    rw [hh]
    ring
  · dsimp [T, C]
    rw [WeylNullScreen.complexTide_weyl]
    push_cast
    ring
/-- The two independent trace-free components of the twist-free Sachs matrix equation. -/
theorem screen_riccati_components
    (θ s u θ' s' u' Rkk : ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (htrace : P 0 0 + P 1 1 = Rkk)
    (h : (!![θ'/2+s', u'; u', θ'/2-s'] : Matrix (Fin 2) (Fin 2) ℝ) =
      -(!![θ/2+s,u;u,θ/2-s] * !![θ/2+s,u;u,θ/2-s]) - P) :
    θ' = -θ^2/2 - Complex.normSq ⟨Real.sqrt 2 * s, Real.sqrt 2 * u⟩ - Rkk ∧
    (⟨Real.sqrt 2 * s', Real.sqrt 2 * u'⟩ : ℂ) =
      -(θ : ℂ) * ⟨Real.sqrt 2 * s, Real.sqrt 2 * u⟩ -
        ⟨Real.sqrt 2 * (P 0 0 - Rkk/2), Real.sqrt 2 * P 0 1⟩ := by
  have h₀ := congrFun (congrFun h 0) 0
  have h₁ := congrFun (congrFun h 1) 1
  have h₂ := congrFun (congrFun h 0) 1
  simp at h₀ h₁ h₂
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  constructor
  · simp [Complex.normSq_apply]
    nlinarith only [htrace, h₀, h₁, congrArg (fun z : ℝ => z * s^2) hsq,
      congrArg (fun z : ℝ => z * u^2) hsq]
  · have hs : s' = -θ*s - (P 0 0 - Rkk/2) := by nlinarith only [htrace, h₀, h₁]
    have hu : u' = -θ*u - P 0 1 := by nlinarith only [h₂]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hs, hu] <;> ring
def areaChange (o : OpticalData) (e : ℝ) : ℝ := area o 0 - area o (-e)
def heat (o : OpticalData) (T : ℝ → ℝ) (κ e : ℝ) : ℝ :=
  κ * ∫ x in -e..0, -x * T x * area o x
private def weightMean (q : ℝ → ℝ) (e : ℝ) : ℝ :=
  (∫ x in -e..0, -x * q x) / (e^2 / 2)
private theorem weightMean_tendsto {q : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hq : ContinuousOn q (Icc (-b) 0)) :
    Tendsto (weightMean q) (𝓝[>] (0 : ℝ)) (𝓝 (q 0)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont := (Metric.continuousWithinAt_iff.mp (hq 0 ⟨by linarith, le_rfl⟩))
    (ε/2) (by positivity)
  obtain ⟨d, hd, hclose⟩ := hcont
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (Metric.ball_mem_nhds (0 : ℝ) (lt_min hd hb))] with e he he'
  have hepos : 0 < e := he
  have hball : |e| < min d b := by simpa [Real.dist_eq] using he'
  rw [abs_of_pos hepos] at hball
  have hed : e < d := hball.trans_le (min_le_left _ _)
  have heb : e ≤ b := (hball.trans_le (min_le_right _ _)).le
  have hsub : Icc (-e) 0 ⊆ Icc (-b) 0 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hclose' (x : ℝ) (hx : x ∈ Icc (-e) 0) : |q x - q 0| < ε/2 := by
    apply hclose (hsub hx)
    rw [Real.dist_eq, sub_zero, abs_of_nonpos hx.2]
    linarith [hx.1]
  have hweight : (∫ x in -e..0, -x) = e^2/2 := by
    rw [intervalIntegral.integral_neg, integral_id]
    ring
  have hconst (c : ℝ) : (∫ x in -e..0, -x * c) = (e^2/2)*c := by
    rw [intervalIntegral.integral_mul_const, hweight]
  have hi : IntervalIntegrable (fun x => -x * q x) MeasureTheory.volume (-e) 0 :=
    (continuousOn_id.neg.mul (hq.mono hsub)).intervalIntegrable_of_Icc (by linarith)
  have hl := intervalIntegral.integral_mono_on (by linarith : -e ≤ 0)
    ((continuous_id.neg.mul continuous_const).intervalIntegrable (-e) 0) hi
    (fun x hx => mul_le_mul_of_nonneg_left (by linarith [(abs_lt.mp (hclose' x hx)).1] :
      q 0 - ε/2 ≤ q x) (neg_nonneg.mpr hx.2))
  have hu := intervalIntegral.integral_mono_on (by linarith : -e ≤ 0) hi
    ((continuous_id.neg.mul continuous_const).intervalIntegrable (-e) 0)
    (fun x hx => mul_le_mul_of_nonneg_left (by linarith [(abs_lt.mp (hclose' x hx)).2] :
      q x ≤ q 0 + ε/2) (neg_nonneg.mpr hx.2))
  change (∫ x in -e..0, -x * (q 0 - ε/2)) ≤ ∫ x in -e..0, -x * q x at hl
  change (∫ x in -e..0, -x * q x) ≤ ∫ x in -e..0, -x * (q 0 + ε/2) at hu
  rw [hconst] at hl hu
  have hpos : 0 < e^2/2 := by positivity
  rw [Real.dist_eq]
  apply abs_lt.mpr
  unfold weightMean
  constructor
  · have h := (le_div_iff₀ hpos).mpr (by linarith only [hl] :
      (q 0 - ε/2) * (e^2/2) ≤ ∫ x in -e..0, -x * q x)
    linarith
  · have h := (div_le_iff₀ hpos).mpr (by linarith only [hu] :
      (∫ x in -e..0, -x * q x) ≤ (q 0 + ε/2) * (e^2/2))
    linarith
/-- Normalized past-horizon area and heat variations converge to local curvature and flux. -/
theorem horizon_first_variation {o : OpticalData} {b : ℝ} (hb : 0 < b)
    (ho : SolvesOn o (Icc (-b) 0)) (hθ : o.expansion 0 = 0) (hσ : o.shear 0 = 0)
    (hr : 0 < o.radius 0) (T : ℝ → ℝ) (hT : ContinuousOn T (Icc (-b) 0)) (κ : ℝ) :
    Tendsto (fun e => areaChange o e / (area o 0 * e^2 / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (o.ricciTerm 0)) ∧
    Tendsto (fun e => heat o T κ e / (area o 0 * e^2 / 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (κ * T 0)) := by
  have h0 : 0 ∈ Icc (-b) (0 : ℝ) := ⟨by linarith, le_rfl⟩
  have hA : ContinuousOn (area o) (Icc (-b) 0) :=
    fun x hx => (hasDerivAt_area ho hx).continuousAt.continuousWithinAt
  have hA0 : area o 0 ≠ 0 := by unfold area; positivity
  have hθc : ContinuousOn o.expansion (Icc (-b) 0) :=
    fun x hx => (ho.expansion' x hx).continuousAt.continuousWithinAt
  have hd : ContinuousOn (dslope o.expansion 0) (Icc (-b) 0) := by
    intro x hx
    by_cases he : x = 0
    · subst x
      exact (continuousAt_dslope_same.mpr (ho.expansion' 0 h0).differentiableAt).continuousWithinAt
    · exact (continuousWithinAt_dslope_of_ne he).2 (hθc x hx)
  let q := fun x => -dslope o.expansion 0 x * area o x / area o 0
  let p := fun x => T x * area o x / area o 0
  have hq := weightMean_tendsto hb ((hd.neg.mul hA).div_const (area o 0))
  have hp := weightMean_tendsto hb ((hT.mul hA).div_const (area o 0))
  change Tendsto (weightMean q) _ (𝓝 (q 0)) at hq
  change Tendsto (weightMean p) _ (𝓝 (p 0)) at hp
  have hq0 : q 0 = o.ricciTerm 0 := by
    simp [q, (ho.expansion' 0 h0).deriv, hθ, hσ, hA0]
  have hp0 : p 0 = T 0 := by simp [p, hA0]
  rw [hq0] at hq
  rw [hp0] at hp
  have hevent : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e ∧ e ≤ b := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with e he he'
    exact ⟨he, he'.le⟩
  refine ⟨hq.congr' ?_, (tendsto_const_nhds.mul hp).congr' ?_⟩
  · filter_upwards [hevent] with e he
    have hsub : Icc (-e) 0 ⊆ Icc (-b) 0 := fun x hx => ⟨by linarith [hx.1, he.2], hx.2⟩
    have hi := (hθc.mul hA).mono hsub
    have ha := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by linarith [he.1])
      (hA.mono hsub) (fun x hx => hasDerivAt_area ho (hsub (Ioo_subset_Icc_self hx)))
      (hi.intervalIntegrable_of_Icc (by linarith [he.1]))
    have hqeq : (∫ x in -e..0, -x * q x) =
        (∫ x in -e..0, o.expansion x * area o x) / area o 0 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro x _
      have h := sub_smul_dslope o.expansion 0 x
      simp [hθ, smul_eq_mul] at h
      simp only [q]
      rw [show -x * (-dslope o.expansion 0 x * area o x / area o 0) =
          (x * dslope o.expansion 0 x) * area o x / area o 0 by ring, h]
    rw [weightMean, hqeq, ha, areaChange]
    field_simp [hA0, he.1.ne']
  · filter_upwards [hevent] with e he
    have hh : (∫ x in -e..0, -x * p x) =
        (∫ x in -e..0, -x * T x * area o x) / area o 0 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro x _
      simp only [p]
      ring
    rw [weightMean, hh, heat]
    field_simp [hA0, he.1.ne']
/-- The local Clausius identity fixes the proportionality of Ricci curvature and heat flux. -/
theorem null_identity_of_clausius {o : OpticalData} {b : ℝ} (hb : 0 < b)
    (ho : SolvesOn o (Icc (-b) 0)) (hθ : o.expansion 0 = 0) (hσ : o.shear 0 = 0)
    (hr : 0 < o.radius 0) (T : ℝ → ℝ) (hT : ContinuousOn T (Icc (-b) 0))
    (κ ℏ η : ℝ) (hκ : 0 < κ) (hℏ : 0 < ℏ) (hη : 0 < η)
    (hc : ∀ e ∈ Ioc 0 b, heat o T κ e = (ℏ * κ / (2 * Real.pi)) * η * areaChange o e) :
    o.ricciTerm 0 - (2 * Real.pi / (ℏ * η)) * T 0 = 0 := by
  obtain ⟨ha, hq⟩ := horizon_first_variation hb ho hθ hσ hr T hT κ
  have he : (fun e => heat o T κ e / (area o 0 * e^2 / 2)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun e => (ℏ * κ / (2 * Real.pi)) * η *
        (areaChange o e / (area o 0 * e^2 / 2))) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hb)] with e he he'
    rw [hc e ⟨he, he'.le⟩, mul_div_assoc]
  have hh := tendsto_nhds_unique (hq.congr' he) (tendsto_const_nhds.mul ha)
  field_simp [Real.pi_ne_zero] at hh
  field_simp [hℏ.ne', hη.ne']
  linear_combination -hh

section Einstein
open D5.S0.Certificates
open D5.S0.Certificates.MinkowskiNullConeRigidity
local notation "V" => Fin 4 → ℝ
local notation "M" => Matrix (Fin 4) (Fin 4) ℝ
private def splitVec : Space 3 ≃ₗ[ℝ] V where
  toFun v := ![v.1, v.2 0, v.2 1, v.2 2]
  invFun v := (v 0, (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm ![v 1, v 2, v 3])
  left_inv v := by
    apply Prod.ext
    · rfl
    · apply (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
      funext i
      fin_cases i <;> rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' c x := by funext i; fin_cases i <;> rfl
private theorem signature_transport (v : Space 3) :
    MinkowskiNullConeRigidity.minkowski 3 v = -WeylNullScreen.minkowski (splitVec v) (splitVec v) := by
  rcases v with ⟨t,w⟩
  have h : MinkowskiNullConeRigidity.minkowski 3 (t,w) = t^2 - ‖w‖^2 := by
    simp [MinkowskiNullConeRigidity.minkowski, QuadraticMap.sq, pow_two]
  rw [h, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [WeylNullScreen.minkowski, splitVec]
  ring
private theorem matrix_of_quadratic_eq (A B : M) (ha : Aᵀ = A) (hb : Bᵀ = B)
    (h : A.toQuadraticForm' = B.toQuadraticForm') : A = B := by
  ext i j
  have hh := congrArg (fun Q : QuadraticForm ℝ V =>
    QuadraticMap.polar Q (Pi.single i 1) (Pi.single j 1)) h
  have hA : A j i = A i j := congrFun (congrFun ha i) j
  have hB : B j i = B i j := congrFun (congrFun hb i) j
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply, Pi.single_apply, hA, hB] at hh
  linarith
/-- Null agreement in an arbitrary Lorentz frame fixes a symmetric tensor up to the metric. -/
theorem symmetric_eq_metric_of_null (S g : M) (hs : Sᵀ = S) (hg : gᵀ = g)
    (e : V ≃ₗ[ℝ] V) (he : ∀ v, g.toQuadraticForm' (e v) = WeylNullScreen.minkowski v v)
    (hn : ∀ v, g.toQuadraticForm' v = 0 → S.toQuadraticForm' v = 0) :
    ∃ f : ℝ, S = f • g := by
  let E := splitVec.trans e
  let Q := S.toQuadraticForm'.comp E.toLinearMap
  have hQ : ∀ v, MinkowskiNullConeRigidity.minkowski 3 v = 0 → Q v = 0 := by
    intro v hv
    apply hn
    change g.toQuadraticForm' (e (splitVec v)) = 0
    rw [he, signature_transport] at *
    linarith
  have hrig := eq_smul_minkowski_of_null Q hQ
  refine ⟨-Q (1,0), matrix_of_quadratic_eq S _ hs (by simp [hg]) ?_⟩
  apply QuadraticMap.ext
  intro x
  obtain ⟨v,rfl⟩ := E.surjective x
  have hv := congrArg (fun q : QuadraticForm ℝ (Space 3) => q v) hrig
  change S.toQuadraticForm' (e (splitVec v)) = Q (1,0) * MinkowskiNullConeRigidity.minkowski 3 v at hv
  rw [signature_transport] at hv
  change S.toQuadraticForm' (e (splitVec v)) = _
  rw [hv]
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply]
  have he' := he (splitVec v)
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply] at he'
  simp only [Fin.sum_univ_four] at he' ⊢
  exact Or.inl he'.symm
abbrev TensorField := V → M
def coordinateDerivative (f : V → ℝ) (x : V) (m : Fin 4) : ℝ :=
  fderiv ℝ f x (Pi.single m 1)
def tensorDivergence (gInv : TensorField) (Γ : V → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (S : TensorField) (x : V) (b : Fin 4) : ℝ :=
  ∑ m, ∑ a, gInv x m a * (coordinateDerivative (fun y => S y a b) x m -
    ∑ d, (Γ x d m a * S x d b + Γ x d m b * S x a d))
def metricTrace (gInv S : TensorField) (x : V) : ℝ :=
  ∑ m, ∑ a, gInv x m a * S x a m
def ComponentDiff (S : TensorField) (Ω : Set V) : Prop :=
  ∀ i j, DifferentiableOn ℝ (fun x => S x i j) Ω
private theorem cd_at {S : TensorField} {Ω : Set V} (h : ComponentDiff S Ω)
    (ho : IsOpen Ω) {x : V} (hx : x ∈ Ω) (i j : Fin 4) :
    DifferentiableAt ℝ (fun y => S y i j) x :=
  (h i j x hx).differentiableAt (ho.mem_nhds hx)
private theorem div_metric_mul (g gi : TensorField) (Γ : V → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (f : V → ℝ) (x : V) (b : Fin 4)
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hf : DifferentiableAt ℝ f x)
    (hi : gi x * g x = 1)
    (hcompat : ∀ m a b, coordinateDerivative (fun y => g y a b) x m =
      ∑ d, (Γ x d m a * g x d b + Γ x d m b * g x a d)) :
    tensorDivergence gi Γ (fun y => f y • g y) x b = coordinateDerivative f x b := by
  have hpart (m a : Fin 4) : coordinateDerivative (fun y => (f y • g y) a b) x m =
      coordinateDerivative f x m * g x a b + f x * coordinateDerivative (fun y => g y a b) x m := by
    simp only [Matrix.smul_apply, smul_eq_mul, coordinateDerivative, fderiv_fun_mul hf (hg a b),
      add_apply, smul_apply]
    ring
  unfold tensorDivergence
  calc
    _ = ∑ m, ∑ a, coordinateDerivative f x m * (gi x m a * g x a b) := by
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun a _ => ?_
      rw [hpart, hcompat]
      simp only [Matrix.smul_apply, smul_eq_mul]
      simp only [Fin.sum_univ_four]
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← Matrix.mul_apply, hi, Matrix.one_apply]
      simp
private theorem div_sub_const (gi : TensorField) (Γ : V → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (A B : TensorField) (c : ℝ) (x : V) (b : Fin 4)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hB : ∀ i j, DifferentiableAt ℝ (fun y => B y i j) x) :
    tensorDivergence gi Γ (fun y => A y - c • B y) x b =
      tensorDivergence gi Γ A x b - c * tensorDivergence gi Γ B x b := by
  have hp (m a : Fin 4) :
      coordinateDerivative (fun y => (A y - c • B y) a b) x m =
      coordinateDerivative (fun y => A y a b) x m -
        c * coordinateDerivative (fun y => B y a b) x m := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, coordinateDerivative]
    rw [fderiv_fun_sub (hA a b) ((hB a b).const_mul c)]
    rw [fderiv_fun_mul (differentiableAt_const c) (hB a b)]
    simp
  unfold tensorDivergence
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun a _ => ?_
  rw [hp]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Fin.sum_univ_four]
  ring
private theorem div_eq_on {Ω : Set V} (ho : IsOpen Ω) {A B : TensorField}
    (h : EqOn A B Ω) (gi : TensorField) (Γ : V → Fin 4 → Fin 4 → Fin 4 → ℝ)
    {x : V} (hx : x ∈ Ω) (b : Fin 4) :
    tensorDivergence gi Γ A x b = tensorDivergence gi Γ B x b := by
  have he (a b : Fin 4) : (fun y => A y a b) =ᶠ[𝓝 x] (fun y => B y a b) :=
    Filter.Eventually.mono (ho.mem_nhds hx) fun y hy => congrFun (congrFun (h hy) a) b
  simp only [tensorDivergence, coordinateDerivative, h hx, (he _ _).fderiv_eq]
private theorem trace_metric (g gi : TensorField) (x : V) (hi : gi x * g x = 1)
    (f : ℝ) : metricTrace gi (fun y => f • g y) x = 4 * f := by
  unfold metricTrace
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm _ f, ← Finset.mul_sum, ← Matrix.mul_apply, hi]
  simp [mul_comm]
/-- Null Clausius agreement, conservation, and the contracted Bianchi identity fix
the Einstein equation with a constant cosmological term on a connected chart. -/
theorem jacobson_einstein_on (Ω : Set V) (ho : IsOpen Ω) (hc : IsPreconnected Ω)
    (g gi R T : TensorField) (Γ : V → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (ℏ η : ℝ) (hh : 0 < ℏ) (hη : 0 < η)
    (dg : ComponentDiff g Ω) (dgi : ComponentDiff gi Ω)
    (dR : ComponentDiff R Ω) (dT : ComponentDiff T Ω)
    (hmetric : ∀ x ∈ Ω, (g x)ᵀ = g x ∧ gi x * g x = 1 ∧
      ∃ e : V ≃ₗ[ℝ] V, ∀ v, (g x).toQuadraticForm' (e v) =
        WeylNullScreen.minkowski v v)
    (hsym : ∀ x ∈ Ω, (R x)ᵀ = R x ∧ (T x)ᵀ = T x)
    (hclausius : ∀ x ∈ Ω, ∀ v : V, v ≠ 0 → (g x).toQuadraticForm' v = 0 →
      ∃ (o : OpticalData) (b κ : ℝ) (flux : ℝ → ℝ),
        0 < b ∧ 0 < κ ∧ SolvesOn o (Icc (-b) 0) ∧
        o.expansion 0 = 0 ∧ o.shear 0 = 0 ∧ 0 < o.radius 0 ∧
        ContinuousOn flux (Icc (-b) 0) ∧
        o.ricciTerm 0 = (R x).toQuadraticForm' v ∧ flux 0 = (T x).toQuadraticForm' v ∧
        ∀ e ∈ Ioc 0 b, heat o flux κ e = (ℏ * κ / (2 * Real.pi)) * η * areaChange o e)
    (hcompat : ∀ x ∈ Ω, ∀ m a b, coordinateDerivative (fun y => g y a b) x m =
      ∑ d, (Γ x d m a * g x d b + Γ x d m b * g x a d))
    (hBianchi : ∀ x ∈ Ω, ∀ b,
      tensorDivergence gi Γ (fun y => R y - (metricTrace gi R y / 2) • g y) x b = 0)
    (hconserve : ∀ x ∈ Ω, ∀ b, tensorDivergence gi Γ T x b = 0) :
    ∃ Λ : ℝ, ∀ x ∈ Ω,
      R x - (metricTrace gi R x / 2) • g x + Λ • g x =
        (8 * Real.pi * (1 / (4 * ℏ * η))) • T x := by
  let c := 2 * Real.pi / (ℏ * η)
  let S : TensorField := fun x => R x - c • T x
  let f : V → ℝ := fun x => metricTrace gi S x / 4
  let r : V → ℝ := fun x => metricTrace gi R x / 2
  have dS : ComponentDiff S Ω := fun i j => (dR i j).sub ((dT i j).const_mul c)
  have traceDiff (A : TensorField) (dA : ComponentDiff A Ω) :
      DifferentiableOn ℝ (metricTrace gi A) Ω := by
    unfold metricTrace
    exact DifferentiableOn.fun_sum fun m _ => DifferentiableOn.fun_sum
      fun a _ => (dgi m a).mul (dA a m)
  have df : DifferentiableOn ℝ f Ω := by
    simpa only [f, div_eq_mul_inv] using (traceDiff S dS).mul_const ((4 : ℝ)⁻¹)
  have dr : DifferentiableOn ℝ r Ω := by
    simpa only [r, div_eq_mul_inv] using (traceDiff R dR).mul_const ((2 : ℝ)⁻¹)
  have hnull (x : V) (hx : x ∈ Ω) (v : V) (hv : (g x).toQuadraticForm' v = 0) :
      (S x).toQuadraticForm' v = 0 := by
    by_cases hz : v = 0
    · simp [hz]
    obtain ⟨o,b,κ,flux,hb,hκ,ho',hθ,hσ,hr,hT,hR0,hT0,hcl⟩ := hclausius x hx v hz hv
    have h := null_identity_of_clausius hb ho' hθ hσ hr flux hT κ ℏ η hκ hh hη hcl
    rw [hR0, hT0] at h
    simp only [S, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, smul_eq_mul, Matrix.sub_apply, Matrix.smul_apply] at h ⊢
    simp only [Fin.sum_univ_four] at h ⊢
    linear_combination h
  have hS : EqOn S (fun x => f x • g x) Ω := by
    intro x hx
    obtain ⟨hgs, hi, e, he⟩ := hmetric x hx
    obtain ⟨hRs,hTs⟩ := hsym x hx
    obtain ⟨a, ha⟩ := symmetric_eq_metric_of_null (S x) (g x)
      (by simp [S,hRs,hTs]) hgs e he (hnull x hx)
    have ht := trace_metric g gi x hi a
    have heq : metricTrace gi S x = 4 * a := by
      simpa [metricTrace, ha] using ht
    have hfa : f x = a := by dsimp [f]; linarith
    change S x = f x • g x
    rw [hfa]
    exact ha
  have dconst : Ω.EqOn (fderiv ℝ (fun x => f x - r x)) 0 := by
    intro x hx
    have hfa := (df x hx).differentiableAt (ho.mem_nhds hx)
    have hra := (dr x hx).differentiableAt (ho.mem_nhds hx)
    have drv : ∀ b, coordinateDerivative f x b = coordinateDerivative r x b := by
      intro b
      have hdA := div_eq_on ho hS gi Γ hx b
      have hm := div_metric_mul g gi Γ f x b (cd_at dg ho hx)
        hfa (hmetric x hx).2.1 (hcompat x hx)
      have hdS := div_sub_const gi Γ R T c x b (cd_at dR ho hx) (cd_at dT ho hx)
      have hdB := div_sub_const gi Γ R (fun y => r y • g y) 1 x b
        (cd_at dR ho hx) (fun i j => hra.mul (cd_at dg ho hx i j))
      have hmB := div_metric_mul g gi Γ r x b (cd_at dg ho hx)
        hra (hmetric x hx).2.1 (hcompat x hx)
      change tensorDivergence gi Γ S x b = _ at hdS
      rw [hm, hdS, hconserve x hx b, mul_zero, sub_zero] at hdA
      simp only [one_smul, one_mul] at hdB
      change tensorDivergence gi Γ (fun y => R y - (metricTrace gi R y / 2) • g y) x b = _ at hdB
      rw [hBianchi x hx b, hmB] at hdB
      linarith
    rw [fderiv_fun_sub hfa hra]
    ext v
    have hbas : v = ∑ i : Fin 4, v i • Pi.single i (1 : ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hbas, map_sum]
    simp only [map_smul, smul_eq_mul, sub_apply]
    exact Finset.sum_eq_zero fun i _ => by
      have h := drv i
      unfold coordinateDerivative at h
      rw [h, sub_self, mul_zero]
  obtain ⟨k, hk⟩ := ho.exists_is_const_of_fderiv_eq_zero hc (df.sub dr) dconst
  refine ⟨-k, fun x hx => ?_⟩
  have hs := hS hx
  have hcoef : c = 8 * Real.pi * (1 / (4 * ℏ * η)) := by
    dsimp [c]
    field_simp [hh.ne', hη.ne']; ring
  change R x - c • T x = f x • g x at hs
  have hfr : f x - r x = k := hk x hx
  change R x - r x • g x + (-k) • g x = _
  rw [← hcoef]
  have he : f x = r x + k := by linarith
  rw [he, add_smul] at hs
  rw [(sub_eq_iff_eq_add).mp hs, neg_smul]
  abel

end Einstein
end D5.S3.Geometry.Lorentz.SachsJacobsonEinstein4D
