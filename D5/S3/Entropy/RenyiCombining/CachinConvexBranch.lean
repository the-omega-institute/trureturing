/- GID: D5/S3/Entropy/RenyiCombining/CachinConvexBranch
   generality: G
   mirror-B: D5/B/S3/Entropy/RenyiCombining/CachinConvexBranch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Riccati curvature certificate for the convex Renyi combining branch. -/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! The declarations concern differential inequalities for arbitrary real functions,
not finite calculations or certified numerical instances. -/

open Set Filter
open scoped Topology

namespace D5.S3.Entropy.RenyiCombining.CachinConvexBranch

/-- A negative curvature cannot cross zero when its derivative is negative at every
possible first crossing. The companion first derivative is kept negative by integration. -/
theorem curvature_neg_of_first_zero (g f f' : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hg : ContinuousOn g (Icc 0 a)) (hf : ContinuousOn f (Icc 0 a))
    (hg' : ∀ z ∈ Ioo 0 a, HasDerivAt g (f z) z)
    (hf' : ∀ z ∈ Ioc 0 a, HasDerivAt f (f' z) z)
    (hg0 : g 0 < 0) (hf0 : f 0 < 0)
    (hbarrier : ∀ z ∈ Ioc 0 a, f z = 0 → g z < 0 → f' z < 0) :
    ∀ z ∈ Icc 0 a, f z < 0 := by
  intro z hz
  by_contra hn
  have hzn : 0 ≤ f z := le_of_not_gt hn
  let S : Set ℝ := {x ∈ Icc 0 a | 0 ≤ f x}
  have hSclosed : IsClosed S := isClosed_Icc.isClosed_le continuousOn_const hf
  have hScompact : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed (by
    intro x hx; exact hx.1)
  obtain ⟨b, hbS, hbmin⟩ := hScompact.exists_isLeast ⟨z, hz, hzn⟩
  have hb0 : 0 < b := by
    have hb : 0 ≤ b := hbS.1.1
    by_contra h
    have : b = 0 := le_antisymm (le_of_not_gt h) hb
    subst b
    exact (not_le_of_gt hf0) hbS.2
  have hba : b ≤ a := hbS.1.2
  have hbefore : ∀ x ∈ Ico 0 b, f x < 0 := by
    intro x hx
    by_contra hxneg
    have hxS : x ∈ S := ⟨⟨hx.1, hx.2.le.trans hba⟩, le_of_not_gt hxneg⟩
    exact (not_le_of_gt hx.2) (hbmin hxS)
  have hfb : f b = 0 := by
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hb0.le
      (hf.mono (Icc_subset_Icc le_rfl hba)) ⟨hf0.le, hbS.2⟩
    have hcS : c ∈ S := ⟨⟨hc.1, hc.2.trans hba⟩, by rw [hfc]⟩
    have : c = b := le_antisymm hc.2 (hbmin hcS)
    simpa [this] using hfc
  have hfm : ∀ x ∈ Icc 0 b, f x ≤ 0 := by
    intro x hx
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · exact (hbefore x ⟨hx.1, hlt⟩).le
    · exact hfb.le
  have hgm : AntitoneOn g (Icc 0 b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (hg.mono (Icc_subset_Icc le_rfl hba))
      (fun x hx => (hg' x (by
        have hxi : x ∈ Ioo 0 b := by simpa using hx
        exact ⟨hxi.1, hxi.2.trans_le hba⟩)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hxi : x ∈ Ioo 0 b := by simpa using hx
        rw [(hg' x ⟨hxi.1, hxi.2.trans_le hba⟩).deriv]
        exact hfm x ⟨hxi.1.le, hxi.2.le⟩)
  have hgb : g b < 0 := (hgm ⟨le_rfl, hb0.le⟩ ⟨hb0.le, le_rfl⟩ hb0.le).trans_lt hg0
  have hfb' : f' b < 0 := hbarrier b ⟨hb0, hba⟩ hfb hgb
  have hnonneg : 0 ≤ f' b := by
    apply ge_of_tendsto ((hasDerivAt_iff_tendsto_slope_left_right.mp
      (hf' b ⟨hb0, hba⟩)).1)
    have hlow : ∀ᶠ x in 𝓝[<] b, 0 < x :=
      (eventually_gt_nhds hb0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hlow, self_mem_nhdsWithin] with x hx0 hxb
    rw [slope_def_field, hfb, sub_zero]
    exact div_nonneg_iff.mpr (Or.inr ⟨(hbefore x ⟨hx0.le, hxb⟩).le,
      sub_nonpos.mpr hxb.le⟩)
  exact (not_le_of_gt hfb') hnonneg

/-- Logarithmic inverse hyperbolic tangent, in natural-log units. -/
noncomputable def artanh (t : ℝ) : ℝ := (Real.log (1 + t) - Real.log (1 - t)) / 2

/-- The auxiliary quotient, with both removable singularities filled explicitly. -/
noncomputable def C (n z : ℝ) : ℝ :=
  if z = 0 then 1 else
    if n = 0 then Real.sqrt z / artanh (Real.sqrt z)
    else n * Real.sqrt z * Real.cosh (n * artanh (Real.sqrt z)) /
      Real.sinh (n * artanh (Real.sqrt z))

noncomputable def D (n z : ℝ) : ℝ := C n z + n * z

/-- Elasticity in the squared-bias coordinate. -/
noncomputable def elasticity (D D₁ : ℝ → ℝ) (z : ℝ) : ℝ := 1 - 2 * z * D₁ z / D z

/-- The rational witness gives a strict negative initial slope uniformly over the
entire parameter interval needed by the conjecture. -/
theorem initial_slope_bound (n : ℝ) (hn : -1 < n) (hn' : n ≤ 1 / 4) :
    (n ^ 2 + 3 * n - 1) / 3 ≤ -(1 / 16 : ℝ) := by
  have hprod : 0 ≤ (1 / 4 - n) * (n + 13 / 4) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The logarithmic derivative of the denominator gives a strictly increasing
elasticity whenever its first two derivatives are negative. -/
theorem elasticity_hasDerivAt (D D₁ D₂ : ℝ → ℝ) (z : ℝ) (hD : D z ≠ 0)
    (hd : HasDerivAt D (D₁ z) z) (hd₁ : HasDerivAt D₁ (D₂ z) z) :
    HasDerivAt (elasticity D D₁)
      (-2 * D₁ z / D z - 2 * z * D₂ z / D z +
        2 * z * (D₁ z) ^ 2 / (D z) ^ 2) z := by
  convert (hasDerivAt_const z 1).sub
    ((((hasDerivAt_id z).const_mul 2).mul hd₁).div hd hD) using 1
  · rfl
  · dsimp
    field_simp
    <;> ring

theorem elasticity_strictMonoOn (D D₁ D₂ : ℝ → ℝ) (a b : ℝ)
    (hpos : ∀ z ∈ Ioo a b, 0 < z ∧ 0 < D z)
    (hd : ∀ z ∈ Ioo a b, HasDerivAt D (D₁ z) z)
    (hd₁ : ∀ z ∈ Ioo a b, HasDerivAt D₁ (D₂ z) z)
    (hneg₁ : ∀ z ∈ Ioo a b, D₁ z < 0)
    (hneg₂ : ∀ z ∈ Ioo a b, D₂ z < 0) :
    StrictMonoOn (elasticity D D₁) (Ioo a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun z hz => (elasticity_hasDerivAt D D₁ D₂ z (hpos z hz).2.ne'
      (hd z hz) (hd₁ z hz)).continuousAt.continuousWithinAt)
  intro z hz
  have hz' : z ∈ Ioo a b := by simpa using hz
  have hp := hpos z hz'
  rw [(elasticity_hasDerivAt D D₁ D₂ z hp.2.ne' (hd z hz') (hd₁ z hz')).deriv]
  have h₁ : 0 < -2 * D₁ z / D z :=
    div_pos (mul_pos_of_neg_of_neg (by norm_num) (hneg₁ z hz')) hp.2
  have h₂ : 0 < -(2 * z * D₂ z) / D z :=
    div_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (mul_pos (by norm_num) hp.1) (hneg₂ z hz'))) hp.2
  have h₃ : 0 ≤ 2 * z * (D₁ z) ^ 2 / (D z) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hp.1.le) (sq_nonneg _)) (sq_nonneg _)
  have h₂' : 0 < -2 * z * D₂ z / D z := by convert h₂ using 1 <;> ring
  have hres := add_pos_of_pos_of_nonneg (add_pos h₁ h₂') h₃
  convert hres using 1 <;> ring

theorem artanh_pos (t : ℝ) (ht : t ∈ Ioo 0 1) : 0 < artanh t := by
  have hp : 0 < Real.log (1 + t) := Real.log_pos (by linarith [ht.1])
  have hm : Real.log (1 - t) < 0 := Real.log_neg (by linarith [ht.2]) (by linarith [ht.1])
  unfold artanh
  linarith

theorem artanh_hasDerivAt (t : ℝ) (ht : t ∈ Ioo 0 1) :
    HasDerivAt artanh (1 / (1 - t ^ 2)) t := by
  have hp : 1 + t ≠ 0 := by linarith [ht.1]
  have hm : 1 - t ≠ 0 := by linarith [ht.2]
  have h1t : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2]
  convert ((((hasDerivAt_const t 1).add (hasDerivAt_id t)).log hp).sub
    (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log hm)).div_const 2 using 1
  · rfl
  · dsimp
    field_simp [hp, hm, h1t]
    <;> ring

theorem C_pos (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) : 0 < C n z := by
  have ht : Real.sqrt z ∈ Ioo 0 1 := ⟨Real.sqrt_pos.mpr hz.1,
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have hu := artanh_pos _ ht
  simp only [C, if_neg hz.1.ne', if_neg hn.ne']
  exact div_pos (mul_pos (mul_pos hn ht.1) (Real.cosh_pos _))
    (Real.sinh_pos_iff.mpr (mul_pos hn hu))

theorem D_pos (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) : 0 < D n z := by
  exact add_pos (C_pos n z hn hz) (mul_pos hn hz.1)

/-- The explicit hyperbolic quotient satisfies the Riccati equation in the open interval. -/
theorem C_hasDerivAt (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    HasDerivAt (C n)
      (((1 - z) * C n z - (C n z) ^ 2 + n ^ 2 * z) / (2 * z * (1 - z))) z := by
  let t := Real.sqrt z
  have ht : t ∈ Ioo 0 1 := ⟨Real.sqrt_pos.mpr hz.1,
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have htz : t ^ 2 = z := Real.sq_sqrt hz.1.le
  have htne : t ≠ 0 := ht.1.ne'
  have h1t : 1 - t ^ 2 ≠ 0 := by rw [htz]; linarith [hz.2]
  have hs : Real.sinh (n * artanh t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hn (artanh_pos t ht))).ne'
  have hd := Real.hasDerivAt_sqrt hz.1.ne'
  have hu := (artanh_hasDerivAt t ht).comp z hd
  have hnu := hu.const_mul n
  have hraw := (((hd.const_mul n).mul hnu.cosh).div hnu.sinh hs)
  have heq : C n =ᶠ[𝓝 z] (fun x => n * Real.sqrt x *
      Real.cosh (n * artanh (Real.sqrt x)) / Real.sinh (n * artanh (Real.sqrt x))) := by
    filter_upwards [eventually_ne_nhds hz.1.ne'] with x hx
    simp only [C, if_neg hx, if_neg hn.ne']
  apply (hraw.congr_of_eventuallyEq heq).congr_deriv
  simp only [C, if_neg hz.1.ne', if_neg hn.ne']
  change ((n * (1 / (2 * t)) * Real.cosh (n * artanh t) + n * t *
      (Real.sinh (n * artanh t) * (n * (1 / (1 - t ^ 2) * (1 / (2 * t)))))) *
      Real.sinh (n * artanh t) - n * t * Real.cosh (n * artanh t) *
      (Real.cosh (n * artanh t) * (n * (1 / (1 - t ^ 2) * (1 / (2 * t)))))) /
      Real.sinh (n * artanh t) ^ 2 = _
  have hh : Real.cosh (n * artanh t) ^ 2 = 1 + Real.sinh (n * artanh t) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (n * artanh t)]
  change _ = ((1 - z) * (n * t * Real.cosh (n * artanh t) / Real.sinh (n * artanh t)) -
      (n * t * Real.cosh (n * artanh t) / Real.sinh (n * artanh t)) ^ 2 + n ^ 2 * z) /
      (2 * z * (1 - z))
  rw [← htz]
  field_simp [htne, hs, h1t]
  nlinarith [hh]

/-- Translation of the first-crossing argument to any nonsingular initial point. -/
theorem curvature_neg_of_first_zero_from (g f f' : ℝ → ℝ) (l a : ℝ) (hla : l < a)
    (hg : ContinuousOn g (Icc l a)) (hf : ContinuousOn f (Icc l a))
    (hg' : ∀ z ∈ Ioo l a, HasDerivAt g (f z) z)
    (hf' : ∀ z ∈ Ioc l a, HasDerivAt f (f' z) z)
    (hgl : g l < 0) (hfl : f l < 0)
    (hbarrier : ∀ z ∈ Ioc l a, f z = 0 → g z < 0 → f' z < 0) :
    ∀ z ∈ Icc l a, f z < 0 := by
  have hmap : MapsTo (fun x => l + x) (Icc 0 (a - l)) (Icc l a) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have htranslate := curvature_neg_of_first_zero
    (fun x => g (l + x)) (fun x => f (l + x)) (fun x => f' (l + x)) (a - l)
    (sub_pos.mpr hla)
    (hg.comp (continuous_const.add continuous_id).continuousOn hmap)
    (hf.comp (continuous_const.add continuous_id).continuousOn hmap)
    (fun x hx => by
      have hd := (hg' (l + x) (by constructor <;> linarith [hx.1, hx.2])).comp x
        ((hasDerivAt_const x l).add (hasDerivAt_id x))
      convert hd using 1 <;> (try ext w) <;> (try dsimp) <;> ring)
    (fun x hx => by
      have hd := (hf' (l + x) (by constructor <;> linarith [hx.1, hx.2])).comp x
        ((hasDerivAt_const x l).add (hasDerivAt_id x))
      convert hd using 1 <;> (try ext w) <;> (try dsimp) <;> ring)
    (by simpa using hgl) (by simpa using hfl)
    (fun x hx => hbarrier (l + x) (by constructor <;> linarith [hx.1, hx.2]))
  intro z hz
  have := htranslate (z - l) (by constructor <;> linarith [hz.1, hz.2])
  simpa using this

/-- Only a punctured right-neighborhood of the singular endpoint needs initial
curvature information; no differentiability at zero is assumed. -/
theorem riccati_curvature_neg_of_local (C C₁ C₂ C₃ : ℝ → ℝ)
    (hc₁ : ContinuousOn C₁ (Ioo 0 1)) (hc₂ : ContinuousOn C₂ (Ioo 0 1))
    (hd₁ : ∀ z ∈ Ioo 0 1, HasDerivAt C₁ (C₂ z) z)
    (hd₂ : ∀ z ∈ Ioo 0 1, HasDerivAt C₂ (C₃ z) z)
    (hlocal : ∃ ε > 0, ∀ z ∈ Ioo 0 ε, C₁ z < 0 ∧ C₂ z < 0)
    (hode : ∀ z ∈ Ioo 0 1,
      2 * z * (1 - z) * C₃ z = (-3 + 7 * z - 2 * C z) * C₂ z +
        2 * C₁ z * (1 - C₁ z)) :
    ∀ z ∈ Ioo 0 1, C₂ z < 0 := by
  obtain ⟨ε, hε, hlocal⟩ := hlocal
  intro z hz
  let l := min (z / 2) (ε / 2)
  have hl : 0 < l := lt_min (by linarith [hz.1]) (by linarith)
  have hlz : l < z := (min_le_left _ _).trans_lt (by linarith [hz.1])
  have hlε : l < ε := (min_le_right _ _).trans_lt (by linarith)
  have hsub : Icc l z ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hl.trans_le hx.1, hx.2.trans_lt hz.2⟩
  have hneg := curvature_neg_of_first_zero_from C₁ C₂ C₃ l z hlz
    (hc₁.mono hsub) (hc₂.mono hsub)
    (fun x hx => hd₁ x (hsub ⟨hx.1.le, hx.2.le⟩))
    (fun x hx => hd₂ x (hsub ⟨hx.1.le, hx.2⟩))
    (hlocal l ⟨hl, hlε⟩).1 (hlocal l ⟨hl, hlε⟩).2
    (by
      intro x hx hzero hfirst
      have hx' := hsub ⟨hx.1.le, hx.2⟩
      have hcoef : 0 < 2 * x * (1 - x) :=
        mul_pos (mul_pos (by norm_num) hx'.1) (by linarith [hx'.2])
      have hright : 2 * C₁ x * (1 - C₁ x) < 0 :=
        mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hfirst) (by linarith)
      have heq := hode x hx'
      rw [hzero, mul_zero, zero_add] at heq
      have hh : 2 * x * (1 - x) * C₃ x < 0 := heq.trans_lt hright
      by_contra h
      exact (not_lt_of_ge (mul_nonneg hcoef.le (le_of_not_gt h))) hh)
  exact hneg z ⟨hlz.le, le_rfl⟩

/-- Differentiating the Riccati equation once, with all hypotheses confined to the
open interval where its coefficients are nonsingular. -/
theorem riccati_differentiate (C C₁ C₂ : ℝ → ℝ) (n z : ℝ) (hz : z ∈ Ioo 0 1)
    (hd : HasDerivAt C (C₁ z) z) (hd₁ : HasDerivAt C₁ (C₂ z) z)
    (hR : ∀ w ∈ Ioo 0 1,
      2 * w * (1 - w) * C₁ w = (1 - w) * C w - (C w) ^ 2 + n ^ 2 * w) :
    2 * z * (1 - z) * C₂ z = (-1 + 3 * z - 2 * C z) * C₁ z - C z + n ^ 2 := by
  have hL : HasDerivAt (fun w => 2 * w * (1 - w) * C₁ w)
      ((2 - 4 * z) * C₁ z + 2 * z * (1 - z) * C₂ z) z := by
    convert ((((hasDerivAt_id z).const_mul 2).mul
      ((hasDerivAt_const z 1).sub (hasDerivAt_id z))).mul hd₁) using 1 <;> (try ext w) <;> (try dsimp) <;> ring
  have hRight : HasDerivAt (fun w => (1 - w) * C w - (C w) ^ 2 + n ^ 2 * w)
      (-C z + (1 - z) * C₁ z - 2 * C z * C₁ z + n ^ 2) z := by
    convert ((((hasDerivAt_const z 1).sub (hasDerivAt_id z)).mul hd).sub
      (hd.pow 2)).add ((hasDerivAt_id z).const_mul (n ^ 2)) using 1 <;> (try ext w) <;> (try dsimp) <;> ring
  have heq : (fun w => 2 * w * (1 - w) * C₁ w) =ᶠ[𝓝 z]
      (fun w => (1 - w) * C w - (C w) ^ 2 + n ^ 2 * w) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact hR w hw
  have he := hL.unique (hRight.congr_of_eventuallyEq heq)
  linear_combination he

/-- A second differentiation yields the sign-preserving curvature equation used
by the first-zero argument. -/
theorem riccati_differentiate_twice (C C₁ C₂ C₃ : ℝ → ℝ) (n z : ℝ)
    (hz : z ∈ Ioo 0 1) (hd : HasDerivAt C (C₁ z) z)
    (hd₁ : HasDerivAt C₁ (C₂ z) z) (hd₂ : HasDerivAt C₂ (C₃ z) z)
    (hR : ∀ w ∈ Ioo 0 1,
      2 * w * (1 - w) * C₂ w = (-1 + 3 * w - 2 * C w) * C₁ w - C w + n ^ 2) :
    2 * z * (1 - z) * C₃ z = (-3 + 7 * z - 2 * C z) * C₂ z +
      2 * C₁ z * (1 - C₁ z) := by
  have hL : HasDerivAt (fun w => 2 * w * (1 - w) * C₂ w)
      ((2 - 4 * z) * C₂ z + 2 * z * (1 - z) * C₃ z) z := by
    convert ((((hasDerivAt_id z).const_mul 2).mul
      ((hasDerivAt_const z 1).sub (hasDerivAt_id z))).mul hd₂) using 1 <;> (try ext w) <;> (try dsimp) <;> ring
  have hRight : HasDerivAt
      (fun w => (-1 + 3 * w - 2 * C w) * C₁ w - C w + n ^ 2)
      ((3 - 2 * C₁ z) * C₁ z + (-1 + 3 * z - 2 * C z) * C₂ z - C₁ z) z := by
    convert (((((hasDerivAt_const z (-1)).add ((hasDerivAt_id z).const_mul 3)).sub
      (hd.const_mul 2)).mul hd₁).sub hd).add (hasDerivAt_const z (n ^ 2)) using 1 <;>
      (try ext w) <;> (try dsimp) <;> ring
  have heq : (fun w => 2 * w * (1 - w) * C₂ w) =ᶠ[𝓝 z]
      (fun w => (-1 + 3 * w - 2 * C w) * C₁ w - C w + n ^ 2) := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
    exact hR w hw
  have he := hL.unique (hRight.congr_of_eventuallyEq heq)
  linear_combination he

/-- Conversion between the hyperbolic and real-power forms of the same quotient. -/
theorem cosh_div_sinh_eq_rpow (n t : ℝ) (hn : 0 < n) (ht : t ∈ Ioo 0 1) :
    Real.cosh (n * artanh t) / Real.sinh (n * artanh t) =
      ((1 + t) ^ n + (1 - t) ^ n) / ((1 + t) ^ n - (1 - t) ^ n) := by
  have hp : 0 < 1 + t := by linarith [ht.1]
  have hm : 0 < 1 - t := by linarith [ht.2]
  have he : Real.exp (n * artanh t) * Real.exp (n * artanh t) =
      (1 + t) ^ n / (1 - t) ^ n := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hm, ← Real.exp_sub]
    congr 1
    unfold artanh
    ring
  have hminus : Real.exp (-(n * artanh t)) = (Real.exp (n * artanh t))⁻¹ :=
    Real.exp_neg _
  have hE : Real.exp (n * artanh t) ≠ 0 := (Real.exp_pos _).ne'
  have hQ : (1 - t) ^ n ≠ 0 := (Real.rpow_pos_of_pos hm n).ne'
  rw [Real.cosh_eq, Real.sinh_eq, hminus]
  apply (div_eq_div_iff (by
    rw [← hminus, ← Real.sinh_eq]
    exact (Real.sinh_pos_iff.mpr (mul_pos hn (artanh_pos t ht))).ne')
    (by
      have : (1 - t) ^ n < (1 + t) ^ n :=
        Real.rpow_lt_rpow hm.le (by linarith [ht.1]) hn
      linarith)).mpr
  have he' : Real.exp (n * artanh t) ^ 2 * (1 - t) ^ n = (1 + t) ^ n := by
    calc
      _ = (Real.exp (n * artanh t) * Real.exp (n * artanh t)) * (1 - t) ^ n := by ring
      _ = _ := by rw [he]; field_simp
  field_simp [hE]
  nlinarith [he']

theorem C_eq_power_quotient (n t : ℝ) (hn : 0 < n) (ht : t ∈ Ioo 0 1) :
    C n (t ^ 2) = n * t * ((1 + t) ^ n + (1 - t) ^ n) /
      ((1 + t) ^ n - (1 - t) ^ n) := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht.1.ne'
  simp only [C, if_neg ht2, if_neg hn.ne', Real.sqrt_sq ht.1.le]
  calc
    _ = n * t * (Real.cosh (n * artanh t) / Real.sinh (n * artanh t)) := by ring
    _ = _ := by rw [cosh_div_sinh_eq_rpow n t hn ht]; ring

theorem artanh_contDiffAt {m : WithTop ℕ∞} (t : ℝ) (ht : t ∈ Ioo 0 1) :
    ContDiffAt ℝ m artanh t := by
  unfold artanh
  exact (((contDiffAt_const.add contDiffAt_id).log (by dsimp; linarith [ht.1])).sub
    ((contDiffAt_const.sub contDiffAt_id).log (by dsimp; linarith [ht.2]))).div_const 2

theorem C_contDiffAt {m : WithTop ℕ∞} (n z : ℝ) (hn : 0 < n) (hz : z ∈ Ioo 0 1) :
    ContDiffAt ℝ m (C n) z := by
  have ht : Real.sqrt z ∈ Ioo 0 1 := ⟨Real.sqrt_pos.mpr hz.1,
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hz.2)⟩
  have hs : Real.sinh (n * artanh (Real.sqrt z)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hn (artanh_pos _ ht))).ne'
  have hsqrt : ContDiffAt ℝ m (fun x : ℝ => Real.sqrt x) z := Real.contDiffAt_sqrt hz.1.ne'
  have hnconst : ContDiffAt ℝ m (fun _ : ℝ => n) z := contDiffAt_const
  have harg := hnconst.mul ((artanh_contDiffAt (m := m) _ ht).comp z hsqrt)
  have hraw := ((hnconst.mul hsqrt).mul harg.cosh).div harg.sinh hs
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz.1.ne'] with x hx
  simp only [C, if_neg hx, if_neg hn.ne']
  rfl

/-- The actual hyperbolic quotient satisfies the curvature equation, rather than
merely assuming that equation as a certificate input. -/
theorem C_curvature_equation (n : ℝ) (hn : 0 < n) (z : ℝ) (hz : z ∈ Ioo 0 1) :
    2 * z * (1 - z) * deriv (deriv (deriv (C n))) z =
      (-3 + 7 * z - 2 * C n z) * deriv (deriv (C n)) z +
        2 * deriv (C n) z * (1 - deriv (C n) z) := by
  have hC : ContDiffOn ℝ 3 (C n) (Ioo 0 1) := fun x hx =>
    (C_contDiffAt (m := 3) n x hn hx).contDiffWithinAt
  have hC₁ : ContDiffOn ℝ 2 (deriv (C n)) (Ioo 0 1) :=
    hC.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hC₂ : ContDiffOn ℝ 1 (deriv (deriv (C n))) (Ioo 0 1) :=
    hC₁.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hd : ∀ w ∈ Ioo 0 1, HasDerivAt (C n) (deriv (C n) w) w := by
    intro w hw
    exact ((C_hasDerivAt n w hn hw).differentiableAt).hasDerivAt
  have hd₁ : ∀ w ∈ Ioo 0 1,
      HasDerivAt (deriv (C n)) (deriv (deriv (C n)) w) w := by
    intro w hw
    exact ((hC₁.differentiableOn (by simp)) w hw).differentiableAt
      (Ioo_mem_nhds hw.1 hw.2) |>.hasDerivAt
  have hd₂ : ∀ w ∈ Ioo 0 1,
      HasDerivAt (deriv (deriv (C n))) (deriv (deriv (deriv (C n))) w) w := by
    intro w hw
    exact ((hC₂.differentiableOn (by simp)) w hw).differentiableAt
      (Ioo_mem_nhds hw.1 hw.2) |>.hasDerivAt
  have hR : ∀ w ∈ Ioo 0 1,
      2 * w * (1 - w) * deriv (C n) w =
        (1 - w) * C n w - (C n w) ^ 2 + n ^ 2 * w := by
    intro w hw
    have hden : 2 * w * (1 - w) ≠ 0 := ne_of_gt
      (mul_pos (mul_pos (by norm_num) hw.1) (by linarith [hw.2]))
    rw [(C_hasDerivAt n w hn hw).deriv]
    field_simp [hw.1.ne', sub_ne_zero.mpr hw.2.ne']
  apply riccati_differentiate_twice (C n) (deriv (C n)) (deriv (deriv (C n)))
    (deriv (deriv (deriv (C n)))) n z hz (hd z hz) (hd₁ z hz) (hd₂ z hz)
  intro w hw
  exact riccati_differentiate (C n) (deriv (C n)) (deriv (deriv (C n))) n w hw
    (hd w hw) (hd₁ w hw) hR

end D5.S3.Entropy.RenyiCombining.CachinConvexBranch
