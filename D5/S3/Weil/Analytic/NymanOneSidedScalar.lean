/- GID: D5/S3/Weil/Analytic/NymanOneSidedScalar
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanOneSidedScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-sided Landau continuation for compact Lipschitz Möbius shells. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Weil.Analytic.NymanShellMellin
import D5.S3.Weil.Analytic.NymanShellScale
import D5.S3.Analytic.Laplace.PositiveLaplaceContinuation
import D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-! One-sided Landau continuation for compact Lipschitz Möbius shells. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory Complex Finset ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open D5.S3.Analytic.Laplace
open NymanShellMellin NymanShellScale
open private continuousOn_scaled zero_top W_differentiableAt from D5.S3.Weil.Analytic.NymanShellMellin
open private scaled_finite from D5.S3.Weil.Analytic.NymanShellScale

namespace NymanOneSidedScalar

/-- The complex-valued kernel associated to a real shell kernel. -/
def Wcomplex (W : ℝ → ℝ) (x : ℝ) : ℂ := W x

/-- A logarithmic shift by log 2 includes the entire compact upper support. -/
def signal (W : ℝ→ℝ) (t : ℝ) : ℝ :=
  (scaled (Wcomplex W) (2*Real.exp (-t))).re

private theorem complex_support {W : ℝ→ℝ}
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) :
    ∀ x∉Set.Ioo (1:ℝ) 2,Wcomplex W x=0 := by
  intro x hx
  simp [Wcomplex,hW x hx]

private theorem complex_lip {W : ℝ→ℝ} {K : ℝ}
    (hW : ∀ x y : ℝ,|W x-W y|≤K*|x-y|) :
    ∀ x y : ℝ,‖Wcomplex W x-Wcomplex W y‖≤K*|x-y| := by
  intro x y
  unfold Wcomplex
  rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact hW x y

private theorem scaled_real {W : ℝ→ℝ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {x : ℝ} (hx : 0<x) :
    ((scaled (Wcomplex W) x).re:ℂ)=scaled (Wcomplex W) x := by
  let R := ⌈2/x⌉₊
  have hR : 2≤(R:ℝ)*x := (div_le_iff₀ hx).1 (Nat.le_ceil _)
  rw [scaled_finite (complex_support hW) hx hR,Complex.re_sum]
  push_cast
  congr 1
  ext n
  simp [Wcomplex,Complex.mul_re]

private theorem signal_cast {W : ℝ→ℝ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (t : ℝ) :
    (signal W t:ℂ)=scaled (Wcomplex W) (2*Real.exp (-t)) :=
  scaled_real hW (by positivity)

private theorem signal_continuous {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) : Continuous (signal W) := by
  have hcW : Continuous (Wcomplex W) := continuous_ofReal.comp hc
  have hs := continuousOn_scaled hcW (complex_support hW)
  have hpos : ∀ t : ℝ, 2*Real.exp (-t)∈Set.Ioi (0:ℝ) := by intro t; change 0<2*Real.exp (-t); positivity
  have h := hs.comp_continuous (f:=fun t : ℝ => 2*Real.exp (-t)) (by fun_prop) hpos
  exact continuous_re.comp h

private theorem W_bound {W : ℝ→ℝ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ,|W x-W y|≤K*|x-y|) (x : ℝ) :
    |W x|≤K := by
  by_cases hx : x∈Set.Ioo (1:ℝ) 2
  · have h := hlip x 1
    rw [hW 1 (by simp),sub_zero,abs_of_nonneg (sub_nonneg.mpr hx.1.le)] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left (show x-1≤1 by linarith [hx.2]) hK])
  · rw [hW x hx,abs_zero]
    exact hK

private theorem signal_exp_bound {W : ℝ→ℝ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ,|W x-W y|≤K*|x-y|) {t : ℝ} (ht : 0≤t) :
    |signal W t|≤3*K*Real.exp t := by
  let x := 2*Real.exp (-t)
  have hx : 0<x := by dsimp [x]; positivity
  let R := ⌈Real.exp t⌉₊
  have hR : 2≤(R:ℝ)*x := by
    have h := Nat.le_ceil (Real.exp t)
    calc
      _ = Real.exp t*x := by dsimp [x]; rw [←mul_assoc,mul_comm (Real.exp t) 2,mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,mul_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right h hx.le
  have hRcard : ((R+1:ℕ):ℝ)≤3*Real.exp t := by
    have hr := Nat.ceil_lt_add_one (Real.exp_nonneg t)
    have hp : 1≤Real.exp t := Real.one_le_exp ht
    change (R:ℝ)<Real.exp t+1 at hr
    push_cast
    linarith
  have hsum : ‖scaled (Wcomplex W) x‖≤((R+1:ℕ):ℝ)*K := by
    rw [scaled_finite (complex_support hW) hx hR]
    calc
      _ ≤ ∑ n∈range (R+1),‖(μ n:ℂ)*Wcomplex W ((n:ℝ)*x)‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈range (R+1),K := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,Wcomplex,Complex.norm_real,Real.norm_eq_abs]
        have hmu : ‖(μ n:ℂ)‖≤1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one (n:=n)
        exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)).trans
          (by simpa using W_bound hW hK hlip ((n:ℝ)*x))
      _ = _ := by simp
  have hcast := signal_cast hW t
  rw [←hcast,Complex.norm_real,Real.norm_eq_abs] at hsum
  exact hsum.trans ((mul_le_mul_of_nonneg_right hRcard hK).trans_eq (by ring))

private theorem signal_laplace_integrable {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ,|W x-W y|≤K*|x-y|)
    {s : ℂ} (hs : 1<s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s*(t:ℂ))*(signal W t:ℂ)) (Set.Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => 3*K*Real.exp (-(s.re-1)*t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (sub_pos.mpr hs)) 0).const_mul _
  have hcont : Continuous (fun t : ℝ => Complex.exp (-s*(t:ℂ))*(signal W t:ℂ)) := by
    exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-s*(t:ℂ)))).mul
      (continuous_ofReal.comp (signal_continuous hc hW))
  apply hi.mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hh := signal_exp_bound hW hK hlip ht.le
  rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
  have he : (-s*(t:ℂ)).re=-s.re*t := by simp [Complex.mul_re]
  rw [he]
  calc
    _ ≤ Real.exp (-s.re*t)*(3*K*Real.exp t) := mul_le_mul_of_nonneg_left hh (Real.exp_nonneg _)
    _ = _ := by rw [mul_left_comm (Real.exp (-s.re*t)),←Real.exp_add]; congr 2; ring

private theorem exp_image : (fun t : ℝ => 2*Real.exp (-t)) '' (Set.Ioi 0)=Set.Ioo 0 2 := by
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨by positivity,?_⟩
    have hh : Real.exp (-t)<1 := Real.exp_lt_one_iff.mpr (by linarith [show 0<t from ht])
    linarith
  · intro hx
    have hx0 : 0<x := hx.1
    refine ⟨-Real.log (x/2),?_,?_⟩
    · have h : Real.log (x/2)<0 := Real.log_neg (by positivity) (by linarith [hx.2])
      exact neg_pos.mpr h
    · change 2*Real.exp (-(-Real.log (x/2)))=x
      rw [neg_neg,Real.exp_log (by positivity)]
      ring

private theorem exp_inj : Set.InjOn (fun t : ℝ => 2*Real.exp (-t)) (Set.Ioi 0) := by
  intro x hx y hy he
  have hh : Real.exp (-x)=Real.exp (-y) := by linarith
  have hh := Real.exp_injective hh
  linarith

/-- The shifted logarithmic signal has the complete Mellin transform, with
the explicit dilation factor and no interval omitted. -/
theorem signal_mellin {W : ℝ→ℝ} (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) :
    mellin (scaled (Wcomplex W)) s =
      (2:ℂ)^s*(∫ t in Set.Ioi (0:ℝ),Complex.exp (-s*(t:ℂ))*(signal W t:ℂ)) := by
  unfold mellin
  have he : (∫ x in Set.Ioi (0:ℝ),(x:ℂ)^(s-1) • scaled (Wcomplex W) x)=
      ∫ x in Set.Ioo (0:ℝ) 2,(x:ℂ)^(s-1) • scaled (Wcomplex W) x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hx.1)
    intro x hx
    have h2 : 2≤x := by by_contra! hh; exact hx.2 ⟨hx.1,hh⟩
    rw [zero_top (complex_support hW) h2,smul_zero]
  rw [he,←exp_image]
  have hderiv : ∀ t∈Set.Ioi (0:ℝ), HasDerivWithinAt
      (fun x : ℝ => 2*Real.exp (-x)) (-2*Real.exp (-t)) (Set.Ioi 0) t := by
    intro t ht
    have h := (((hasDerivAt_id t).neg.exp).const_mul 2)
    change HasDerivAt (fun y : ℝ => 2*Real.exp (-y)) (2*(Real.exp (-t)*(-1))) t at h
    convert h.hasDerivWithinAt using 1
    ring
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv exp_inj]
  rw [←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hpos : 0<2*Real.exp (-t) := by positivity
  change |-2*Real.exp (-t)| • (((2*Real.exp (-t):ℝ):ℂ)^(s-1) • scaled (Wcomplex W) (2*Real.exp (-t)))=
    (2:ℂ)^s*(Complex.exp (-s*(t:ℂ))*(signal W t:ℂ))
  rw [abs_of_nonpos (show -2*Real.exp (-t)≤0 by linarith [Real.exp_pos (-t)])]
  simp only [neg_mul,neg_neg,Complex.real_smul,smul_eq_mul]
  rw [←signal_cast hW t]
  have hcpow : ((2*Real.exp (-t):ℝ):ℂ)*((2*Real.exp (-t):ℝ):ℂ)^(s-1)=
      (2:ℂ)^s*Complex.exp (-s*(t:ℂ)) := by
    conv_lhs => lhs; rw [←Complex.cpow_one ((2*Real.exp (-t):ℝ):ℂ)]
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hpos.ne'),
      show (1:ℂ)+(s-1)=s by ring,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity),
      Complex.ofReal_exp,Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
    push_cast
    congr 1
    ring
  rw [←mul_assoc,hcpow]
  rw [neg_mul,mul_assoc]

private def polar (W : ℝ→ℝ) (s : ℂ) : ℂ :=
  Complex.exp (-s*Complex.log 2)*mellin (Wcomplex W) s*(s-1)/riemannZeta₁ s

private theorem kernel_analytic {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) : AnalyticAt ℂ (mellin (Wcomplex W)) s := by
  have h : Differentiable ℂ (mellin (Wcomplex W)) :=
    fun x => W_differentiableAt (continuous_ofReal.comp hc) (complex_support hW) x
  exact h.analyticAt s

private theorem polar_meromorphic {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) (s : ℂ) : MeromorphicAt (polar W) s := by
  unfold polar
  have hfactor : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z*Complex.log 2)) s := by fun_prop
  exact (((hfactor.mul (kernel_analytic hc hW s)).mul (analyticAt_id.sub analyticAt_const)).meromorphicAt).div
    (differentiable_riemannZeta₁.analyticAt s).meromorphicAt

private theorem normalized_zeta_real_ne_zero {x : ℝ} (hx : 0<x) :
    riemannZeta₁ (x:ℂ)≠0 := by
  by_cases hx1 : x=1
  · subst x; simp
  · have hs := D5.S3.Analytic.Isolation.RiemannZetaPositiveRealSign.riemannZeta_ofReal_sign hx hx1
    have hz : riemannZeta (x:ℂ)≠0 := by
      intro hz
      rw [hz] at hs
      rcases hs.2 with h|h <;> simp only [Complex.zero_re] at h <;> linarith [h.2]
    intro hn
    apply hz
    rw [riemannZeta_eq_inv_sub_mul (by exact_mod_cast hx1),hn,mul_zero]

private theorem polar_real {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) {x : ℝ} (hx : 0<x) :
    AnalyticAt ℂ (polar W) (x:ℂ) := by
  unfold polar
  have hfactor : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z*Complex.log 2)) (x:ℂ) := by fun_prop
  exact ((hfactor.mul (kernel_analytic hc hW _)).mul (analyticAt_id.sub analyticAt_const)).div
    (differentiable_riemannZeta₁.analyticAt _) (normalized_zeta_real_ne_zero hx)

private theorem polar_eq_integral {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0) {s : ℂ} (hs : 1<s.re) :
    polar W s=∫ t in Set.Ioi (0:ℝ),Complex.exp (-s*(t:ℂ))*(signal W t:ℂ) := by
  have hs1 : s≠1 := by intro he; subst s; norm_num at hs
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  have hZ : riemannZeta₁ s≠0 := by
    intro h
    apply hz
    rw [riemannZeta_eq_inv_sub_mul hs1,h,mul_zero]
  have hm := scaled_mellin_dirichlet (continuous_ofReal.comp hc) (complex_support hW) hs
  change riemannZeta s*mellin (scaled (Wcomplex W)) s=mellin (Wcomplex W) s at hm
  rw [riemannZeta_eq_inv_sub_mul hs1,signal_mellin hW s] at hm
  have hdiv : mellin (Wcomplex W) s*(s-1)/riemannZeta₁ s =
      (2:ℂ)^s*(∫ t in Set.Ioi (0:ℝ),Complex.exp (-s*(t:ℂ))*(signal W t:ℂ)) := by
    field_simp [sub_ne_zero.mpr hs1,hZ] at hm ⊢
    linear_combination -hm
  unfold polar
  rw [mul_assoc,mul_div_assoc,hdiv,←mul_assoc]
  have he : Complex.exp (-s*Complex.log 2)*(2:ℂ)^s=1 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num),←Complex.exp_add,
      show -s*Complex.log 2+Complex.log 2*s=0 by ring,Complex.exp_zero]
  rw [he,one_mul]

private def normalized (W : ℝ→ℝ) (β t : ℝ) : ℝ := Real.exp (-β*t)*signal W t

private theorem normalized_kernel (W : ℝ→ℝ) (β : ℝ) (s : ℂ) :
    EulerPoleObstruction.kernel (normalized W β) (s-β)=
      fun t : ℝ => Complex.exp (-s*(t:ℂ))*(signal W t:ℂ) := by
  funext t
  simp only [EulerPoleObstruction.kernel,normalized,Complex.ofReal_mul,Complex.ofReal_exp,
    Complex.ofReal_neg,←mul_assoc,←Complex.exp_add]
  congr 2
  ring

/-- A one-sided exponential bound for the logarithmic actual Möbius signal
excludes genuine zeta zeros to its right, by positivity and real-regular
meromorphic continuation. -/
theorem zero_re_le_of_one_sided_signal {W : ℝ→ℝ} (hc : Continuous W)
    (hW : ∀ x∉Set.Ioo (1:ℝ) 2,W x=0)
    {K : ℝ} (hK : 0≤K) (hlip : ∀ x y : ℝ,|W x-W y|≤K*|x-y|)
    {β c C : ℝ} (hβ : 0<β) (hβ1 : β<1) (hc0 : c≠0)
    (hbound : ∀ᶠ t in atTop,c*signal W t≤C*Real.exp (β*t))
    {rho : ℂ} (hz : riemannZeta rho=0) (hrho1 : rho.re<1)
    (hker : mellin (Wcomplex W) rho≠0) : rho.re≤β := by
  have hnorm : ∀ᶠ t in atTop,c*normalized W β t≤0*t+C := by
    filter_upwards [hbound] with t ht
    have h := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg (-β*t))
    have hcancel : Real.exp (-β*t)*Real.exp (β*t)=1 := by
      rw [←Real.exp_add,show -β*t+β*t=0 by ring,Real.exp_zero]
    calc
      c*normalized W β t=Real.exp (-β*t)*(c*signal W t) := by unfold normalized;ring
      _ ≤ Real.exp (-β*t)*(C*Real.exp (β*t)) := h
      _ = 0*t+C := by rw [mul_left_comm,hcancel];ring
  obtain ⟨L,hL,hMatch⟩ := PositiveLaplaceContinuation.analytic_continuation_of_affine_bound
    (a:=β) (b:=1) (U:=0) (f:=normalized W β) (F:=polar W) (by norm_num) hβ1
    ((show Continuous (fun t : ℝ => Real.exp (-β*t)) by fun_prop).mul (signal_continuous hc hW)) hc0 hnorm
    (fun s hs => by rw [normalized_kernel];exact signal_laplace_integrable hc hW hK hlip hs)
    (fun s hs => by
      change polar W s=∫ t in Set.Ioi (0:ℝ),EulerPoleObstruction.kernel (normalized W β) (s-β) t
      rw [normalized_kernel,polar_eq_integral hc hW hs])
    (fun s _ => polar_meromorphic hc hW s)
    (fun x hx => polar_real hc hW (hβ.trans hx))
  let U := {s : ℂ | β<s.re}
  let G (s : ℂ) := Complex.exp (-s*Complex.log 2)*mellin (Wcomplex W) s*(s-1)
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt β).isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta₁ U := fun s _ => differentiable_riemannZeta₁.analyticAt s
  have hprod : AnalyticOnNhd ℂ (fun s => L s*riemannZeta₁ s) U := hL.mul hζ
  have hG : AnalyticOnNhd ℂ G U := by
    intro s hs
    have hF : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z*Complex.log 2)) s := by fun_prop
    exact (hF.mul (kernel_analytic hc hW s)).mul (analyticAt_id.sub analyticAt_const)
  have htwo : (2:ℂ)∈U := by change β<(2:ℂ).re; norm_num;linarith
  have hlocal : (fun s => L s*riemannZeta₁ s)=ᶠ[𝓝 (2:ℂ)] G := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds (show (1:ℝ)<(2:ℂ).re by norm_num)] with s hs
    change 1<s.re at hs
    have hZ : riemannZeta₁ s≠0 := by
      intro h
      apply riemannZeta_ne_zero_of_one_lt_re hs
      rw [riemannZeta_eq_inv_sub_mul (by intro he;subst s;norm_num at hs),h,mul_zero]
    change L s*riemannZeta₁ s=G s
    rw [hMatch s hs,polar]
    dsimp [G]
    field_simp
  by_contra! hbad
  have he := hprod.eqOn_of_preconnected_of_eventuallyEq hG hconn htwo hlocal (show rho∈U from hbad)
  have hρne : rho≠1 := by intro he;subst rho;norm_num at hrho1
  have hZ : riemannZeta₁ rho=0 := by
    have h := (riemannZeta_eq_inv_sub_mul hρne).symm.trans hz
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (sub_ne_zero.mpr hρne))
  change L rho*riemannZeta₁ rho=G rho at he
  rw [hZ,mul_zero] at he
  exact (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hker) (sub_ne_zero.mpr hρne)) he.symm

end NymanOneSidedScalar
