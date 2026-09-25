/- GID: D5/S3/Quantum/Information/FixedSupportFisherGap
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/FixedSupportFisherGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive fixed-support Fisher gap for one normalized same-curve family. -/

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter Finset
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FixedSupportGap

/-- A uniform Fisher bound for one finite probability curve on fixed support has a positive gap. -/
theorem result {ι : Type*} [Fintype ι] (a R : ℝ) (x : ι → ℝ) (p : ι → ℝ → ℝ)
    (ha : 0 < a) (ha1 : a < 1)
    (hx : ∀ j, x j ∈ Icc (-1 : ℝ) 1)
    (hp : ∀ u ∈ Ioo (2*a-1) 1, ∀ j, 0 ≤ p j u)
    (hd : ∀ j, DifferentiableOn ℝ (p j) (Ioo (2*a-1) 1))
    (h0 : ∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u = 1)
    (h1 : ∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u * x j = a)
    (h2 : ∀ u ∈ Ioo (2*a-1) 1, ∑ j, p j u * x j^2 = (1+u)/2)
    (hI : ∀ u ∈ Ioo (2*a-1) 1,
      (∑ j ∈ univ.filter (fun j => 0 < p j u), (deriv (p j) u)^2 / p j u) ≤
        R*(1-a^2)/((1-u)*(1+u-2*a^2))) :
    1 + a^2 / (1+4*a+2*(1+a)*Real.log 2)^2 ≤ R := by
  classical
  let J := Ioo (2*a-1) (1 : ℝ)
  let d := 1-a^2
  let l := fun u : ℝ => (1-u)/2
  let q := fun u : ℝ => (1+u)/2-a^2
  let N := fun u : ℝ => ∑ j, p j u * (1-x j^2)*x j
  let m := fun u : ℝ => N u / l u
  have hdpos : 0 < d := by dsimp [d]; nlinarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  have haJ : a ∈ J := by constructor <;> linarith
  have hlpos {u : ℝ} (hu : u ∈ J) : 0 < l u := by dsimp [l]; linarith [hu.2]
  have hqpos {u : ℝ} (hu : u ∈ J) : 0 < q u := by
    dsimp [q]; nlinarith [hu.1, mul_pos ha (sub_pos.mpr ha1)]
  have hdl (u : ℝ) : HasDerivAt l (-(1/2)) u := by
    convert ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).div_const 2 using 1 <;> first | rfl | norm_num [l]
  have hdp {u : ℝ} (hu : u ∈ J) (j : ι) : HasDerivAt (p j) (deriv (p j) u) u :=
    ((hd j).differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
  have hzero {u : ℝ} (hu : u ∈ J) {j : ι} (hz : p j u = 0) : deriv (p j) u = 0 := by
    apply IsLocalMin.deriv_eq_zero
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    rw [hz]
    exact hp v hv j
  have hfiltered {u : ℝ} (hu : u ∈ J) :
      (∑ j ∈ univ.filter (fun j => 0 < p j u), (deriv (p j) u)^2 / p j u) =
      ∑ j, (deriv (p j) u)^2 / p j u := by
    apply sum_subset (filter_subset _ _) ?_
    intro j _ hj
    have hz : p j u = 0 := le_antisymm (le_of_not_gt (by simpa using hj)) (hp u hu j)
    simp [hz, hzero hu hz]
  have hIall {u : ℝ} (hu : u ∈ J) :
      (∑ j, (deriv (p j) u)^2 / p j u) ≤ R*d/((1-u)*(1+u-2*a^2)) := by
    rw [← hfiltered hu]
    exact hI u hu
  have hdm {u : ℝ} (hu : u ∈ J) : HasDerivAt m
      ((∑ j, deriv (p j) u * (1-x j^2)*x j) / l u + m u / (2*l u)) u := by
    have hn : HasDerivAt N (∑ j, deriv (p j) u * (1-x j^2)*x j) u :=
      HasDerivAt.fun_sum (fun j _ => ((hdp hu j).mul_const _).mul_const _)
    convert hn.div (hdl u) (ne_of_gt (hlpos hu)) using 1 <;>
      first | rfl | (dsimp [m]; field_simp [ne_of_gt (hlpos hu)]; ring)
  have hpoint {u : ℝ} (hu : u ∈ J) :
      1 ≤ R ∧ |m u-a*l u/d| ≤ q u/d * (Real.sqrt (R-1)/Real.sqrt R) ∧
      |deriv m u| ≤ Real.sqrt (R-1)/(1-u) := by
    let w := fun j => p j u
    let v := fun j => deriv (p j) u
    let I := ∑ j, (v j)^2 / w j
    let E := fun f : ι → ℝ => ∑ j, w j * f j
    let H := (1+u)/2
    let L := l u
    let Q := q u
    let M := m u
    let T := E (fun j => (1-x j^2)*(x j-M)^2) / L
    let K := L*(a-M)/Q
    let Y := fun j => x j^2-H-K*(x j-a)
    have hL : 0 < L := hlpos hu
    have hQ : 0 < Q := hqpos hu
    have hLn : L ≠ 0 := ne_of_gt hL
    have hQn : Q ≠ 0 := ne_of_gt hQ
    have hId : I ≤ R*d/(4*L*Q) := by
      convert hIall hu using 1
      dsimp [I, v, w, d, L, Q, l, q]
      congr 1
      ring
    have hIn : 0 ≤ I := sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (hp u hu j))
    have hW : ∀ j, 0 ≤ w j := hp u hu
    have hX : ∀ j, 0 ≤ 1-x j^2 := fun j => by
      have h := hx j; nlinarith [h.1, h.2, mul_nonneg (sub_nonneg.mpr h.2) (by linarith [h.1] : 0 ≤ 1+x j)]
    have hE0 : E (fun _ => 1) = 1 := by simpa [E, w] using h0 u hu
    have hE1 : E x = a := h1 u hu
    have hE2 : E (fun j => x j^2) = H := h2 u hu
    have hN : E (fun j => (1-x j^2)*x j) = L*M := by
      dsimp [E, M, m, L, w, N]
      rw [mul_div_cancel₀ _ (ne_of_gt (hlpos hu))]
      apply sum_congr rfl; intro j _; ring
    have hT : E (fun j => (1-x j^2)*(x j-M)^2) = L*T := by
      dsimp [T]; rw [mul_div_cancel₀ _ hLn]
    have hTn : 0 ≤ T := div_nonneg (sum_nonneg (fun j _ =>
      mul_nonneg (hW j) (mul_nonneg (hX j) (sq_nonneg _)))) hL.le
    have hmom0 : ∑ j, v j = 0 := by
      have he : (fun t => ∑ j, p j t) =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
        exact h0 t ht
      exact (HasDerivAt.fun_sum (fun j _ => hdp hu j)).unique
        ((hasDerivAt_const u 1).congr_of_eventuallyEq he)
    have hmom1 : ∑ j, v j*x j = 0 := by
      have he : (fun t => ∑ j, p j t*x j) =ᶠ[𝓝 u] (fun _ => a) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
        exact h1 t ht
      exact (HasDerivAt.fun_sum (fun j _ => (hdp hu j).mul_const _)).unique
        ((hasDerivAt_const u a).congr_of_eventuallyEq he)
    have hmom2 : ∑ j, v j*x j^2 = 1/2 := by
      have he : (fun t => ∑ j, p j t*x j^2) =ᶠ[𝓝 u] (fun t => (1+t)/2) := by
        filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
        exact h2 t ht
      have hb := ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u)).div_const 2
      norm_num at hb
      exact (HasDerivAt.fun_sum (fun j _ => (hdp hu j).mul_const _)).unique
        (hb.congr_of_eventuallyEq he)
    have hCS (f : ι → ℝ) : (∑ j, v j*f j)^2 ≤ I*E (fun j => (f j)^2) := by
      apply sum_sq_le_sum_mul_sum_of_sq_le_mul univ
        (fun j _ => div_nonneg (sq_nonneg _) (hW j))
        (fun j _ => mul_nonneg (hW j) (sq_nonneg _))
      intro j _
      by_cases hz : w j = 0
      · have hv : v j = 0 := hzero hu hz
        simp [hz, hv]
      · exact le_of_eq (by field_simp)
    have hscoreY : (∑ j, v j*Y j) = 1/2 := by
      calc
        _ = (∑ j, v j*x j^2) - H*(∑ j, v j) -
            K*((∑ j, v j*x j)-a*(∑ j, v j)) := by
          simp only [Y, mul_sum, ← sum_sub_distrib]
          apply sum_congr rfl
          intro j _
          ring
        _ = 1/2 := by rw [hmom0, hmom1, hmom2]; ring
    have hEY : E (fun j => (Y j)^2) =
        L*Q/d - L*d/Q*(M-a*L/d)^2 - L*T := by
      have hexpand : E (fun j => (Y j)^2) =
          ((K*a-H)^2+M^2)*E (fun _ => 1) +
          (-2*K^2*a+2*K*H-2*K)*E x +
          (K^2+2*K*a-2*H+1-M^2)*E (fun j => x j^2) +
          (2*K-2*M)*E (fun j => (1-x j^2)*x j) -
          E (fun j => (1-x j^2)*(x j-M)^2) := by
        dsimp [E]
        simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
        apply sum_congr rfl
        intro j _
        dsimp [Y]
        ring
      rw [hexpand, hE0, hE1, hE2, hN, hT]
      dsimp only [K]
      field_simp [hQn, hdne]
      dsimp [L, Q, H, d, l, q]
      ring
    have hreg : (1/4 : ℝ) ≤ I*(L*Q/d - L*d/Q*(M-a*L/d)^2-L*T) := by
      have hc := hCS Y
      rw [hscoreY, hEY] at hc
      norm_num at hc ⊢
      exact hc
    have hVn : 0 ≤ L*Q/d-L*d/Q*(M-a*L/d)^2-L*T := by
      rw [← hEY]
      exact sum_nonneg (fun j _ => mul_nonneg (hW j) (sq_nonneg _))
    have hR0 : 0 ≤ R := by
      have hb := (le_div_iff₀ (show 0 < 4*L*Q by positivity)).mp (hIn.trans hId)
      have hc : 0 ≤ R*d := by simpa only [zero_mul] using hb
      exact (mul_nonneg_iff_of_pos_right hdpos).mp hc
    have hmaster : R*d^2*(M-a*L/d)^2 + R*d*Q*T ≤ (R-1)*Q^2 := by
      have hb := hreg.trans (mul_le_mul_of_nonneg_right hId hVn)
      have hpos : 0 < 4*L*Q^2 := by positivity
      have hb' := (mul_le_mul_of_nonneg_right hb hpos.le)
      field_simp [hLn, hQn, hdne] at hb'
      have he : d^2*(M-a*L/d)^2 = (d*M-L*a)^2 := by field_simp
      rw [mul_assoc R (d^2), he]
      nlinarith only [hb']
    have hRm : 1 ≤ R := by
      have hnon1 : 0 ≤ R*d^2*(M-a*L/d)^2 := by positivity
      have hnon2 : 0 ≤ R*d*Q*T := by positivity
      have hq2 : 0 < Q^2 := sq_pos_of_pos hQ
      nlinarith only [hmaster, hnon1, hnon2, hq2]
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRm
    have hs : 0 ≤ Real.sqrt (R-1) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt (R-1))^2 = R-1 := Real.sq_sqrt (by linarith)
    have hr : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
    have hr2 : (Real.sqrt R)^2 = R := Real.sq_sqrt hRpos.le
    have hmean : |M-a*L/d| ≤ Q/d*(Real.sqrt (R-1)/Real.sqrt R) := by
      apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      rw [sq_abs]
      apply (mul_le_mul_iff_of_pos_left (show 0 < R*d^2 by positivity)).mp
      have hh : R*d^2*(Q/d*(Real.sqrt (R-1)/Real.sqrt R))^2 = (R-1)*Q^2 := by
        field_simp
        nlinarith only [hs2, hr2]
      rw [hh]
      exact le_trans (le_add_of_nonneg_right (by positivity)) hmaster
    have hvar : I*T ≤ (R-1)/(4*L) := by
      have htbound : R*d*Q*T ≤ (R-1)*Q^2 :=
        le_trans (le_add_of_nonneg_left (by positivity)) hmaster
      have hit := mul_le_mul_of_nonneg_right hId hTn
      apply (le_div_iff₀ (show 0 < 4*L by positivity)).mpr
      apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hQ)).mp
      have hb := mul_le_mul_of_nonneg_right hit (show 0 ≤ 4*L*Q^2 by positivity)
      have he : R*d/(4*L*Q)*T*(4*L*Q^2) = R*d*Q*T := by field_simp
      rw [he] at hb
      nlinarith only [hb, htbound]
    have hspeedCS := hCS (fun j => (1-x j^2)*(x j-M))
    have hspeedE : E (fun j => ((1-x j^2)*(x j-M))^2) ≤ L*T := by
      rw [← hT]
      apply sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hW j)
      have hh := hX j
      have hx2 := sq_nonneg (x j)
      have hm2 := sq_nonneg (x j-M)
      nlinarith only [mul_nonneg (mul_nonneg hh hx2) hm2]
    have hscoreM : (∑ j, v j*((1-x j^2)*(x j-M))) = L*deriv m u := by
      have hmder := (hdm hu).deriv
      have hmom : (∑ j, v j*(1-x j^2)) = -(1/2) := by
        simp only [mul_sub, mul_one, sum_sub_distrib, hmom0, hmom2]; ring
      calc
        _ = (∑ j, v j*(1-x j^2)*x j) - M*(∑ j, v j*(1-x j^2)) := by
          simp only [mul_sum, ← sum_sub_distrib]
          apply sum_congr rfl; intro j _; ring
        _ = L*deriv m u := by rw [hmom, hmder]; dsimp [L, M, v]; field_simp [ne_of_gt (hlpos hu)]; ring
    have hspeed : |deriv m u| ≤ Real.sqrt (R-1)/(1-u) := by
      rw [hscoreM] at hspeedCS
      have hc := hspeedCS.trans (mul_le_mul_of_nonneg_left hspeedE hIn)
      have hlue : 1-u = 2*L := by dsimp [L, l]; ring
      rw [hlue]
      apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
      rw [sq_abs]
      apply (mul_le_mul_iff_of_pos_left (show 0 < (2*L)^2 by positivity)).mp
      have hsdiv : (2*L)^2*(Real.sqrt (R-1)/(2*L))^2 = R-1 := by
        field_simp
        exact hs2
      rw [hsdiv]
      have hv' := (le_div_iff₀ (show 0 < 4*L by positivity)).mp hvar
      nlinarith only [hc, hv']
    exact ⟨hRm, hmean, hspeed⟩
  have hR : 1 ≤ R := (hpoint haJ).1
  let s := Real.sqrt (R-1)
  let r := Real.sqrt R
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = R-1 := Real.sq_sqrt (by linarith)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact (Real.one_le_sqrt).2 hR
  have hlog {u : ℝ} (hu : u ∈ J) :
      HasDerivAt (fun t : ℝ => Real.log (1-t)) (-(1/(1-u))) u := by
    have hh := ((hasDerivAt_id u).const_sub 1).log (by linarith [hu.2] : (1 : ℝ)-u ≠ 0)
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  have hmove {u v : ℝ} (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v) :
      |m v-m u| ≤ s*(Real.log (1-u)-Real.log (1-v)) := by
    have hplusd {t : ℝ} (ht : t ∈ J) :
        HasDerivAt (fun z => m z+s*Real.log (1-z)) (deriv m t-s/(1-t)) t := by
      convert ((hdm ht).differentiableAt.hasDerivAt).add ((hlog ht).const_mul s) using 1 <;> first | rfl | ring
    have hminusd {t : ℝ} (ht : t ∈ J) :
        HasDerivAt (fun z => m z-s*Real.log (1-z)) (deriv m t+s/(1-t)) t := by
      convert ((hdm ht).differentiableAt.hasDerivAt).sub ((hlog ht).const_mul s) using 1 <;> first | rfl | ring
    have hplus : AntitoneOn (fun z => m z+s*Real.log (1-z)) J := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
      · intro t ht; exact (hplusd ht).continuousAt.continuousWithinAt
      · intro t ht; exact (hplusd (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hplusd (interior_subset ht)).deriv]
        exact sub_nonpos.mpr ((le_abs_self _).trans (hpoint (interior_subset ht)).2.2)
    have hminus : MonotoneOn (fun z => m z-s*Real.log (1-z)) J := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
      · intro t ht; exact (hminusd ht).continuousAt.continuousWithinAt
      · intro t ht; exact (hminusd (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [(hminusd (interior_subset ht)).deriv]
        have hb := (abs_le.mp (hpoint (interior_subset ht)).2.2).1
        linarith only [hb]
    have hpa := hplus hu hv huv
    have hma := hminus hu hv huv
    apply abs_le.mpr
    constructor <;> dsimp at hpa hma ⊢ <;> linarith only [hpa, hma]
  have hfinite {u : ℝ} (hu : u ∈ J) (hua : u ≤ a) :
      a*l u/d-a*l a/d ≤ (q u+q a)/d*(s/r) + s*(Real.log (1-u)-Real.log (1-a)) := by
    have hm0 := (abs_le.mp (hpoint hu).2.1).1
    have hm1 := (abs_le.mp (hpoint haJ).2.1).2
    have hmm := (abs_le.mp (hmove hu haJ hua)).1
    change -(q u/d*(s/r)) ≤ m u-a*l u/d at hm0
    change m a-a*l a/d ≤ q a/d*(s/r) at hm1
    have he : (q u+q a)/d*(s/r) = q u/d*(s/r)+q a/d*(s/r) := by ring
    rw [he]
    linarith only [hm0, hm1, hmm]
  let b := 2*a-1
  have hba : b < a := by dsimp [b]; linarith
  have hb1 : 0 < 1-b := by dsimp [b]; linarith
  have hlim : a*l b/d-a*l a/d ≤
      (q b+q a)/d*(s/r) + s*(Real.log (1-b)-Real.log (1-a)) := by
    let f := fun u => a*l u/d-a*l a/d -
      ((q u+q a)/d*(s/r) + s*(Real.log (1-u)-Real.log (1-a)))
    have hc : ContinuousAt f b := by
      dsimp [f, l, q]
      fun_prop (disch := first | positivity | exact ne_of_gt hb1 | exact hdne)
    have hb : Tendsto f (𝓝[>] b) (𝓝 (f b)) := hc.continuousWithinAt.tendsto
    have he : ∀ᶠ u in 𝓝[>] b, f u ≤ 0 := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hba)] with u hu hua
      have huJ : u ∈ J := ⟨hu, lt_trans hua ha1⟩
      exact sub_nonpos.mpr (hfinite huJ hua.le)
    exact sub_nonpos.mp (le_of_tendsto hb he)
  have haminus : (1 : ℝ)-a ≠ 0 := by linarith
  have haplus : (1 : ℝ)+a ≠ 0 := by positivity
  have hloga : Real.log (1-b)-Real.log (1-a) = Real.log 2 := by
    rw [← Real.log_div (ne_of_gt hb1) (by linarith : (1 : ℝ)-a ≠ 0)]
    congr 1
    dsimp [b]
    field_simp [haminus]
    ring
  have hcenter : a*l b/d-a*l a/d = a/(2*(1+a)) := by
    dsimp [l, b]
    field_simp [hdne, haplus]
    dsimp [d]
    ring
  have hwidth : (q b+q a)/d = (1+4*a)/(2*(1+a)) := by
    dsimp [q, b]
    field_simp [hdne, haplus]
    dsimp [d]
    ring
  have hendpoint : a/(2*(1+a)) ≤
      s*((1+4*a)/(2*(1+a)*r)+Real.log 2) := by
    rw [hloga, hcenter, hwidth] at hlim
    convert hlim using 1
    field_simp [haplus, ne_of_gt hr]
  have hweak : a/(2*(1+a)) ≤ s*((1+4*a)/(2*(1+a))+Real.log 2) := by
    apply hendpoint.trans
    apply mul_le_mul_of_nonneg_left _ hs
    apply add_le_add_left
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith only [hr1, ha])
  let C := 1+4*a+2*(1+a)*Real.log 2
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hfinal : a ≤ s*C := by
    have hh := (div_le_iff₀ (show 0 < 2*(1+a) by positivity)).mp hweak
    calc
      a ≤ (s*((1+4*a)/(2*(1+a))+Real.log 2))*(2*(1+a)) := hh
      _ = s*C := by dsimp [C]; field_simp [haplus]
  have hsq : a^2 ≤ s^2*C^2 := by nlinarith only [hfinal, ha, mul_nonneg hs hC.le]
  rw [hs2] at hsq
  have hh := (div_le_iff₀ (sq_pos_of_pos hC)).mpr hsq
  change 1+a^2/C^2 ≤ R
  linarith only [hh]

#print axioms result
end FixedSupportGap
