/- GID: D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree
   generality: G
   mirror-B: D5/B/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The source-normalized series of every positive composition is zero-free in the disk. -/
import D5.S3.AnalyticClosure.Polylogarithm.CompositionRecurrences
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFree
open CompositionDisk CompositionRecurrences
/-- Xu--Zhao's actual positive-composition series on the unit disk.
The local first-contact argument is the classical Miller--Mocanu--Reade
integral-preservation argument; it is not a separate literature or resolution claim. -/
theorem result : diskStatement := by
  have integral : ∀ (g h : ℂ → ℂ) (p : ℕ),
      AnalyticOnNhd ℂ g (Metric.ball 0 1) →
      AnalyticOnNhd ℂ h (Metric.ball 0 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, h z ≠ 0) →
      0 < (g 0 / h 0).re →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < ((p : ℂ) + z * deriv h z / h z).re) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, z * deriv g z + (p : ℂ) * g z = h z) →
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        g z ≠ 0 ∧ 0 < ((p : ℂ) + z * deriv g z / g z).re := by
    intro g h p hg hh hn hinit hpos heq
    have firstContact : ∀ (P Q : ℂ → ℂ),
        AnalyticOnNhd ℂ P (Metric.ball 0 1) →
        (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (Q z).re) →
        0 < (P 0).re →
        (∀ z ∈ Metric.ball (0 : ℂ) 1, z * deriv P z = 1 - P z * Q z) →
        ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (P z).re := by
      intro P Q hP Qpos hP0 hODE w hw
      by_contra hbad
      have hw1 : ‖w‖ < 1 := by simpa using hw
      let K : Set ℂ := {z ∈ Metric.closedBall 0 ‖w‖ | (P z).re ≤ 0}
      have hsub : Metric.closedBall (0 : ℂ) ‖w‖ ⊆ Metric.ball 0 1 := by
        intro z hz
        exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz).trans_lt (by simpa using hw1))
      have hclosed : IsClosed K := Metric.isClosed_closedBall.isClosed_le
        (Complex.continuous_re.comp_continuousOn (hP.continuousOn.mono hsub)) continuousOn_const
      have hcompact : IsCompact K := (isCompact_closedBall (0 : ℂ) ‖w‖).of_isClosed_subset
        hclosed (fun _ h => h.1)
      obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn
        (show K.Nonempty from ⟨w, by simpa [K] using not_lt.mp hbad⟩) continuous_norm.continuousOn
      have hp1 : p ∈ Metric.ball (0 : ℂ) 1 := hsub hp.1
      have hpw : ‖p‖ ≤ ‖w‖ := by simpa using hp.1
      have hpne : p ≠ 0 := by intro h; have := hp.2; rw [h] at this; exact (not_le.mpr hP0) this
      have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hpne
      have hsmall : ∀ z : ℂ, ‖z‖ < ‖p‖ → 0 < (P z).re := by
        intro z hz
        by_contra hh
        have hzK : z ∈ K := ⟨by simpa using hz.le.trans hpw, not_lt.mp hh⟩
        exact (not_le.mpr hz) (hmin hzK)
      have hballsub : Metric.closedBall (0 : ℂ) ‖p‖ ⊆ Metric.ball 0 1 := by
        intro z hz
        apply hsub
        exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hz).trans hpw)
      have hnonneg : ∀ z : ℂ, ‖z‖ ≤ ‖p‖ → 0 ≤ (P z).re := by
        have hcl := le_on_closure (s := Metric.ball (0 : ℂ) ‖p‖)
          (f := fun _ => (0 : ℝ)) (g := fun z => (P z).re)
          (fun z hz => (hsmall z (by simpa using hz)).le) continuousOn_const
          (by rw [closure_ball (0 : ℂ) hpn.ne']; exact
            Complex.continuous_re.comp_continuousOn (hP.continuousOn.mono hballsub))
        intro z hz
        apply hcl
        rw [closure_ball (0 : ℂ) hpn.ne']
        simpa using hz
      have hpzero : (P p).re = 0 := le_antisymm hp.2 (hnonneg p le_rfl)
      have hpd := (hP p hp1).differentiableAt.hasDerivAt
      have hangleC : HasDerivAt (fun t : ℂ => Complex.exp (t * Complex.I) * p)
          (Complex.I * p) 0 := by
        simpa using ((Complex.hasDerivAt_exp (0 * Complex.I)).comp 0
          ((hasDerivAt_id (0 : ℂ)).mul_const Complex.I)).mul_const p
      have hangle : HasDerivAt
          (fun t : ℝ => (P (Complex.exp ((t : ℂ) * Complex.I) * p)).re)
          (deriv P p * (Complex.I * p)).re 0 := by
        simpa using (hpd.comp_of_eq 0 hangleC (by simp)).real_of_complex
      have hangleMin : IsLocalMin
          (fun t : ℝ => (P (Complex.exp ((t : ℂ) * Complex.I) * p)).re) 0 := by
        apply Filter.Eventually.of_forall
        intro t
        simpa [hpzero] using hnonneg (Complex.exp ((t : ℂ) * Complex.I) * p) (by
          simp [Complex.norm_exp])
      have him : (p * deriv P p).im = 0 := by
        have he := hangleMin.hasDerivAt_eq_zero hangle
        simpa [Complex.mul_re, Complex.mul_im, mul_comm] using congrArg Neg.neg he
      have hradC : HasDerivAt (fun t : ℂ => t * p) p 1 := by
        simpa using (hasDerivAt_id (1 : ℂ)).mul_const p
      have hrad : HasDerivAt (fun t : ℝ => (P ((t : ℂ) * p)).re)
          (deriv P p * p).re 1 := by
        simpa using (hpd.comp_of_eq 1 hradC (by simp)).real_of_complex
      have hre : (deriv P p * p).re ≤ 0 := by
        apply le_of_tendsto hrad.tendsto_slope_zero_left
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
          (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))] with t ht htl
        change t < 0 at ht
        have hpp : 0 ≤ (P (((1 + t : ℝ) : ℂ) * p)).re := hnonneg _ (by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          nlinarith [norm_nonneg p])
        simpa [hpzero] using mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr ht.le) hpp
      have ho := hODE p hp1
      have hoi := congrArg Complex.im ho
      have hor := congrArg Complex.re ho
      have hqi := Qpos p hp1
      have hpim : (P p).im = 0 := by
        simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, hpzero, zero_mul, zero_add,
          him] at hoi
        nlinarith
      have hpre : (p * deriv P p).re ≤ 0 := by simpa [mul_comm] using hre
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, hpzero, hpim, zero_mul,
        sub_zero] at hor
      simp only [Complex.mul_re] at hpre
      linarith
    let P : ℂ → ℂ := fun z => g z / h z
    let Q : ℂ → ℂ := fun z => (p : ℂ) + z * deriv h z / h z
    have hPa : AnalyticOnNhd ℂ P (Metric.ball 0 1) := fun z hz =>
      (hg z hz).div (hh z hz) (hn z hz)
    have hODE : ∀ z ∈ Metric.ball (0 : ℂ) 1,
        z * deriv P z = 1 - P z * Q z := by
      intro z hz
      have hd := ((hg z hz).differentiableAt.hasDerivAt.div
        (hh z hz).differentiableAt.hasDerivAt (hn z hz)).deriv
      change deriv P z = _ at hd
      rw [hd]
      dsimp [P, Q]
      have he := heq z hz
      field_simp [hn z hz]
      linear_combination h z * he
    have hp := firstContact P Q hPa hpos hinit hODE
    intro z hz
    have hgz : g z ≠ 0 := by
      intro hzero
      have := hp z hz
      simp [P, hzero] at this
    refine ⟨hgz, ?_⟩
    have hq : (p : ℂ) + z * deriv g z / g z = (P z)⁻¹ := by
      dsimp [P]
      rw [inv_div]
      have he := heq z hz
      field_simp [hgz]
      linear_combination he
    rw [hq, Complex.inv_re]
    exact div_pos (hp z hz) (Complex.normSq_pos.mpr (div_ne_zero hgz (hn z hz)))
  have recover : ∀ (head : ℕ+) (tail : List ℕ+) (h : ℂ → ℂ),
      AnalyticOnNhd ℂ h (Metric.ball 0 1) →
      (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
        z * deriv (li head tail) z = z ^ depth tail * h z) →
      ∀ z ∈ Metric.ball (0 : ℂ) 1,
        z * deriv (normalized head tail) z +
          (depth tail : ℂ) * normalized head tail z = h z := by
    intro head tail h hh hrec
    have ha := (source_series head tail).2.2.2.1
    have hoff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
        z * deriv (normalized head tail) z + (depth tail : ℂ) * normalized head tail z =
          h z := by
      intro z hz hn
      have hd : deriv (li head tail) z =
          (depth tail : ℂ) * z ^ tail.length * normalized head tail z +
            z ^ depth tail * deriv (normalized head tail) z := by
        change deriv (fun w : ℂ => w ^ depth tail * normalized head tail w) z = _
        simpa only [li, Pi.mul_def, depth, Nat.add_sub_cancel] using
          ((hasDerivAt_pow (depth tail) z).mul (ha z hz).differentiableAt.hasDerivAt).deriv
      apply mul_left_cancel₀ (pow_ne_zero (depth tail) hn)
      calc
        z ^ depth tail * (z * deriv (normalized head tail) z +
            (depth tail : ℂ) * normalized head tail z) = z * deriv (li head tail) z := by
          rw [hd]
          simp only [depth, pow_succ]
          ring
        _ = z ^ depth tail * h z := hrec z hz hn
    intro z hz
    by_cases hn : z = 0
    · subst z
      have h0 : (0 : ℂ) ∈ Metric.ball 0 1 := by simp
      have hc : ContinuousAt (fun w : ℂ => w * deriv (normalized head tail) w +
          (depth tail : ℂ) * normalized head tail w) 0 :=
        (continuousAt_id.mul (ha 0 h0).deriv.continuousAt).add
          (continuousAt_const.mul (ha 0 h0).continuousAt)
      have he : (fun w : ℂ => w * deriv (normalized head tail) w +
          (depth tail : ℂ) * normalized head tail w) =ᶠ[𝓝[≠] 0] h := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
          (Metric.isOpen_ball.mem_nhds h0)] with w hw hwU
        exact hoff w hwU (by simpa using hw)
      exact tendsto_nhds_unique (hc.mono_left nhdsWithin_le_nhds)
        (((hh 0 h0).continuousAt.mono_left nhdsWithin_le_nhds).congr' he.symm)
    · exact hoff z hz hn
  let A : List ℕ+ → ℂ → ℂ := fun ks => match ks with
    | [] => fun _ => 1
    | k :: t => normalized k t
  let R : List ℕ+ → ℂ → ℂ := fun ks z => (ks.length : ℂ) + z * deriv (A ks) z / A ks z
  have hAa : ∀ ks, AnalyticOnNhd ℂ (A ks) (Metric.ball 0 1) := by
    intro ks; cases ks with
    | nil => exact analyticOnNhd_const
    | cons k t => exact (source_series k t).2.2.2.1
  have hA0 : ∀ ks, ∃ c : ℝ, 0 < c ∧ A ks 0 = (c : ℂ) := by
    intro ks; cases ks with
    | nil => exact ⟨1, zero_lt_one, rfl⟩
    | cons k t =>
      refine ⟨coefficient k t 0, (source_series k t).1 0, ?_⟩
      change (∑' n, (coefficient k t n : ℂ) * (0 : ℂ) ^ n) = _
      rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]; simp
  have hrep : ∀ ks z, z ∈ Metric.ball (0 : ℂ) 1 → source ks z = z ^ ks.length * A ks z := by
    intro ks z hz; cases ks with
    | nil => simp [source, A]
    | cons k t => exact ((source_series k t).2.2.2.2.1 z (by simpa using hz)).symm
  have hld : ∀ k t z, z ∈ Metric.ball (0 : ℂ) 1 →
      deriv (li k t) z = deriv (source (k :: t)) z := by
    intro k t z hz
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact (source_series k t).2.2.2.2.1 w (by simpa using hw)
  have hone : ∀ z ∈ Metric.ball (0 : ℂ) 1, 1 - z ≠ 0 ∧ 0 < ((1 - z)⁻¹).re := by
    intro z hz
    have hr : 0 < (1 - z).re := by
      have := Complex.re_le_norm z
      have : ‖z‖ < 1 := by simpa using hz
      simp only [Complex.sub_re, Complex.one_re]; linarith
    have hn : 1 - z ≠ 0 := by intro hh; simp [hh] at hr
    exact ⟨hn, by rw [Complex.inv_re]; exact div_pos hr (Complex.normSq_pos.mpr hn)⟩
  have hall : ∀ ks z, z ∈ Metric.ball (0 : ℂ) 1 →
      A ks z ≠ 0 ∧ 0 ≤ (R ks z).re ∧ (ks ≠ [] → 0 < (R ks z).re) := by
    intro ks
    induction ks with
    | nil => intro z hz; simp [A, R, deriv_const]
    | cons k t iht =>
      refine PNat.recOn k ?_ ?_
      · let h : ℂ → ℂ := fun z => A t z / (1 - z)
        have hha : AnalyticOnNhd ℂ h (Metric.ball 0 1) := fun z hz =>
          (hAa t z hz).div (analyticAt_const.sub analyticAt_id) (hone z hz).1
        have hhn : ∀ z ∈ Metric.ball (0 : ℂ) 1, h z ≠ 0 := fun z hz =>
          div_ne_zero (iht z hz).1 (hone z hz).1
        have hhp : ∀ z ∈ Metric.ball (0 : ℂ) 1,
            0 < ((depth t : ℂ) + z * deriv h z / h z).re := by
          intro z hz
          have hd := ((hAa t z hz).differentiableAt.hasDerivAt.div
            ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)) (hone z hz).1).deriv
          have he : (depth t : ℂ) + z * deriv h z / h z = R t z + (1 - z)⁻¹ := by
            change deriv h z = _ at hd
            rw [hd]; dsimp [h, R, depth]
            push_cast
            field_simp [(iht z hz).1, (hone z hz).1]
            ring
          rw [he, Complex.add_re]
          exact add_pos_of_nonneg_of_pos (iht z hz).2.1 (hone z hz).2
        have hinit : 0 < (normalized 1 t 0 / h 0).re := by
          obtain ⟨c, hc, hec⟩ := hA0 (1 :: t)
          obtain ⟨b, hb, heb⟩ := hA0 t
          change normalized 1 t 0 = (c : ℂ) at hec
          simp only [h, hec, heb, sub_zero, div_one, ← Complex.ofReal_div, Complex.ofReal_re]
          exact div_pos hc hb
        have heq := recover 1 t h hha (by
          intro z hz hn
          rw [hld 1 t z hz, source_recurrences.1 t z (by simpa using hz), hrep t z hz]
          dsimp [h, depth]; rw [pow_succ]; ring)
        have hi := integral (normalized 1 t) h (depth t) (hAa (1 :: t)) hha hhn hinit hhp heq
        intro z hz
        exact ⟨(hi z hz).1, (hi z hz).2.le, fun _ => (hi z hz).2⟩
      · intro k ih
        have hinit : 0 < (normalized (k + 1) t 0 / normalized k t 0).re := by
          obtain ⟨c, hc, hec⟩ := hA0 ((k + 1) :: t)
          obtain ⟨b, hb, heb⟩ := hA0 (k :: t)
          change normalized (k + 1) t 0 = (c : ℂ) at hec
          change normalized k t 0 = (b : ℂ) at heb
          rw [hec, heb, ← Complex.ofReal_div, Complex.ofReal_re]; exact div_pos hc hb
        have heq := recover (k + 1) t (normalized k t) (hAa (k :: t)) (by
          intro z hz hn
          rw [hld (k + 1) t z hz, (source_derivative (k + 1) t z (by simpa using hz)).deriv]
          change z * derivativeSeries ((↑(k + 1) : ℕ) - 1) t z = li k t z
          rw [(source_series k t).2.2.2.2.1 z (by simpa using hz)]
          simp only [derivativeSeries, source, PNat.add_coe, PNat.val_ofNat, Nat.add_sub_cancel]
          rw [← tsum_mul_left]
          apply tsum_congr; intro n; ring)
        have hi := integral (normalized (k + 1) t) (normalized k t) (depth t)
          (hAa ((k + 1) :: t)) (hAa (k :: t)) (fun z hz => (ih z hz).1)
          hinit (fun z hz => (ih z hz).2.2 (by simp)) heq
        intro z hz
        exact ⟨(hi z hz).1, (hi z hz).2.le, fun _ => (hi z hz).2⟩
  intro head tail
  have ha := (source_series head tail).2.2.2.1
  have hn : ∀ z ∈ Metric.ball (0 : ℂ) 1, normalized head tail z ≠ 0 :=
    fun z hz => (hall (head :: tail) z hz).1
  have hq : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      logarithmicDerivative head tail z = R (head :: tail) z := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z; simp [logarithmicDerivative, R, depth]
    · rw [logarithmicDerivative, if_neg hz0]
      have hd : deriv (li head tail) z =
          (depth tail : ℂ) * z ^ tail.length * normalized head tail z +
            z ^ depth tail * deriv (normalized head tail) z := by
        change deriv (fun w : ℂ => w ^ depth tail * normalized head tail w) z = _
        simpa only [Pi.mul_def, depth, Nat.add_sub_cancel] using
          ((hasDerivAt_pow (depth tail) z).mul (ha z hz).differentiableAt.hasDerivAt).deriv
      rw [hd]; dsimp [li, R, A, depth]
      field_simp [hz0, hn z hz]
      simp only [pow_succ]; ring
  refine ⟨(source_series head tail).2.2.1, ha,
    fun z hz => hn z (by simpa using hz), ?_, ?_⟩
  · apply AnalyticOnNhd.congr Metric.isOpen_ball
      (fun z hz => analyticAt_const.add
        ((analyticAt_id.mul (ha z hz).deriv).div (ha z hz) (hn z hz)))
    · intro z hz
      exact (hq z hz).symm
  · intro z hz
    rw [hq z (by simpa using hz)]
    exact (hall (head :: tail) z (by simpa using hz)).2.2 (by simp)
#print axioms result
end D5.S3.AnalyticClosure.Polylogarithm.CompositionZeroFree
