/- GID: D5/S3/Weil/Separator/OffLineZeroNegativeLiteralRationalEnergy
   generality: I
   mirror-B: D5/B/S3/Weil/Separator/OffLineZeroNegativeLiteralRationalEnergy
   mirror-E: none(waiver:analytic-erased-existence-without-numerical-extraction)
   anchors: []
   utility: none
   digest: An actual off-line zero produces a literal rational test with negative full energy. -/

import D5.S3.Weil.TestFunctions.RationalCutoffApproximation
import D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare
import D5.S3.Weil.Separator.UnconditionalExplicitFormula
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Separator.OffLineZeroNegativeLiteralRationalEnergy

open Set MeasureTheory Polynomial
open scoped ContDiff BigOperators ComplexConjugate
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.RationalCutoffApproximation
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.Convention
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.ConvolutionSquareOrbitBounds
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.OffLineNonrealZeroNegativeWeilSquare
open D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open D5.S3.Weil.BurnolGram.WeilMixedHeadTailBudget
open D5.S3.Weil.BurnolGram.ExplicitWeilFourthMomentTail
open D5.S3.Weil.Separator.OffLineZeroNegativeWeilSquare
open D5.S3.Weil.Separator.ArchimedeanConvergence
open D5.S3.Weil.ZetaBridge.PrimeArchimedeanEnergyIdentity
open D5.S3.Weil.ZetaBridge.PrimeJumpDecomposition
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

/-- A stored off-line zero yields a literal rational smooth-transition test
with negative complete paired zero sum and the same negative full energy.
The existential analytic construction makes no numerical extraction claim. -/
theorem offLineZero_yields_negative_literal_rational_energy
    (Z : ZeroData) (n : ℕ)
    (hOff : (Z.zero n).re ≠ criticalAbscissa) :
    ∃ R : ℕ, 0 < R ∧ ∃ p q : ℚ[X], ∃ h : WeilTestFunction,
      h.toFun = (fun x : ℝ =>
        (Real.smoothTransition (2 - |x| / (R : ℝ)) : ℂ) *
          rationalEvenPolynomial p q x) ∧
      tsupport (h : ℝ → ℂ) ⊆
        Icc (-(2 * (R : ℝ))) (2 * (R : ℝ)) ∧
      let hZero := symmetricConvergent_of_zeroData Z (convolutionSquare h)
      let E : ℝ :=
        2 * Complex.normSq
          (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * h x) +
        archimedeanJumpEnergy h +
        arithmeticJumpEnergy (2 * (R : ℝ)) h -
        (2 * totalPrimeWeight (2 * (R : ℝ)) - archimedeanConstant) *
          l2Mass h
      (zeroSum Z (convolutionSquare h) hZero).re < 0 ∧
        zeroSum Z (convolutionSquare h) hZero = (E : ℂ) ∧ E < 0 := by
  classical
  obtain ⟨g, hgZero, hgNegative⟩ := offLineZero_yields_negative_weil_square Z n hOff
  have hgneg :
      (zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z _)).re < 0 := by
    rw [zeroSum_eq_tsum_of_zeroData] at hgNegative ⊢
    exact hgNegative
  obtain ⟨L, hL⟩ := g.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨R, hRbound⟩ := exists_nat_gt (max L 0)
  have hRr : (0 : ℝ) < R := lt_of_le_of_lt (le_max_right L 0) hRbound
  have hR : 0 < R := Nat.cast_pos.mp hRr
  have hs : tsupport (g : ℝ → ℂ) ⊆ Icc (-(R : ℝ)) R := by
    intro x hx
    have hxs : x ∈ Icc (-L) L := by
      simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add] using hL hx
    have hLR : L < (R : ℝ) := lt_of_le_of_lt (le_max_left L 0) hRbound
    constructor <;> linarith [hxs.1, hxs.2]
  let χ : ℝ → ℝ := fun x => Real.smoothTransition (2 - |x| / (R : ℝ))
  let c : ℝ → ℂ := fun x => (χ x : ℂ)
  have hχ : ContDiff ℝ ∞ χ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hb := (ContDiffBumpBase.ofInnerProductSpace ℝ).smooth.contDiffAt
      (show Ioi (1 : ℝ) ×ˢ (univ : Set ℝ) ∈
        nhds ((2 : ℝ), x / (R : ℝ)) from
        prod_mem_nhds (Ioi_mem_nhds (by norm_num)) Filter.univ_mem)
    have ht := hb.comp x
      ((contDiffAt_const (c := (2 : ℝ))).prodMk
        ((contDiffAt_id (x := x)).div_const (R : ℝ)))
    change ContDiffAt ℝ ∞ (fun y : ℝ =>
      Real.smoothTransition (((2 : ℝ) - ‖y / (R : ℝ)‖) / (2 - 1))) x at ht
    simpa [χ, Real.norm_eq_abs,
      abs_div, abs_of_pos hRr, show (2 : ℝ) - 1 = 1 by norm_num] using ht
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp hχ
  let S := Icc (-(2 * R : ℝ)) (2 * R)
  have hcS : tsupport c ⊆ S := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hχne : χ x ≠ 0 := by intro hz; exact hx (by simp [c, hz])
    have hpos : 0 < 2 - |x| / (R : ℝ) := by
      by_contra hn
      exact hχne (Real.smoothTransition.zero_of_nonpos (le_of_not_gt hn))
    have hbound : |x| < 2 * (R : ℝ) := (div_lt_iff₀ hRr).mp (by linarith)
    exact abs_le.mp hbound.le
  have hcc : HasCompactSupport c :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hcS
  have hdensity (ε : ℝ) (hε : 0 < ε) :
      ∃ p q : ℚ[X], ∃ h : WeilTestFunction,
        h.toFun = (fun x : ℝ =>
          (Real.smoothTransition (2 - |x| / (R : ℝ)) : ℂ) *
            rationalEvenPolynomial p q x) ∧
        tsupport (h : ℝ → ℂ) ⊆ S ∧
        (∫ x : ℝ, ‖g x - h x‖) +
          (∫ x : ℝ, ‖deriv (deriv (fun y => g y - h y)) x‖) < ε := by
    have hc1 : ContDiff ℝ ∞ (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
    have hc2 : ContDiff ℝ ∞ (deriv (deriv c)) := (contDiff_infty_iff_deriv.mp hc1).2
    obtain ⟨C1, hC1⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
      hc1.continuous.continuousOn
    obtain ⟨C2, hC2⟩ := (isCompact_Icc : IsCompact S).exists_bound_of_continuousOn
      hc2.continuous.continuousOn
    let K : ℝ := 1 + |C1| + |C2|
    have hK : 0 < K := by dsimp [K]; positivity
    let η : ℝ := ε / (64 * R * K)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨p, hp⟩ := exists_rational_two_jet (fun x => (g x).re)
      (Complex.reCLM.contDiff.comp g.contDiff) (2 * R) η (by positivity) hη
    obtain ⟨q, hq⟩ := exists_rational_two_jet (fun x => (g x).im)
      (Complex.imCLM.contDiff.comp g.contDiff) (2 * R) η (by positivity) hη
    let F (p q : ℚ[X]) (x : ℝ) : ℂ := (aeval x p : ℝ) + Complex.I * (aeval x q : ℝ)
    have hFd (p q : ℚ[X]) (x : ℝ) :
        HasDerivAt (F p q) (F p.derivative q.derivative x) x := by
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (p.hasDerivAt_aeval x)).add
        ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x
          (q.hasDerivAt_aeval x)).const_mul Complex.I)
    have hFs : ContDiff ℝ ∞ (F p q) :=
      (Complex.ofRealCLM.contDiff.comp (p.contDiff_aeval ∞)).add
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (q.contDiff_aeval ∞)))
    let e : ℝ → ℂ := fun x => g x - F p q x
    have he : ContDiff ℝ ∞ e := g.contDiff.sub hFs
    have he1 : ContDiff ℝ ∞ (deriv e) := (contDiff_infty_iff_deriv.mp he).2
    have hg1 : ContDiff ℝ ∞ (deriv (g : ℝ → ℂ)) :=
      (contDiff_infty_iff_deriv.mp g.contDiff).2
    have hprojection (f : ℝ → ℂ) (hf : Differentiable ℝ f) (L : ℂ →L[ℝ] ℝ) :
        deriv (fun x => L (f x)) = fun x => L (deriv f x) := by
      funext x
      exact (L.hasFDerivAt.comp_hasDerivAt x (hf x).hasDerivAt).deriv
    have hproj0 := hprojection (g : ℝ → ℂ) (g.contDiff.differentiable (by simp))
    have hproj1 := hprojection (deriv (g : ℝ → ℂ)) (hg1.differentiable (by simp))
    have hed : deriv e = fun x => deriv (g : ℝ → ℂ) x - F p.derivative q.derivative x := by
      funext x
      exact ((g.contDiff.differentiable (by simp) x).hasDerivAt.sub (hFd p q x)).deriv
    have hedd : deriv (deriv e) = fun x =>
        deriv (deriv (g : ℝ → ℂ)) x -
          F p.derivative.derivative q.derivative.derivative x := by
      rw [hed]
      funext x
      exact ((hg1.differentiable (by simp) x).hasDerivAt.sub
        (hFd p.derivative q.derivative x)).deriv
    have hcomplex (z : ℂ) (a b : ℝ) (hr : ‖z.re - a‖ ≤ η) (hi : ‖z.im - b‖ ≤ η) :
        ‖z - ((a : ℂ) + Complex.I * b)‖ ≤ 2 * η := by
      have ht := Complex.norm_le_abs_re_add_abs_im (z - ((a : ℂ) + Complex.I * b))
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im,
        one_mul, zero_add] at ht
      rw [Real.norm_eq_abs] at hr hi
      linarith
    have hejets (x : ℝ) (hx : x ∈ S) :
        ‖e x‖ ≤ 2 * η ∧ ‖deriv e x‖ ≤ 2 * η ∧
          ‖deriv (deriv e) x‖ ≤ 2 * η := by
      obtain ⟨hp0, hp1, hp2⟩ := hp x hx
      obtain ⟨hq0, hq1, hq2⟩ := hq x hx
      have hr0 := hproj0 Complex.reCLM
      have hi0 := hproj0 Complex.imCLM
      have hr1 := hproj1 Complex.reCLM
      have hi1 := hproj1 Complex.imCLM
      simp only [Complex.reCLM_apply] at hr0 hr1
      simp only [Complex.imCLM_apply] at hi0 hi1
      rw [hr0] at hp1 hp2
      rw [hi0] at hq1 hq2
      rw [hr1] at hp2
      rw [hi1] at hq2
      exact ⟨hcomplex _ _ _ hp0 hq0,
        by rw [hed]; exact hcomplex _ _ _ hp1 hq1,
        by rw [hedd]; exact hcomplex _ _ _ hp2 hq2⟩
    let a : ℝ → ℂ := fun x => (e x + e (-x)) / 2
    have ha : ContDiff ℝ ∞ a := (he.add (he.comp contDiff_neg)).div_const 2
    have ha1 : deriv a = fun x => (deriv e x - deriv e (-x)) / 2 := by
      funext x
      exact (((he.differentiable (by simp) x).hasDerivAt.add
        (((he.differentiable (by simp) (-x)).hasDerivAt).scomp x
          (hasDerivAt_id x).neg)).div_const 2).deriv.trans (by simp only [neg_one_smul]; ring)
    have ha2 : deriv (deriv a) = fun x =>
        (deriv (deriv e) x + deriv (deriv e) (-x)) / 2 := by
      rw [ha1]
      funext x
      exact (((he1.differentiable (by simp) x).hasDerivAt.sub
        (((he1.differentiable (by simp) (-x)).hasDerivAt).scomp x
          (hasDerivAt_id x).neg)).div_const 2).deriv.trans (by simp only [neg_one_smul]; ring)
    have hajets (x : ℝ) (hx : x ∈ S) :
        ‖a x‖ ≤ 2 * η ∧ ‖deriv a x‖ ≤ 2 * η ∧
          ‖deriv (deriv a) x‖ ≤ 2 * η := by
      have hxneg : -x ∈ S := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      obtain ⟨he0, he1, he2⟩ := hejets x hx
      obtain ⟨hen0, hen1, hen2⟩ := hejets (-x) hxneg
      have hsum (u v : ℂ) (hu : ‖u‖ ≤ 2 * η) (hv : ‖v‖ ≤ 2 * η) :
          ‖(u + v) / 2‖ ≤ 2 * η := by
        rw [norm_div, Complex.norm_ofNat]
        exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          ((norm_add_le _ _).trans (by linarith))
      refine ⟨hsum _ _ he0 hen0, ?_, ?_⟩
      · simp only [ha1, sub_eq_add_neg]
        exact hsum _ _ he1 (by simpa using hen1)
      · rw [ha2]
        exact hsum _ _ he2 hen2
    have hcginv (x : ℝ) : c x * g x = g x := by
      by_cases hx : g x = 0
      · simp [hx]
      · have hxs := hs (subset_tsupport (g : ℝ → ℂ) hx)
        have hχ : χ x = 1 := Real.smoothTransition.one_of_one_le
          (by have ht := (div_le_one hRr).2 (abs_le.mpr hxs); linarith)
        simp [c, hχ]
    let h : WeilTestFunction :=
      { toFun := fun x : ℝ =>
          (Real.smoothTransition (2 - |x| / (R : ℝ)) : ℂ) *
            rationalEvenPolynomial p q x
        contDiff' := by
          apply hc.mul
          have hpoly (r : ℚ[X]) : ContDiff ℝ ∞ (fun x : ℝ =>
              ((aeval x r : ℝ) + aeval (-x) r) / 2) :=
            ((r.contDiff_aeval ∞).add ((r.contDiff_aeval ∞).comp contDiff_neg)).div_const 2
          exact (Complex.ofRealCLM.contDiff.comp (hpoly p)).add
            (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hpoly q)))
        hasCompactSupport' := hcc.mul_right
        even' := fun x => by simp [rationalEvenPolynomial, abs_neg, add_comm] }
    have hdiff : (fun x => g x - h x) = fun x => c x * a x := by
      funext x
      have hsym : a x = g x - rationalEvenPolynomial p q x := by
        dsimp [a, e, F, rationalEvenPolynomial]
        rw [g.even]
        push_cast
        ring
      rw [hsym, mul_sub, hcginv]
      rfl
    have hhs : tsupport (h : ℝ → ℂ) ⊆ S := by
      change tsupport (fun x => c x * rationalEvenPolynomial p q x) ⊆ S
      exact tsupport_mul_subset_left.trans hcS
    have hds : tsupport (fun x => g x - h x) ⊆ S := by
      rw [hdiff]
      exact tsupport_mul_subset_left.trans hcS
    have hdd : deriv (deriv (fun x => g x - h x)) = fun x =>
        deriv (deriv c) x * a x + 2 * deriv c x * deriv a x +
          c x * deriv (deriv a) x := by
      rw [hdiff]
      have hd : deriv (fun x => c x * a x) =
          fun x => deriv c x * a x + c x * deriv a x := by
        funext x
        exact ((hc.differentiable (by simp) x).hasDerivAt.mul
          (ha.differentiable (by simp) x).hasDerivAt).deriv
      rw [hd]
      have ha' : ContDiff ℝ ∞ (deriv a) := (contDiff_infty_iff_deriv.mp ha).2
      funext x
      exact (((hc1.differentiable (by simp) x).hasDerivAt.mul
        (ha.differentiable (by simp) x).hasDerivAt).add
        ((hc.differentiable (by simp) x).hasDerivAt.mul
          (ha'.differentiable (by simp) x).hasDerivAt)).deriv.trans (by ring)
    have hc0 (x : ℝ) : ‖c x‖ ≤ 1 := by
      simpa [c, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ χ x from Real.smoothTransition.nonneg _)] using
        (show χ x ≤ 1 from Real.smoothTransition.le_one _)
    have hc1K (x : ℝ) (hx : x ∈ S) : ‖deriv c x‖ ≤ K :=
      (hC1 x hx).trans (by dsimp [K]; linarith [le_abs_self C1, abs_nonneg C2])
    have hc2K (x : ℝ) (hx : x ∈ S) : ‖deriv (deriv c) x‖ ≤ K :=
      (hC2 x hx).trans (by dsimp [K]; linarith [le_abs_self C2, abs_nonneg C1])
    have hK1 : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg C1, abs_nonneg C2]
    have hv (x : ℝ) (hx : x ∈ S) : ‖g x - h x‖ ≤ 2 * K * η := by
      rw [congrFun hdiff x, norm_mul]
      calc
        _ ≤ K * (2 * η) := mul_le_mul ((hc0 x).trans hK1) (hajets x hx).1
          (norm_nonneg _) hK.le
        _ = _ := by ring
    have hsecond (x : ℝ) (hx : x ∈ S) :
        ‖deriv (deriv (fun y => g y - h y)) x‖ ≤ 8 * K * η := by
      rw [hdd]
      have ht := (norm_add_le (deriv (deriv c) x * a x + 2 * deriv c x * deriv a x)
        (c x * deriv (deriv a) x)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      simp only [norm_mul, Complex.norm_ofNat] at ht
      have hj := hajets x hx
      have h0 := mul_le_mul (hc2K x hx) hj.1 (norm_nonneg _) hK.le
      have h1 := mul_le_mul (hc1K x hx) hj.2.1 (norm_nonneg _) hK.le
      have h2 := mul_le_mul ((hc0 x).trans hK1) hj.2.2 (norm_nonneg _) hK.le
      nlinarith
    have lint (f : ℝ → ℂ) (hf : tsupport f ⊆ S) (A : ℝ)
        (hA : ∀ x ∈ S, ‖f x‖ ≤ A) : (∫ x : ℝ, ‖f x‖) ≤ 4 * R * A := by
      have heq : (∫ x in S, ‖f x‖) = ∫ x, ‖f x‖ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have hz : f x = 0 := by
            by_contra hn
            exact hx (hf (subset_tsupport f hn))
          simp [hz]
      rw [← heq]
      have hb := norm_setIntegral_le_of_norm_le_const
        (f := fun x => ‖f x‖) (isCompact_Icc.measure_lt_top : volume S < ⊤)
        (fun x hx => by simpa using hA x hx)
      have hvS : volume.real S = 4 * R := by
        change (volume (Icc (-(2 * (R : ℝ))) (2 * R))).toReal = _
        rw [Real.volume_Icc, ENNReal.toReal_ofReal
          (show 0 ≤ 2 * (R : ℝ) - -(2 * R) by linarith)]
        ring
      rw [hvS, Real.norm_eq_abs] at hb
      exact (le_abs_self _).trans (by nlinarith [hb])
    have hsecondS : tsupport (deriv (deriv (fun x => g x - h x))) ⊆ S :=
      tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hds)
    refine ⟨p, q, h, rfl, hhs, ?_⟩
    have hdcont : ContDiff ℝ ∞ (fun x => g x - h x) := g.contDiff.sub h.contDiff
    have hdcomp : HasCompactSupport (fun x => g x - h x) :=
      g.hasCompactSupport.sub h.hasCompactSupport
    have hdint : Integrable (fun x : ℝ => ‖g x - h x‖) :=
      hdcont.continuous.norm.integrable_of_hasCompactSupport hdcomp.norm
    have hd2int : Integrable (fun x : ℝ =>
        ‖deriv (deriv (fun y => g y - h y)) x‖) :=
      ((contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp hdcont).2).2.continuous.norm).integrable_of_hasCompactSupport
          hdcomp.deriv.deriv.norm
    have hb := add_le_add (lint _ hds _ hv) (lint _ hsecondS _ hsecond)
    have hstrict : 4 * (R : ℝ) * (2 * K * η) + 4 * R * (8 * K * η) < ε := by
      dsimp [η]
      field_simp
      nlinarith
    exact hb.trans_lt hstrict
  let ε : ℝ :=
    -(zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z _)).re / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let E := Z.symmetricIndices 6
  have htail := (zeroData_fourth_moment_tail_rational Z 5 (by decide) E
    (by norm_num [E])).1
  have hmoment : Summable (fourthMomentSummand Z) :=
    E.summable_compl_iff.mp htail
  let M : ℝ := ∑' n : ℕ, fourthMomentSummand Z n
  have hM : 0 ≤ M := tsum_nonneg fun n => by
    unfold fourthMomentSummand inverseQuadraticEnvelope
    positivity
  let Cg := closedStripJetBudget g (1 / 2)
  have hCg : 0 ≤ Cg := (closedStripJetBudget_spec g (1 / 2) (by norm_num)).1
  let A := Real.exp (R : ℝ)
  have hA : 0 < A := Real.exp_pos _
  let δ := min (ε / 2) (min (1 / (2 * A)) (ε / (2 * A * (2 * Cg + 1) * (M + 1))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 / (2 * A) := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ ε / (2 * A * (2 * Cg + 1) * (M + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  let Cd := A * δ
  have hCd : 0 ≤ Cd := by dsimp [Cd]; positivity
  have hCdHalf : Cd ≤ 1 / 2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hδ1
    dsimp [Cd]
    nlinarith
  have hsmall : Cd * (2 * Cg + Cd) * M < ε := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * A * (2 * Cg + 1) * (M + 1))).mp hδ2
    have hprod : Cd * (2 * Cg + Cd) * M ≤ Cd * (2 * Cg + 1) * (M + 1) := by
      gcongr <;> linarith
    apply hprod.trans_lt
    dsimp [Cd] at *
    nlinarith
  obtain ⟨p, q, h, hLiteral, hhS, hj⟩ := hdensity δ hδ
  let d : WeilTestFunction :=
    { toFun := fun x => g x - h x
      contDiff' := g.contDiff.sub h.contDiff
      hasCompactSupport' := g.hasCompactSupport.sub h.hasCompactSupport
      even' := fun x => by rw [g.even, h.even] }
  have hdS : tsupport (d : ℝ → ℂ) ⊆ Icc (-(2 * R : ℝ)) (2 * R) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_cases hg : g x = 0
    · have hh : h x ≠ 0 := by
        intro hz
        apply hx
        change g x - h x = 0
        rw [hg, hz, sub_self]
      exact hhS (subset_tsupport (h : ℝ → ℂ) hh)
    · have hb := hs (subset_tsupport (g : ℝ → ℂ) hg)
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) R, hb.1, hb.2]
  have hdBudget : closedStripJetBudget d (1 / 2) ≤ Cd := by
    have hb := closedStripJetBudget_le_support_jets d (2 * R) (1 / 2)
      (∫ x : ℝ, ‖d x‖) (∫ x : ℝ, ‖((deriv^[2]) (d : ℝ → ℂ)) x‖)
      (by norm_num) hdS le_rfl le_rfl
    have hj' : (∫ x : ℝ, ‖d x‖) +
        (∫ x : ℝ, ‖((deriv^[2]) (d : ℝ → ℂ)) x‖) ≤ δ := by
      change (∫ x : ℝ, ‖g x - h x‖) +
        (∫ x : ℝ, ‖deriv (deriv (fun y => g y - h y)) x‖) ≤ δ
      exact hj.le
    have hexp : Real.exp ((1 / 2 : ℝ) * (2 * R)) = A := by
      congr 1
      ring
    rw [hexp] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hj' hA.le)
  have htransform (z : ℂ) : fourierLaplace d z = fourierLaplace g z - fourierLaplace h z := by
    have hint (b : WeilTestFunction) : Integrable (fun x : ℝ => fourierKernel z x * b x) :=
      ((by unfold fourierKernel; fun_prop : Continuous (fourierKernel z)).mul
        b.continuous).integrable_of_hasCompactSupport b.hasCompactSupport.mul_left
    change (∫ x : ℝ, fourierKernel z x * d x) =
      (∫ x : ℝ, fourierKernel z x * g x) - ∫ x : ℝ, fourierKernel z x * h x
    rw [← integral_sub (hint g) (hint h)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      change fourierKernel z x * (g x - h x) =
        fourierKernel z x * g x - fourierKernel z x * h x
      ring)
  have hstrip (n : ℕ) : |(Z.gamma n).im| ≤ (1 / 2 : ℝ) := by
    rw [ZeroData.gamma, ← gammaOf_eq_spectralParameter]
    exact (Zeta23.WeilEF.abs_gammaOf_im_lt (Z.zero_isNontrivial n).2).le
  have hb (b : WeilTestFunction) (C : ℝ) (hC : closedStripJetBudget b (1 / 2) ≤ C)
      (n : ℕ) :
      ‖fourierLaplace b (Z.gamma n)‖ ≤ C * inverseQuadraticEnvelope Z n ∧
      ‖fourierLaplace b (conj (Z.gamma n))‖ ≤ C * inverseQuadraticEnvelope Z n := by
    have ht := (closedStripJetBudget_spec b (1 / 2) (by norm_num)).2
    have hden : 0 ≤ inverseQuadraticEnvelope Z n := by unfold inverseQuadraticEnvelope; positivity
    constructor
    · have hu : ‖fourierLaplace b (Z.gamma n)‖ ≤
          closedStripJetBudget b (1 / 2) * inverseQuadraticEnvelope Z n := by
        simpa only [inverseQuadraticEnvelope, div_eq_mul_inv] using
          (ht (Z.gamma n) (hstrip n))
      exact hu.trans (mul_le_mul_of_nonneg_right hC hden)
    · have hu : ‖fourierLaplace b (conj (Z.gamma n))‖ ≤
          closedStripJetBudget b (1 / 2) * inverseQuadraticEnvelope Z n := by
        simpa only [inverseQuadraticEnvelope, div_eq_mul_inv, Complex.conj_re] using
          (ht (conj (Z.gamma n)) (by simpa using hstrip n))
      exact hu.trans (mul_le_mul_of_nonneg_right hC hden)
  have hpoint (n : ℕ) :
      ‖zeroSummand Z (convolutionSquare g) n - zeroSummand Z (convolutionSquare h) n‖ ≤
        (Cd * (2 * Cg + Cd)) * fourthMomentSummand Z n := by
    let w := inverseQuadraticEnvelope Z n
    have hw : 0 ≤ w := by dsimp [w, inverseQuadraticEnvelope]; positivity
    have hg := hb g Cg le_rfl n
    have hd := hb d Cd hdBudget n
    rw [htransform, htransform] at hd
    have hh : ‖fourierLaplace h (Z.gamma n)‖ ≤ (Cg + Cd) * w := by
      have ht := norm_le_norm_add_norm_sub' (fourierLaplace h (Z.gamma n))
        (fourierLaplace g (Z.gamma n))
      rw [norm_sub_rev] at ht
      nlinarith [hg.1, hd.1]
    have hid :
        fourierLaplace g (Z.gamma n) * conj (fourierLaplace g (conj (Z.gamma n))) -
          fourierLaplace h (Z.gamma n) * conj (fourierLaplace h (conj (Z.gamma n))) =
        (fourierLaplace g (Z.gamma n) - fourierLaplace h (Z.gamma n)) *
          conj (fourierLaplace g (conj (Z.gamma n))) +
        fourierLaplace h (Z.gamma n) *
          conj (fourierLaplace g (conj (Z.gamma n)) - fourierLaplace h (conj (Z.gamma n))) := by
      rw [map_sub]
      ring
    simp only [zeroSummand, fourierLaplace_convolutionSquare_complex]
    rw [← mul_sub, norm_mul, Complex.norm_natCast, hid]
    have ht := norm_add_le
      ((fourierLaplace g (Z.gamma n) - fourierLaplace h (Z.gamma n)) *
        conj (fourierLaplace g (conj (Z.gamma n))))
      (fourierLaplace h (Z.gamma n) *
        conj (fourierLaplace g (conj (Z.gamma n)) - fourierLaplace h (conj (Z.gamma n))))
    simp only [norm_mul, Complex.norm_conj] at ht
    have hleft := mul_le_mul hd.1 hg.2 (norm_nonneg _) (mul_nonneg hCd hw)
    have hright := mul_le_mul hh hd.2 (norm_nonneg _) (mul_nonneg (add_nonneg hCg hCd) hw)
    calc
      _ ≤ (Z.multiplicity n : ℝ) *
          ((Cd * w) * (Cg * w) + ((Cg + Cd) * w) * (Cd * w)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact ht.trans (add_le_add hleft hright)
      _ = _ := by unfold fourthMomentSummand; dsimp [w]; ring
  have hgs := zeroSummand_summable_of_zeroData Z (convolutionSquare g)
  have hhs := zeroSummand_summable_of_zeroData Z (convolutionSquare h)
  have hsum :
      ‖zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z _) -
        zeroSum Z (convolutionSquare h) (symmetricConvergent_of_zeroData Z _)‖ ≤
          Cd * (2 * Cg + Cd) * M := by
    rw [zeroSum_eq_tsum_of_zeroData, zeroSum_eq_tsum_of_zeroData, ← hgs.tsum_sub hhs]
    calc
      _ ≤ ∑' n : ℕ, ‖zeroSummand Z (convolutionSquare g) n -
          zeroSummand Z (convolutionSquare h) n‖ := norm_tsum_le_tsum_norm (hgs.sub hhs).norm
      _ ≤ ∑' n : ℕ, (Cd * (2 * Cg + Cd)) * fourthMomentSummand Z n :=
        (hgs.sub hhs).norm.tsum_le_tsum hpoint (hmoment.mul_left _)
      _ = _ := tsum_mul_left
  have hnear := hsum.trans_lt hsmall
  have hnegative :
      (zeroSum Z (convolutionSquare h) (symmetricConvergent_of_zeroData Z _)).re < 0 := by
    have hre := Complex.re_le_norm
      (zeroSum Z (convolutionSquare h) (symmetricConvergent_of_zeroData Z _) -
        zeroSum Z (convolutionSquare g) (symmetricConvergent_of_zeroData Z _))
    rw [norm_sub_rev] at hre
    simp only [Complex.sub_re] at hre
    dsimp [ε] at hnear
    linarith
  let hZero := symmetricConvergent_of_zeroData Z (convolutionSquare h)
  let hArch := archimedeanConvergent_of_weilTestFunction (convolutionSquare h)
  have hidentity := (prime_archimedean_energy_identity Z h (2 * (R : ℝ)) hhS hZero hArch).1
  refine ⟨R, hR, p, q, h, hLiteral, hhS, hnegative, hidentity, ?_⟩
  have hre := congrArg Complex.re hidentity
  simp only [Complex.ofReal_re] at hre
  exact lt_of_eq_of_lt hre.symm hnegative

#print axioms offLineZero_yields_negative_literal_rational_energy

end D5.S3.Weil.Separator.OffLineZeroNegativeLiteralRationalEnergy
