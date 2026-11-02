/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelFiniteCodimension
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelFiniteCodimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.PSeries]
   utility: none
   digest: Complete actual-kernel coercivity and grouped-measure strictness after uniformly many ordinary atomic moments. -/

import D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.PSeries

/-!
SOURCE PREPARATION ONLY: this file has not been elaborated.

Canonical inputs: trureturing 6509238f4b736633f2995a759b89dde27dc8f5eb,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The two imported
preparatory bridges are source drafts, not verified dependencies. The remainder
draft also requires its supplied visibility-only mangoldtPart_eq_range patch.

The source clause is the existing AURIC prime-power difference coupling,
finite-codimension positivity and root Robin budget, Section 5, Theorem 2,
equations (17)--(20), and Appendix C. The public moment convention is
inclusive r≤N, as in the original statement.

Only one theorem is public. Its live proof includes the complete coefficient
series, a finite-prefix lower bound, harmonic growth and uniform moment-order
selection before the actual arithmetic remainder is subtracted, followed by
strictness for a genuinely nonzero grouped atomic measure. In particular no
infinite exchange involving trivialCoeff n * rate n is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
open MeasureTheory Set Filter
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Analytic.Interpolation.FiniteMomentCorrelation
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension

private def rate (n : ℕ) : ℝ := 2 * ((n : ℝ) + 1) + 1 / 2

private lemma rate_pos (n : ℕ) : 0 < rate n := by
  dsimp [rate]
  positivity

private def P (t : ℝ) : ℝ := Real.exp (-|t| / 2) * trivialT |t|

private def Q {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (f : ℝ → ℝ) : ℂ :=
  ∑ i, ∑ j, star (a i) * a j * (f (x i - x j) : ℂ)

private def E {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) : ℝ :=
  ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2

private lemma energy_nonneg {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) : 0 ≤ E x a :=
  integral_nonneg (fun _ => sq_nonneg _)

private lemma scalar_bound (n : ℕ) (t : ℝ) :
    |trivialCoeff n * Real.exp (-rate n * |t|)| ≤ trivialCoeff n := by
  rw [abs_of_nonneg (mul_nonneg (trivialCoeff_nonneg n) (Real.exp_nonneg _))]
  exact mul_le_of_le_one_right (trivialCoeff_nonneg n)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (rate_pos n).le) (abs_nonneg t)))

/- The original coefficient mass dominates the series also at t=0. -/
private lemma P_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => trivialCoeff n * Real.exp (-rate n * |t|)) (P t) := by
  have hs : Summable (fun n : ℕ => trivialCoeff n * Real.exp (-rate n * |t|)) := by
    apply Summable.of_norm_bounded trivialCoeff_hasSum.summable
    intro n
    rw [Real.norm_eq_abs]
    exact scalar_bound n t
  have he (n : ℕ) : trivialCoeff n * Real.exp (-rate n * |t|) =
      Real.exp (-|t| / 2) *
        (trivialCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * |t|)) := by
    calc
      _ = trivialCoeff n *
          Real.exp (-|t| / 2 + -(2 * ((n : ℝ) + 1)) * |t|) := by
        congr 2
        dsimp [rate]
        ring
      _ = _ := by rw [Real.exp_add]; ring
  have hv : (∑' n : ℕ, trivialCoeff n * Real.exp (-rate n * |t|)) = P t := by
    simp_rw [he]
    rw [tsum_mul_left]
    rfl
  simpa only [hv] using hs.hasSum

/- Absolute domination precedes the finite quadratic/series interchange.
For each pair i,j the majorant is norm(conj(a_i)*a_j) * trivialCoeff n.
The coefficients, rather than the divergent weighted rates, are summed. -/
private lemma quadratic_hasSum {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) :
    HasSum (fun n : ℕ => (trivialCoeff n : ℂ) *
      Q x a (fun t => Real.exp (-rate n * |t|))) (Q x a P) := by
  classical
  let f : I → I → ℕ → ℂ := fun i j n => star (a i) * a j *
    ((trivialCoeff n * Real.exp (-rate n * |x i - x j|) : ℝ) : ℂ)
  have hn (i j : I) : Summable (fun n : ℕ => ‖f i j n‖) := by
    apply Summable.of_norm_bounded
      (trivialCoeff_hasSum.summable.mul_left ‖star (a i) * a j‖)
    intro n
    rw [norm_norm]
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (scalar_bound n (x i - x j)) (norm_nonneg _)
  have hp (i j : I) : (∑' n : ℕ, f i j n) =
      star (a i) * a j * (P (x i - x j) : ℂ) := by
    exact ((Complex.hasSum_ofReal.mpr (P_hasSum (x i - x j))).mul_left
      (star (a i) * a j)).tsum_eq
  have hs : HasSum (fun n : ℕ => ∑ i, ∑ j, f i j n)
      (∑ i, ∑ j, ∑' n : ℕ, f i j n) :=
    hasSum_sum (fun i _ => hasSum_sum (fun j _ => (hn i j).of_norm.hasSum))
  have ht (n : ℕ) : (∑ i, ∑ j, f i j n) =
      (trivialCoeff n : ℂ) * Q x a (fun t => Real.exp (-rate n * |t|)) := by
    dsimp only [Q, f]
    simp only [Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hv : (∑ i, ∑ j, ∑' n : ℕ, f i j n) = Q x a P := by
    simp_rw [hp]
    rfl
  simpa only [ht, hv] using hs

private lemma diameter {I : Type u} [Fintype I]
    {D : ℝ} (x : I → ℝ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (i j : I) :
    |x i - x j| ≤ D := by
  apply abs_le.mpr
  constructor <;> linarith [(hx i).1, (hx i).2, (hx j).1, (hx j).2]

/- Tail positivity is obtained from the original exponential quadratics. It
does not require a termwise identity with a divergent weighted energy series. -/
private lemma finite_prefix_le {I : Type u} [Fintype I]
    (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) (J : ℕ) :
    (∑ n ∈ Finset.range J, trivialCoeff n *
      (Q x a (fun t => Real.exp (-rate n * |t|))).re) ≤ (Q x a P).re := by
  have hpos (n : ℕ) : 0 ≤ (Q x a (fun t => Real.exp (-rate n * |t|))).re := by
    have hb := exponential_prefix_coercivity x a ha (rate n) D
      (rate_pos n) hD (diameter x hx)
    have hzero : 0 ≤ 2 * rate n * Real.exp (-rate n * D) * E x a :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (rate_pos n).le)
        (Real.exp_nonneg _)) (energy_nonneg x a)
    exact hzero.trans hb
  have hs : HasSum (fun n : ℕ => trivialCoeff n *
      (Q x a (fun t => Real.exp (-rate n * |t|))).re) (Q x a P).re := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using Complex.hasSum_re (quadratic_hasSum x a)
  exact sum_le_hasSum (Finset.range J)
    (fun n _ => mul_nonneg (trivialCoeff_nonneg n) (hpos n)) hs

/- The witness is a grouped atomic mass: coincident indices are summed before
testing nonzero, so a nonzero coefficient vector with exact cancellation is
not accepted as a nonzero measure. -/
private def groupedMass {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, if x i = t then a i else 0

private theorem finite_node_gap {I : Type u} [Fintype I]
    (x : I → ℝ) (t : ℝ) (s : Finset I) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, x i ≠ t → δ ≤ |x i - t| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih
    by_cases hx : x i = t
    · refine ⟨δ, hδ, ?_⟩
      intro j hj hjt
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hjt hx).elim
      · exact hbound j hj hjt
    · refine ⟨min δ |x i - t|,
        lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr hx)), ?_⟩
      intro j hj hjt
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound j hj hjt)

private theorem prefix_right {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (t δ v : ℝ)
    (hgap : ∀ i, x i ≠ t → δ ≤ |x i - t|)
    (hv : t ≤ v ∧ v < t + δ) : «prefix» x a v = «prefix» x a t := by
  classical
  unfold «prefix»
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ≤ t
  · have hiv : x i ≤ v := hi.trans hv.1
    simp only [if_pos hi, if_pos hiv]
  · have hti : t < x i := lt_of_not_ge hi
    have hg := hgap i (ne_of_gt hti)
    rw [abs_of_pos (sub_pos.mpr hti)] at hg
    have hiv : ¬ x i ≤ v := by linarith [hv.2]
    simp only [if_neg hi, if_neg hiv]

private theorem prefix_zero_of_ae {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ)
    (hzero : (fun v : ℝ => ‖«prefix» x a v‖ ^ 2) =ᵐ[volume] 0) :
    ∀ t : ℝ, «prefix» x a t = 0 := by
  intro t
  obtain ⟨δ, hδ, hgap⟩ := finite_node_gap x t Finset.univ
  have hg : ∀ i, x i ≠ t → δ ≤ |x i - t| :=
    fun i => hgap i (Finset.mem_univ i)
  have hm : volume (Ioo t (t + δ)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  obtain ⟨v, hv, hvzero⟩ := exists_mem_of_measure_ne_zero_of_ae hm
    (ae_restrict_of_ae hzero)
  have heq := prefix_right x a t δ v hg ⟨hv.1.le, hv.2⟩
  have hnorm : ‖«prefix» x a v‖ = 0 := by
    change ‖«prefix» x a v‖ ^ 2 = 0 at hvzero
    nlinarith [norm_nonneg («prefix» x a v)]
  rw [← heq]
  exact norm_eq_zero.mp hnorm

private theorem mass_zero_of_prefix_zero {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ)
    (hzero : ∀ v : ℝ, «prefix» x a v = 0) (t : ℝ) :
    groupedMass x a t = 0 := by
  classical
  obtain ⟨δ, hδ, hgap⟩ := finite_node_gap x t Finset.univ
  let v := t - δ / 2
  have hv : t - δ < v ∧ v < t := by
    dsimp [v]
    constructor <;> linarith
  have hdiff : «prefix» x a t - «prefix» x a v = groupedMass x a t := by
    unfold «prefix» groupedMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases he : x i = t
    · have hiv : ¬ t ≤ v := not_le.mpr hv.2
      simp [he, hiv]
    · have hg := hgap i (Finset.mem_univ i) he
      by_cases hlt : x i < t
      · rw [abs_of_neg (sub_neg.mpr hlt)] at hg
        have hiv : x i ≤ v := by linarith [hv.1]
        simp [he, hlt.le, hiv]
      · have hgt : t < x i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
        have hit : ¬ x i ≤ t := not_le.mpr hgt
        have hiv : ¬ x i ≤ v := not_le.mpr (hv.2.trans hgt)
        simp [he, hit, hiv]
  rw [hzero t, hzero v, sub_self] at hdiff
  exact hdiff.symm

private theorem energy_pos_of_groupedMass {I : Type u} [Fintype I]
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (hmass : ∃ t : ℝ, groupedMass x a t ≠ 0) :
    0 < E x a := by
  classical
  have hfi := (shifted_hinge_prefix_energy x a ha 0).2.1
  have hnn : ∀ v : ℝ, 0 ≤ ‖«prefix» x a v‖ ^ 2 := fun v => sq_nonneg _
  by_contra hn
  have he : E x a = 0 := by
    dsimp only [E]
    exact le_antisymm (le_of_not_gt hn) (integral_nonneg hnn)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hfi).mp he
  have hp := prefix_zero_of_ae x a hae
  obtain ⟨t, ht⟩ := hmass
  exact ht (mass_zero_of_prefix_zero x a hp t)

private lemma weight_lower (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ 4 * (trivialCoeff n * rate n) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn' : 2 * ((n : ℝ) + 1) + 1 ≠ 0 := by positivity
  have hid : trivialCoeff n * rate n - 1 / (4 * ((n : ℝ) + 1)) =
      1 / (2 * (2 * ((n : ℝ) + 1) + 1)) := by
    dsimp only [trivialCoeff, rate]
    field_simp [hn, hn'] <;> ring
  have hpos : (0 : ℝ) ≤ 1 / (2 * (2 * ((n : ℝ) + 1) + 1)) := by positivity
  have hdiv : 4 * (1 / (4 * ((n : ℝ) + 1))) = 1 / ((n : ℝ) + 1) := by
    field_simp [hn] <;> ring
  nlinarith

private lemma exists_weight_prefix (B : ℝ) :
    ∃ J : ℕ, B ≤ ∑ n ∈ Finset.range J, trivialCoeff n * rate n := by
  have he : ∀ᶠ J : ℕ in atTop,
      4 * B ≤ ∑ n ∈ Finset.range J, (1 / ((n : ℝ) + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop.1 Real.tendsto_sum_range_one_div_nat_succ_atTop) (4 * B)
  obtain ⟨J, hJ⟩ := he.exists
  refine ⟨J, ?_⟩
  have hc : (∑ n ∈ Finset.range J, (1 / ((n : ℝ) + 1))) ≤
      4 * (∑ n ∈ Finset.range J, trivialCoeff n * rate n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n _ => weight_lower n)
  linarith

/- The bridge tolerance is 1/lam. Taking real parts of the exact prefix
identity gives Re Q_lam >= lam E. No division by E is used. -/
private lemma exponential_moment_lower (D : ℝ) (hD : 0 < D)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) →
      (∀ r : ℕ, r < N → ∑ i, a i * (x i : ℂ) ^ r = 0) →
      lam * E x a ≤ (Q x a (fun t => Real.exp (-lam * |t|))).re := by
  let w : ℝ → ℂ := fun s => (Real.exp (-lam * |s|) : ℂ)
  have hw : ContinuousOn w (Icc (-D) D) := by dsimp [w]; fun_prop
  obtain ⟨N, hN, hall⟩ := finite_moment_correlation.{u} D hD w hw
    (1 / lam) (one_div_pos.mpr hlam)
  refine ⟨N, hN, ?_⟩
  intro I inst x a hx hm
  have ha : ∑ i, a i = 0 := by
    simpa only [pow_zero, mul_one] using hm 0 (by omega)
  let C : ℝ → ℂ := fun s =>
    ∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v
  let W : ℂ := ∫ s in Icc (-D) D, w s * C s
  have hb : ‖W‖ ≤ (1 / lam) * E x a := hall x a hx hm
  have hr : W.re ≤ (1 / lam) * E x a := (Complex.re_le_norm W).trans hb
  have hi := (exponential_prefix_energy x a ha lam D hlam hD.le
    (diameter x hx)).2.2.2.2
  change Q x a (fun t => Real.exp (-lam * |t|)) =
    (2 * lam : ℂ) * (E x a : ℂ) - (lam ^ 2 : ℂ) * W at hi
  have hc : Q x a (fun t => Real.exp (-lam * |t|)) =
      ((2 * lam * E x a : ℝ) : ℂ) - ((lam ^ 2 : ℝ) : ℂ) * W := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat] using hi
  have hire : (Q x a (fun t => Real.exp (-lam * |t|))).re =
      2 * lam * E x a - lam ^ 2 * W.re := by
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using congrArg Complex.re hc
  have halg : lam ^ 2 * ((1 / lam) * E x a) = lam * E x a := by
    field_simp [hlam.ne'] <;> ring
  rw [hire]
  calc
    lam * E x a = 2 * lam * E x a - lam ^ 2 * ((1 / lam) * E x a) := by
      rw [halg]
      ring
    _ ≤ _ := sub_le_sub_left (mul_le_mul_of_nonneg_left hr (sq_nonneg lam)) _

/-- For every D>0 and kappa>0, one N>=1 works before every finite
universe-polymorphic atomic family in [0,D]. All ordinary moments r≤N vanish.
The kernel is the literal full actual arithmetic K and the right-hand side is
the Lebesgue energy of the endpoint-inclusive atomic prefix. Empty families,
repeated or unsorted nodes and zero energy are included. The second conjunct
is strict whenever the grouped finite atomic measure is nonzero; it does not
confuse a cancelling coefficient vector with a nonzero measure. -/
theorem actual_kernel_finite_codimension_coercivity
    (D : ℝ) (hD : 0 < D) (kappa : ℝ) (hkappa : 0 < kappa) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) →
      (∀ r : ℕ, r ≤ N → ∑ i, a i * (x i : ℂ) ^ r = 0) →
      kappa * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) ≤
          (∑ i, ∑ j, star (a i) * a j *
            (ActualKernelLocalPositivity.K (x i - x j) : ℂ)).re ∧
        ((∃ t : ℝ, (∑ i, if x i = t then a i else 0) ≠ 0) →
          0 < (∑ i, ∑ j, star (a i) * a j *
            (ActualKernelLocalPositivity.K (x i - x j) : ℂ)).re) := by
  classical
  obtain ⟨M, _hM, hrem⟩ := actual_remainder_prefix_bound.{u} D hD
  obtain ⟨J, hJ⟩ := exists_weight_prefix (kappa + M)
  have horders (n : Fin J) := exponential_moment_lower.{u} D hD (rate n) (rate_pos n)
  choose order _horder hlower using horders
  let N : ℕ := max 1 (Finset.univ.sup order)
  refine ⟨N, le_max_left _ _, ?_⟩
  intro I inst x a hx hm
  have hN : 1 ≤ N := le_max_left _ _
  have ha : ∑ i, a i = 0 := by
    simpa only [pow_zero, mul_one] using hm 0 (by omega)
  have hsmall (n : Fin J) : ∀ r : ℕ, r < order n →
      ∑ i, a i * (x i : ℂ) ^ r = 0 := by
    intro r hr
    have hn : order n ≤ N :=
      (Finset.le_sup (f := order) (Finset.mem_univ n)).trans (le_max_right _ _)
    exact hm r ((Nat.le_of_lt hr).trans hn)
  have hprefix : (kappa + M) * E x a ≤
      ∑ n ∈ Finset.range J, trivialCoeff n *
        (Q x a (fun t => Real.exp (-rate n * |t|))).re := by
    calc
      _ ≤ (∑ n ∈ Finset.range J, trivialCoeff n * rate n) * E x a :=
        mul_le_mul_of_nonneg_right hJ (energy_nonneg x a)
      _ = ∑ n ∈ Finset.range J, trivialCoeff n * (rate n * E x a) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        let nJ : Fin J := ⟨n, Finset.mem_range.mp hn⟩
        exact mul_le_mul_of_nonneg_left (hlower nJ x a hx (hsmall nJ))
          (trivialCoeff_nonneg n)
  have hP : (kappa + M) * E x a ≤ (Q x a P).re :=
    hprefix.trans (finite_prefix_le D hD.le x a hx ha J)
  have hR : ‖Q x a (fun t => ActualKernelLocalPositivity.K t - P t)‖ ≤ M * E x a :=
    hrem x a hx ha
  have hRlower : -(M * E x a) ≤
      (Q x a (fun t => ActualKernelLocalPositivity.K t - P t)).re := by
    have hh := (Complex.re_le_norm
      (-Q x a (fun t => ActualKernelLocalPositivity.K t - P t))).trans
        (by simpa only [norm_neg] using hR)
    simp only [Complex.neg_re] at hh
    linarith
  have hsplit : Q x a ActualKernelLocalPositivity.K = Q x a P +
      Q x a (fun t => ActualKernelLocalPositivity.K t - P t) := by
    simp only [Q, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  have hfinal : kappa * E x a ≤ (Q x a ActualKernelLocalPositivity.K).re := by
    change kappa * E x a ≤ (Q x a ActualKernelLocalPositivity.K).re
    rw [hsplit, Complex.add_re]
    nlinarith
  refine ⟨hfinal, ?_⟩
  intro hmass
  have hmass' : ∃ t : ℝ, groupedMass x a t ≠ 0 := by
    simpa only [groupedMass] using hmass
  have hEpos : 0 < E x a := energy_pos_of_groupedMass x a ha hmass'
  have hpositive : 0 < kappa * E x a := mul_pos hkappa hEpos
  exact hpositive.trans_le hfinal

#print axioms actual_kernel_finite_codimension_coercivity

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelFiniteCodimension
end
