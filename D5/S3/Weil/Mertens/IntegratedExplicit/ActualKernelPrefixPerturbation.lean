/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelPrefixPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform actual arithmetic remainder bound by finite atomic prefix energy. -/

import D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

/-!
Source clause: the AURIC prime-power difference coupling and root Robin budget volume,
Section 5, Theorem 2, first step, equation (19), and Appendix C.
The proof replaces the signed-measure argument there by finitely many ordinary
FTC identities and the published shifted-hinge/prefix theorem. No cutoff of the
arithmetic series is made outside the fixed compact window.

The auxiliary declarations are consumed by the explicit finite-cost theorem.
The original existential bound is its direct consequence.
The remainder in that theorem is literally K minus the COMPLETE trivial-zero
kernel. It is not `ActualKernelCusp.R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
open MeasureTheory Set
open scoped BigOperators
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation

variable {I : Type u} [Fintype I]

private def Q (x : I → ℝ) (a : I → ℂ) (f : ℝ → ℝ) : ℂ :=
  ∑ i, ∑ j, star (a i) * a j * (f (x i - x j) : ℂ)

private def E (x : I → ℝ) (a : I → ℂ) : ℝ :=
  ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2

private lemma Q_congr (x : I → ℝ) (a : I → ℂ) {f g : ℝ → ℝ}
    (h : ∀ i j, f (x i - x j) = g (x i - x j)) : Q x a f = Q x a g := by
  classical
  unfold Q
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h i j]

private lemma Q_add (x : I → ℝ) (a : I → ℂ) (f g : ℝ → ℝ) :
    Q x a (fun t => f t + g t) = Q x a f + Q x a g := by
  simp only [Q, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

private lemma Q_scale (x : I → ℝ) (a : I → ℂ) (c : ℝ) (f : ℝ → ℝ) :
    Q x a (fun t => c * f t) = (c : ℂ) * Q x a f := by
  classical
  simp only [Q, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma Q_sum (x : I → ℝ) (a : I → ℂ) (S : Finset ℕ)
    (f : ℕ → ℝ → ℝ) :
    Q x a (fun t => ∑ n ∈ S, f n t) = ∑ n ∈ S, Q x a (f n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Q]
  | @insert n S hn ih =>
    simp only [Finset.sum_insert hn]
    rw [Q_add, ih]

private lemma Q_constant (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (c : ℝ) : Q x a (fun _ => c) = 0 := by
  classical
  unfold Q
  have hz (i : I) : (∑ j, star (a i) * a j * (c : ℂ)) = 0 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, ha, mul_zero, zero_mul]
  simp only [hz, Finset.sum_const_zero]

private def H (s t : ℝ) : ℝ := max (|t| - s) 0

private lemma abs_hinge_split (s t : ℝ) (hs : 0 ≤ s) :
    H s t = max (t - s) 0 + max (-t - s) 0 := by
  rcases le_total 0 t with ht | ht
  · rw [H, abs_of_nonneg ht, max_eq_right (by linarith : -t - s ≤ 0), add_zero]
  · rw [H, abs_of_nonpos ht, max_eq_right (by linarith : t - s ≤ 0), zero_add]

private lemma reverse_hinge (x : I → ℝ) (a : I → ℂ) (s : ℝ) :
    Q x a (fun t => max (-t - s) 0) =
      star (Q x a (fun t => max (t - s) 0)) := by
  classical
  unfold Q
  rw [Finset.sum_comm]
  simp only [star_sum, star_mul, Complex.star_def,
    Complex.conj_ofReal, starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show -(x j - x i) - s = x i - x j - s by ring]
  ring

private lemma hinge_bound (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) {s : ℝ} (hs : 0 ≤ s) :
    ‖Q x a (H s)‖ ≤ 2 * E x a := by
  have hb : ‖Q x a (fun t => max (t - s) 0)‖ ≤ E x a :=
    (shifted_hinge_prefix_energy x a ha s).2.2.2
  have he : Q x a (H s) = Q x a (fun t => max (t - s) 0) +
      star (Q x a (fun t => max (t - s) 0)) := by
    calc
      _ = Q x a (fun t => max (t - s) 0 + max (-t - s) 0) :=
        Q_congr x a (fun i j => abs_hinge_split s _ hs)
      _ = _ := by rw [Q_add, reverse_hinge]
  rw [he]
  calc
    _ ≤ ‖Q x a (fun t => max (t - s) 0)‖ +
        ‖star (Q x a (fun t => max (t - s) 0))‖ := norm_add_le _ _
    _ ≤ 2 * E x a := by rw [norm_star]; linarith

/- Two ordinary FTC applications are combined into one explicit primitive.
No derivative is taken through a corner. The clipping is introduced afterwards. -/
private lemma taylor_integral (f f₁ f₂ : ℝ → ℝ)
    (hf : ∀ s, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s, HasDerivAt f₁ (f₂ s) s) (hc : Continuous f₂)
    (l r : ℝ) :
    (∫ s in l..r, (r - s) * f₂ s) = f r - f l - (r - l) * f₁ l := by
  have hd (s : ℝ) : HasDerivAt
      (fun v => (r - v) * f₁ v + f v) ((r - s) * f₂ s) s := by
    convert ((((hasDerivAt_const s r).sub (hasDerivAt_id s)).mul
      (hf₁ s)).add (hf s)) using 1
    · rfl
    · dsimp
      ring
  have hi : IntervalIntegrable (fun s => (r - s) * f₂ s) volume l r :=
    ((continuous_const.sub continuous_id).mul hc).intervalIntegrable l r
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hi
  calc
    _ = (r - r) * f₁ r + f r - ((r - l) * f₁ l + f l) := ht
    _ = _ := by ring

private def clipped (l : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if l ≤ |t| then f |t| else 0

private lemma clipped_representation (f f₁ f₂ : ℝ → ℝ)
    (hf : ∀ s, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s, HasDerivAt f₁ (f₂ s) s) (hc : Continuous f₂)
    (l D : ℝ) (hlD : l ≤ D) (hzero : f l = 0)
    {t : ℝ} (ht : |t| ≤ D) :
    clipped l f t = f₁ l * H l t + ∫ s in Icc l D, H s t * f₂ s := by
  let g : ℝ → ℝ := fun s => H s t * f₂ s
  have hg : Continuous g := by dsimp [g, H]; fun_prop
  have hw : (∫ s in Icc l D, g s) = ∫ s in l..D, g s := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hlD]
  by_cases hlt : l ≤ |t|
  · have htail : (∫ s in |t|..D, g s) = 0 := by
      calc
        _ = ∫ s in |t|..D, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le ht] at hs
          dsimp [g, H]
          rw [max_eq_right (by linarith [hs.1] : |t| - s ≤ 0), zero_mul]
        _ = 0 := by simp
    have htrunc : (∫ s in l..D, g s) = ∫ s in l..|t|, g s := by
      have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (hg.intervalIntegrable l |t|) (hg.intervalIntegrable |t| D)
      rw [htail, add_zero] at h
      exact h.symm
    have hleft : (∫ s in l..|t|, g s) = ∫ s in l..|t|, (|t| - s) * f₂ s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hlt] at hs
      dsimp [g, H]
      rw [max_eq_left (by linarith [hs.2] : 0 ≤ |t| - s)]
    change clipped l f t = f₁ l * H l t + ∫ s in Icc l D, g s
    rw [clipped, ite_eq_left hlt, H, max_eq_left (sub_nonneg.mpr hlt),
      hw, htrunc, hleft, taylor_integral f f₁ f₂ hf hf₁ hc l |t|, hzero]
    ring
  · have hz : (∫ s in Icc l D, g s) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro s hs
      dsimp [g, H]
      rw [max_eq_right (by linarith [hs.1] : |t| - s ≤ 0), zero_mul]
    change clipped l f t = f₁ l * H l t + ∫ s in Icc l D, g s
    rw [clipped, ite_eq_right hlt, H, max_eq_right (by linarith : |t| - l ≤ 0),
      mul_zero, hz, add_zero]

private lemma Q_integral (x : I → ℝ) (a : I → ℂ)
    (l D : ℝ) (w : ℝ → ℝ) (hw : Continuous w) :
    Q x a (fun t => ∫ s in Icc l D, H s t * w s) =
      ∫ s in Icc l D, (w s : ℂ) * Q x a (H s) := by
  classical
  have hi (i j : I) : IntegrableOn
      (fun s : ℝ => star (a i) * a j * ((H s (x i - x j) * w s : ℝ) : ℂ))
      (Icc l D) := by
    apply Continuous.integrableOn_Icc
    dsimp [H]
    fun_prop
  have hcast (i j : I) :
      ((∫ s in Icc l D, H s (x i - x j) * w s : ℝ) : ℂ) =
        ∫ s in Icc l D, ((H s (x i - x j) * w s : ℝ) : ℂ) :=
    integral_complex_ofReal.symm
  calc
    _ = ∑ i, ∑ j, ∫ s in Icc l D,
        star (a i) * a j * ((H s (x i - x j) * w s : ℝ) : ℂ) := by
      unfold Q
      simp_rw [hcast, ← integral_const_mul]
    _ = ∫ s in Icc l D, ∑ i, ∑ j,
        star (a i) * a j * ((H s (x i - x j) * w s : ℝ) : ℂ) := by
      symm
      rw [integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi i j)]
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun s => by
        dsimp only [Q]
        simp only [Finset.mul_sum, Complex.ofReal_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring)

private lemma integral_hinge_bound (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (l D : ℝ) (hl : 0 ≤ l)
    (w : ℝ → ℝ) (hw : Continuous w) :
    ‖Q x a (fun t => ∫ s in Icc l D, H s t * w s)‖ ≤
      2 * (∫ s in Icc l D, |w s|) * E x a := by
  have hc : Continuous (fun s : ℝ => (w s : ℂ) * Q x a (H s)) := by
    dsimp [Q, H]
    fun_prop
  have hb : Continuous (fun s : ℝ => |w s| * (2 * E x a)) := by fun_prop
  rw [Q_integral x a l D w hw]
  calc
    _ ≤ ∫ s in Icc l D, ‖(w s : ℂ) * Q x a (H s)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Icc l D, |w s| * (2 * E x a) := by
      apply integral_mono_ae hc.integrableOn_Icc.norm hb.integrableOn_Icc
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hinge_bound x a ha (hl.trans hs.1)) (abs_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

private lemma clipped_bound (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) (D : ℝ) (hx : ∀ i j, |x i - x j| ≤ D)
    (f f₁ f₂ : ℝ → ℝ) (hf : ∀ s, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s, HasDerivAt f₁ (f₂ s) s) (hc : Continuous f₂)
    (l : ℝ) (hl : 0 ≤ l) (hlD : l ≤ D) (hzero : f l = 0) :
    ‖Q x a (clipped l f)‖ ≤
      (2 * (|f₁ l| + ∫ s in Icc l D, |f₂ s|)) * E x a := by
  have hr : Q x a (clipped l f) =
      Q x a (fun t => f₁ l * H l t + ∫ s in Icc l D, H s t * f₂ s) :=
    Q_congr x a (fun i j =>
    clipped_representation f f₁ f₂ hf hf₁ hc l D hlD hzero (hx i j))
  rw [hr, Q_add, Q_scale]
  calc
    _ ≤ ‖(f₁ l : ℂ) * Q x a (H l)‖ +
        ‖Q x a (fun t => ∫ s in Icc l D, H s t * f₂ s)‖ := norm_add_le _ _
    _ ≤ |f₁ l| * (2 * E x a) + 2 * (∫ s in Icc l D, |f₂ s|) * E x a := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hinge_bound x a ha hl) (abs_nonneg _)
      · exact integral_hinge_bound x a ha l D hl f₂ hc
    _ = _ := by ring

private def base (r : ℝ) : ℝ :=
  Real.exp (r / 2) * (1 + Real.eulerMascheroniConstant - r) -
    Real.log (2 * Real.pi) * Real.exp (-r / 2)

private def base₁ (r : ℝ) : ℝ :=
  Real.exp (r / 2) * ((1 + Real.eulerMascheroniConstant - r) / 2 - 1) +
    Real.log (2 * Real.pi) * Real.exp (-r / 2) / 2

private def base₂ (r : ℝ) : ℝ := base r / 4 - Real.exp (r / 2)

private lemma base_deriv (r : ℝ) : HasDerivAt base (base₁ r) r := by
  convert ((((hasDerivAt_id r).div_const 2).exp.mul
    ((hasDerivAt_const r (1 + Real.eulerMascheroniConstant)).sub (hasDerivAt_id r))).sub
      ((((hasDerivAt_id r).neg.div_const 2).exp).const_mul (Real.log (2 * Real.pi))))
    using 1
  · rfl
  · dsimp [base₁]
    ring

private lemma base₁_deriv (r : ℝ) : HasDerivAt base₁ (base₂ r) r := by
  convert ((((hasDerivAt_id r).div_const 2).exp.mul
    ((((hasDerivAt_const r (1 + Real.eulerMascheroniConstant)).sub
      (hasDerivAt_id r)).div_const 2).sub_const 1)).add
      (((((hasDerivAt_id r).neg.div_const 2).exp).const_mul
        (Real.log (2 * Real.pi))).div_const 2)) using 1
  · rfl
  · dsimp [base₁, base₂, base]
    ring

private def smooth (n : ℕ) (r : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (Real.exp (r / 2) / (n : ℝ) - Real.exp (-r / 2))

private def smooth₁ (n : ℕ) (r : ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    (Real.exp (r / 2) / (n : ℝ) + Real.exp (-r / 2)) / 2

private def smooth₂ (n : ℕ) (r : ℝ) : ℝ := smooth n r / 4

private lemma smooth_deriv (n : ℕ) (r : ℝ) :
    HasDerivAt (smooth n) (smooth₁ n r) r := by
  convert (((((hasDerivAt_id r).div_const 2).exp).div_const (n : ℝ)).sub
    (((hasDerivAt_id r).neg.div_const 2).exp)).const_mul
      (ArithmeticFunction.vonMangoldt n) using 1
  · rfl
  · dsimp [smooth₁]
    ring

private lemma smooth₁_deriv (n : ℕ) (r : ℝ) :
    HasDerivAt (smooth₁ n) (smooth₂ n r) r := by
  convert (((((((hasDerivAt_id r).div_const 2).exp).div_const (n : ℝ)).add
    (((hasDerivAt_id r).neg.div_const 2).exp)).const_mul
      (ArithmeticFunction.vonMangoldt n)).div_const 2) using 1
  · rfl
  · dsimp [smooth₁, smooth₂, smooth]
    ring

private lemma damping (n : ℕ) (r : ℝ) :
    Real.exp (-r / 2) *
      (ArithmeticFunction.vonMangoldt n * (Real.exp r / (n : ℝ) - 1)) = smooth n r := by
  have he : Real.exp (-r / 2) * Real.exp r = Real.exp (r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [smooth]
  calc
    _ = ArithmeticFunction.vonMangoldt n *
        ((Real.exp (-r / 2) * Real.exp r) / (n : ℝ) - Real.exp (-r / 2)) := by ring
    _ = _ := by rw [he]

private lemma smooth_entry (n : ℕ) (hn : 2 ≤ n) : smooth n (Real.log n) = 0 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [← damping, Real.exp_log hp, div_self hp.ne']
  ring

private lemma damped_ramp (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    Real.exp (-|t| / 2) * mangoldtRamp n (Real.exp |t|) =
      clipped (Real.log n) (smooth n) t := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  by_cases h : Real.log (n : ℝ) ≤ |t|
  · have he : (n : ℝ) ≤ Real.exp |t| := by
      rw [← Real.exp_log hp]
      exact Real.exp_le_exp.mpr h
    rw [clipped, ite_eq_left h, mangoldtRamp,
      max_eq_left (by have := (one_le_div hp).mpr he; linarith)]
    exact damping n |t|
  · have he : Real.exp |t| < (n : ℝ) := by
      rw [← Real.exp_log hp]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge h)
    rw [clipped, ite_eq_right h, mangoldtRamp,
      max_eq_right (by have := (div_lt_one hp).mpr he; linarith), mul_zero, mul_zero]

private def active (D : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => 2 ≤ n ∧ Real.log (n : ℝ) ≤ D)

private def remainder (t : ℝ) : ℝ :=
  ActualKernelLocalPositivity.K t - Real.exp (-|t| / 2) * trivialT |t|

private lemma local_remainder (D : ℝ) (N : ℕ) (hN : Real.exp D < N)
    {t : ℝ} (ht : |t| ≤ D) :
    remainder t = base |t| + ∑ n ∈ active D N, clipped (Real.log n) (smooth n) t := by
  have he : Real.exp |t| < (N : ℝ) := (Real.exp_le_exp.mpr ht).trans_lt hN
  have hs : (∑ n ∈ Finset.range N, Real.exp (-|t| / 2) *
      mangoldtRamp n (Real.exp |t|)) =
        ∑ n ∈ active D N, clipped (Real.log n) (smooth n) t := by
    classical
    rw [active, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : 2 ≤ n
    · rw [damped_ramp n hn]
      by_cases hlog : Real.log (n : ℝ) ≤ D
      · rw [ite_eq_left ⟨hn, hlog⟩]
      · rw [ite_eq_right (by simp [hlog]), clipped,
          ite_eq_right (by intro h; exact hlog (h.trans ht))]
    · have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl <;> simp [mangoldtRamp]
  have hexp : Real.exp (-|t| / 2) * Real.exp |t| = Real.exp (|t| / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only [remainder, ActualKernelLocalPositivity.K]
  rw [U_eq_complete_ramps (Real.exp_nonneg _), Real.log_exp,
    mangoldtPart_eq_range (Real.exp_nonneg _) he]
  calc
    _ = (Real.exp (-|t| / 2) * Real.exp |t|) *
        (1 + Real.eulerMascheroniConstant - |t|) -
        Real.log (2 * Real.pi) * Real.exp (-|t| / 2) +
        ∑ n ∈ Finset.range N, Real.exp (-|t| / 2) * mangoldtRamp n (Real.exp |t|) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rw [hexp, hs]; rfl

private def cost (f₁ f₂ : ℝ → ℝ) (l D : ℝ) : ℝ :=
  2 * (|f₁ l| + ∫ s in Icc l D, |f₂ s|)

private lemma cost_nonneg (f₁ f₂ : ℝ → ℝ) (l D : ℝ) :
    0 ≤ cost f₁ f₂ l D :=
  mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (integral_nonneg (fun _ => abs_nonneg _)))

private lemma base_bound (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hD : 0 ≤ D) (hx : ∀ i j, |x i - x j| ≤ D) :
    ‖Q x a (fun t => base |t|)‖ ≤ cost base₁ base₂ 0 D * E x a := by
  let f : ℝ → ℝ := fun r => base r - base 0
  have hrep : Q x a (fun t => base |t|) = Q x a (clipped 0 f) := by
    calc
      _ = Q x a (fun t => base 0 + clipped 0 f t) := by
        apply Q_congr x a
        intro i j
        rw [clipped, ite_eq_left (abs_nonneg (x i - x j))]
        dsimp [f]
        ring
      _ = _ := by rw [Q_add, Q_constant x a ha, zero_add]
  rw [hrep]
  exact clipped_bound x a ha D hx f base₁ base₂
    (fun r => (base_deriv r).sub_const _) base₁_deriv
    (by
      change Continuous (fun r : ℝ =>
        (Real.exp (r / 2) * (1 + Real.eulerMascheroniConstant - r) -
          Real.log (2 * Real.pi) * Real.exp (-r / 2)) / 4 - Real.exp (r / 2))
      fun_prop) 0 le_rfl hD (by simp [f])

/-- The finite component-curvature cost used by the proof.  The index N is
chosen after D and before the atomic data; no atom-dependent quantity occurs. -/
def finite_curvature_cost (D : ℝ) (N : ℕ) : ℝ :=
  cost base₁ base₂ 0 D +
    ∑ n ∈ active D N, cost (smooth₁ n) (smooth₂ n) (Real.log n) D

/-- The complete literal remainder has the exact finite component-curvature
bound supplied by the proof.  This is a constructive strengthening of the
existential statement below; it does not identify component curvature with
any total-variation norm. -/
theorem actual_remainder_prefix_bound_with_finite_cost (D : ℝ) (hD : 0 < D)
    (N : ℕ) (hN : Real.exp D < N) :
    0 ≤ finite_curvature_cost D N ∧ ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) → (∑ i, a i = 0) →
      ‖∑ i, ∑ j, star (a i) * a j *
        ((ActualKernelLocalPositivity.K (x i - x j) -
          Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)‖ ≤
        finite_curvature_cost D N * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) := by
  classical
  let S : Finset ℕ := active D N
  refine ⟨add_nonneg (cost_nonneg _ _ _ _)
    (Finset.sum_nonneg (fun n _ => cost_nonneg _ _ _ _)), ?_⟩
  intro I inst x a hx ha
  have hdiam (i j : I) : |x i - x j| ≤ D := by
    apply abs_le.mpr
    constructor <;> linarith [(hx i).1, (hx i).2, (hx j).1, (hx j).2]
  have hsplit : Q x a remainder = Q x a (fun t => base |t|) +
      ∑ n ∈ S, Q x a (clipped (Real.log n) (smooth n)) := by
    calc
      _ = Q x a (fun t => base |t| + ∑ n ∈ S, clipped (Real.log n) (smooth n) t) :=
        Q_congr x a (fun i j => local_remainder D N hN (hdiam i j))
      _ = _ := by rw [Q_add, Q_sum]
  have hterms (n : ℕ) (hn : n ∈ S) :
      ‖Q x a (clipped (Real.log n) (smooth n))‖ ≤
        cost (smooth₁ n) (smooth₂ n) (Real.log n) D * E x a := by
    have hm : 2 ≤ n ∧ Real.log (n : ℝ) ≤ D := (Finset.mem_filter.mp hn).2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    exact clipped_bound x a ha D hdiam (smooth n) (smooth₁ n) (smooth₂ n)
      (smooth_deriv n) (smooth₁_deriv n) (by
        change Continuous (fun r : ℝ => ArithmeticFunction.vonMangoldt n *
          (Real.exp (r / 2) / (n : ℝ) - Real.exp (-r / 2)) / 4)
        fun_prop)
      (Real.log n) (Real.log_nonneg hn1) hm.2 (smooth_entry n hm.1)
  change ‖Q x a remainder‖ ≤ finite_curvature_cost D N * E x a
  rw [hsplit]
  calc
    _ ≤ ‖Q x a (fun t => base |t|)‖ +
        ‖∑ n ∈ S, Q x a (clipped (Real.log n) (smooth n))‖ := norm_add_le _ _
    _ ≤ cost base₁ base₂ 0 D * E x a +
        ∑ n ∈ S, cost (smooth₁ n) (smooth₂ n) (Real.log n) D * E x a := by
      apply add_le_add (base_bound x a ha D hD.le hdiam)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterms)
    _ = finite_curvature_cost D N * E x a := by
      dsimp only [finite_curvature_cost]; rw [add_mul, Finset.sum_mul]

/-- For every real D>0, a finite nonnegative real M is chosen BEFORE the finite
index type, its universe-polymorphic atoms, nodes and coefficients. The literal
complete trivial-zero kernel is subtracted from the literal actual K. No moment
condition other than zero total mass is assumed; the atomic prefix includes its
endpoint. This statement alone asserts no PSD, finite-codimension positivity or RH. -/
theorem actual_remainder_prefix_bound (D : ℝ) (hD : 0 < D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {I : Type u} [Fintype I]
      (x : I → ℝ) (a : I → ℂ),
      (∀ i, x i ∈ Icc (0 : ℝ) D) → (∑ i, a i = 0) →
      ‖∑ i, ∑ j, star (a i) * a j *
        ((ActualKernelLocalPositivity.K (x i - x j) -
          Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)‖ ≤
        M * (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp D)
  obtain ⟨hM, hbound⟩ := actual_remainder_prefix_bound_with_finite_cost D hD N hN
  exact ⟨finite_curvature_cost D N, hM, hbound⟩

/- Source-only extension, 2026-11-03. Original declarations above are
   unchanged. The actual distribution/correlation formula is proved by
   consuming the owner's private FTC and clipped-ramp identities. -/

private def actualCorr (x : I → ℝ) (a : I → ℂ) (s : ℝ) : ℝ :=
  (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re

private lemma corr_continuous (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0) :
    Continuous (actualCorr x a) := by
  have he (s : ℝ) : actualCorr x a s =
      -(Q x a (fun t => max (t - s) 0)).re := by
    have h := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
    dsimp [actualCorr, Q] at *
    linarith only [h]
  have heq : actualCorr x a = fun s => -(Q x a (fun t => max (t - s) 0)).re :=
    funext he
  rw [heq]
  dsimp [Q]
  fun_prop

private lemma corr_at_zero (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0) :
    actualCorr x a 0 = E x a := by
  have hi := (shifted_hinge_prefix_energy x a ha 0).1
  change (∫ v : ℝ, star («prefix» x a (v + 0)) * «prefix» x a v).re =
    ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [← hre]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    simp only [add_zero]
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq])

private lemma hinge_corr (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (s : ℝ) (hs : 0 ≤ s) : (Q x a (H s)).re = -2 * actualCorr x a s := by
  have he : Q x a (H s) = Q x a (fun t => max (t - s) 0) +
      star (Q x a (fun t => max (t - s) 0)) := by
    calc
      _ = Q x a (fun t => max (t - s) 0 + max (-t - s) 0) :=
        Q_congr x a (fun i j => abs_hinge_split s _ hs)
      _ = _ := by rw [Q_add, reverse_hinge]
  have h := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
  rw [he]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  dsimp [actualCorr, Q] at *
  linarith only [h]

private lemma clipped_corr (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (D : ℝ) (hx : ∀ i j, |x i - x j| ≤ D)
    (f f₁ f₂ : ℝ → ℝ) (hf : ∀ s, HasDerivAt f (f₁ s) s)
    (hf₁ : ∀ s, HasDerivAt f₁ (f₂ s) s) (hc : Continuous f₂)
    (l : ℝ) (hl : 0 ≤ l) (hlD : l ≤ D) (hzero : f l = 0) :
    (Q x a (clipped l f)).re = -2 * f₁ l * actualCorr x a l -
      2 * ∫ s in Icc l D, f₂ s * actualCorr x a s := by
  have hrep : Q x a (clipped l f) = (f₁ l : ℂ) * Q x a (H l) +
      ∫ s in Icc l D, (f₂ s : ℂ) * Q x a (H s) := by
    calc
      _ = Q x a (fun t => f₁ l * H l t + ∫ s in Icc l D, H s t * f₂ s) :=
        Q_congr x a (fun i j => clipped_representation f f₁ f₂ hf hf₁ hc
          l D hlD hzero (hx i j))
      _ = _ := by rw [Q_add, Q_scale, Q_integral x a l D f₂ hc]
  have hi : IntegrableOn (fun s : ℝ => (f₂ s : ℂ) * Q x a (H s)) (Icc l D) := by
    apply Continuous.integrableOn_Icc
    dsimp [Q, H]
    fun_prop
  have hre := integral_re hi
  simp only [RCLike.re_to_complex] at hre
  rw [hrep, Complex.add_re, ← hre, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hinge_corr x a ha l hl]
  have he : (∫ s in Icc l D, ((f₂ s : ℂ) * Q x a (H s)).re) =
      -2 * ∫ s in Icc l D, f₂ s * actualCorr x a s := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hinge_corr x a ha s (hl.trans hs.1)]
    ring
  rw [he]
  ring

private lemma base_corr (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (ha : ∑ i, a i = 0)
    (hx : ∀ i j, |x i - x j| ≤ D) :
    (Q x a (fun t => base |t|)).re =
      -(Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)) * E x a -
        2 * ∫ s in Icc 0 D, base₂ s * actualCorr x a s := by
  let f : ℝ → ℝ := fun r => base r - base 0
  have hrep : Q x a (fun t => base |t|) = Q x a (clipped 0 f) := by
    calc
      _ = Q x a (fun t => base 0 + clipped 0 f t) := by
        apply Q_congr x a
        intro i j
        rw [clipped, if_pos (abs_nonneg (x i - x j))]
        dsimp [f]
        ring
      _ = _ := by rw [Q_add, Q_constant x a ha, zero_add]
  rw [hrep, clipped_corr x a ha D hx f base₁ base₂
    (fun r => (base_deriv r).sub_const _) base₁_deriv
    (by unfold base₂ base; fun_prop) 0 le_rfl hD (by simp [f]), corr_at_zero x a ha]
  norm_num [base₁]
  ring

private lemma smooth₁_entry (n : ℕ) (hn : 2 ≤ n) :
    smooth₁ n (Real.log n) = ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : Real.exp (Real.log (n : ℝ) / 2) / n = Real.exp (-Real.log n / 2) := by
    rw [div_eq_mul_inv, ← Real.exp_log hn0, ← Real.exp_neg, ← Real.exp_add]
    simp only [Real.log_exp]
    congr 1 <;> ring
  dsimp [smooth₁]
  rw [he]
  ring

private lemma active_eq_Icc (D : ℝ) (N : ℕ) (hN : Real.exp D < N) :
    active D N = Finset.Icc 2 ⌊Real.exp D⌋₊ := by
  classical
  ext n
  simp only [active, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hnN, hn, hlog⟩
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact ⟨hn, (Nat.le_floor_iff (Real.exp_nonneg D)).mpr (by
      simpa only [Real.exp_log hn0] using Real.exp_le_exp.mpr hlog)⟩
  · rintro ⟨hn, hfloor⟩
    have hnle := (Nat.le_floor_iff (Real.exp_nonneg D)).mp hfloor
    have hnN : n < N := by exact_mod_cast (hnle.trans_lt hN)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact ⟨hnN, hn, by simpa only [Real.log_exp] using Real.log_le_log hn0 hnle⟩

private lemma complete_curvature_integral (D : ℝ) (hD : 0 ≤ D)
    (N : ℕ) (hN : Real.exp D < N) (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) :
    (∫ s in Icc 0 D, base₂ s * actualCorr x a s) +
      (∑ n ∈ active D N, ∫ s in Icc (Real.log n) D, smooth₂ n s * actualCorr x a s) =
    (1 / 4) * (∫ s in Icc 0 D, remainder s * actualCorr x a s) -
      ∫ s in Icc 0 D, Real.exp (s / 2) * actualCorr x a s := by
  classical
  let w : ℕ → ℝ → ℝ := fun n s =>
    (Icc (Real.log n) D).indicator (fun v => smooth₂ n v * actualCorr x a v) s
  have hi (n : ℕ) : IntegrableOn (w n) (Icc 0 D) := by
    apply IntegrableOn.indicator
    · apply Continuous.integrableOn_Icc
      exact (show Continuous (smooth₂ n) by unfold smooth₂ smooth; fun_prop).mul (corr_continuous x a ha)
    · exact measurableSet_Icc
  have hw (n : ℕ) (hn : n ∈ active D N) :
      (∫ s in Icc 0 D, w n s) = ∫ s in Icc (Real.log n) D, smooth₂ n s * actualCorr x a s := by
    have hn2 := (Finset.mem_filter.mp hn).2.1
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    dsimp [w]
    rw [setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.mpr (Icc_subset_Icc_left hln)]
  have hbase : IntegrableOn (fun s : ℝ => base₂ s * actualCorr x a s) (Icc 0 D) := by
    apply Continuous.integrableOn_Icc
    exact (show Continuous base₂ by unfold base₂ base; fun_prop).mul (corr_continuous x a ha)
  have hcomb : (fun s : ℝ => base₂ s * actualCorr x a s + ∑ n ∈ active D N, w n s) =ᵐ[
      volume.restrict (Icc 0 D)] (fun s => (remainder s / 4 - Real.exp (s / 2)) * actualCorr x a s) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    rw [local_remainder D N hN (by rw [abs_of_nonneg hs.1]; exact hs.2)]
    have he : (∑ n ∈ active D N, w n s) =
        (∑ n ∈ active D N, clipped (Real.log n) (smooth n) s) / 4 * actualCorr x a s := by
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hlog : Real.log (n : ℝ) ≤ s <;>
        simp [w, smooth₂, clipped, abs_of_nonneg hs.1, hlog, hs.2, Set.indicator]
    rw [he]
    simp only [abs_of_nonneg hs.1, base₂]
    ring
  have hR : Continuous remainder := by
    exact ActualKernelLocalPositivity.K_continuous.sub
      ((show Continuous (fun t : ℝ => Real.exp (-|t| / 2)) by fun_prop).mul
      (trivialT_continuousOn.comp_continuous continuous_abs
        (fun t => abs_nonneg t)))
  have hRi : IntegrableOn (fun s : ℝ => remainder s * actualCorr x a s) (Icc 0 D) :=
    (hR.mul (corr_continuous x a ha)).integrableOn_Icc
  have hEi : IntegrableOn (fun s : ℝ => Real.exp (s / 2) * actualCorr x a s) (Icc 0 D) :=
    ((show Continuous (fun s : ℝ => Real.exp (s / 2)) by fun_prop).mul
      (corr_continuous x a ha)).integrableOn_Icc
  calc
    _ = ∫ s in Icc 0 D, base₂ s * actualCorr x a s + ∑ n ∈ active D N, w n s := by
      rw [integral_add hbase (integrable_finsetSum _ (fun n hn => hi n)),
        integral_finsetSum _ (fun n hn => hi n)]
      congr 1
      exact Finset.sum_congr rfl hw |>.symm
    _ = ∫ s in Icc 0 D, (remainder s / 4 - Real.exp (s / 2)) * actualCorr x a s :=
      integral_congr_ae hcomb
    _ = _ := by
      simp_rw [sub_mul, div_mul_eq_mul_div]
      rw [integral_sub (hRi.div_const 4) hEi, integral_div]
      ring

/-- Complete actual-R correlation identity. The finite Mangoldt sum includes
every upper cutoff and every prime power. This is the complete finite-window remainder identity. -/
theorem actual_remainder_correlation_identity (D : ℝ) (hD : 0 ≤ D)
    (N : ℕ) (hN : Real.exp D < N) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    (∑ i, ∑ j, star (a i) * a j *
      ((ActualKernelLocalPositivity.K (x i - x j) -
        Real.exp (-|x i - x j| / 2) * trivialT |x i - x j| : ℝ) : ℂ)).re =
    -(Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)) *
      (∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) -
    2 * (∑ n ∈ Finset.Icc 2 ⌊Real.exp D⌋₊,
      (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        (∫ v : ℝ, star («prefix» x a (v + Real.log n)) * «prefix» x a v).re) +
    2 * (∫ s in Icc 0 D, Real.exp (s / 2) *
      (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re) -
    (1 / 2) * (∫ s in Icc 0 D,
      (ActualKernelLocalPositivity.K s - Real.exp (-|s| / 2) * trivialT |s|) *
        (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re) := by
  classical
  have hdiam (i j : I) : |x i - x j| ≤ D :=
    abs_le.mpr ⟨by linarith [(hx i).1, (hx j).2], by linarith [(hx i).2, (hx j).1]⟩
  have hrep : Q x a remainder = Q x a (fun t => base |t|) +
      ∑ n ∈ active D N, Q x a (clipped (Real.log n) (smooth n)) := by
    calc
      _ = Q x a (fun t => base |t| + ∑ n ∈ active D N, clipped (Real.log n) (smooth n) t) :=
        Q_congr x a (fun i j => local_remainder D N hN (hdiam i j))
      _ = _ := by rw [Q_add, Q_sum]
  have hterm (n : ℕ) (hn : n ∈ active D N) :
      (Q x a (clipped (Real.log n) (smooth n))).re =
      -2 * (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) * actualCorr x a (Real.log n) -
        2 * ∫ s in Icc (Real.log n) D, smooth₂ n s * actualCorr x a s := by
    have hn2 := (Finset.mem_filter.mp hn).2.1
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    rw [clipped_corr x a ha D hdiam (smooth n) (smooth₁ n) (smooth₂ n)
      (smooth_deriv n) (smooth₁_deriv n) (by unfold smooth₂ smooth; fun_prop)
      (Real.log n) hln (Finset.mem_filter.mp hn).2.2 (smooth_entry n hn2), smooth₁_entry n hn2]
  have hsum : (Q x a remainder).re =
      -(Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)) * E x a -
      2 * (∑ n ∈ active D N,
        (ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) * actualCorr x a (Real.log n)) -
      2 * ((∫ s in Icc 0 D, base₂ s * actualCorr x a s) +
        ∑ n ∈ active D N, ∫ s in Icc (Real.log n) D, smooth₂ n s * actualCorr x a s) := by
    rw [hrep, Complex.add_re, show (∑ n ∈ active D N, Q x a (clipped (Real.log n) (smooth n))).re =
      ∑ n ∈ active D N, (Q x a (clipped (Real.log n) (smooth n))).re from
        map_sum Complex.reCLM _ _, base_corr D hD x a ha hdiam]
    simp_rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [complete_curvature_integral D hD N hN x a ha, active_eq_Icc D N hN] at hsum
  dsimp [Q, remainder, E, actualCorr] at hsum
  simp only [starRingEnd_apply] at hsum
  linear_combination hsum


/-- The growing exponential has its actual prefix curvature, including
its origin jump. This is the owner-local FTC realization needed by the
full continuum payment, not an assumed distributional identity. -/
theorem growing_exponential_correlation_identity (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) :
    (∑ i, ∑ j, star (a i) * a j * (Real.exp (|x i - x j| / 2) : ℂ)).re =
      -(∫ v : ℝ, ‖«prefix» x a v‖ ^ 2) -
        (1 / 2) * ∫ s in Icc (0 : ℝ) D,
          Real.exp (s / 2) *
            (∫ v : ℝ, star («prefix» x a (v + s)) * «prefix» x a v).re := by
  let f : ℝ → ℝ := fun t => Real.exp (t / 2) - 1
  let f₁ : ℝ → ℝ := fun t => Real.exp (t / 2) / 2
  let f₂ : ℝ → ℝ := fun t => Real.exp (t / 2) / 4
  have hd (t : ℝ) : HasDerivAt f (f₁ t) t := by
    convert (((hasDerivAt_id t).div_const 2).exp.sub_const 1) using 1 <;> dsimp [f, f₁] <;> ring
  have hd₁ (t : ℝ) : HasDerivAt f₁ (f₂ t) t := by
    convert (((hasDerivAt_id t).div_const 2).exp.div_const 2) using 1 <;> dsimp [f₁, f₂] <;> ring
  have hdiam (i j : I) : |x i - x j| ≤ D :=
    abs_le.mpr ⟨by linarith [(hx i).1, (hx j).2], by linarith [(hx i).2, (hx j).1]⟩
  have hrep : Q x a (fun t => Real.exp (|t| / 2)) = Q x a (clipped 0 f) := by
    calc
      _ = Q x a (fun t => 1 + clipped 0 f t) := by
        apply Q_congr x a
        intro i j
        simp [clipped, abs_nonneg, f]
      _ = _ := by rw [Q_add, Q_constant x a ha, zero_add]
  have h := clipped_corr x a ha D hdiam f f₁ f₂ hd hd₁
    (by dsimp [f₂]; fun_prop) 0 le_rfl hD (by simp [f])
  rw [← hrep, corr_at_zero x a ha] at h
  have hi : IntegrableOn (fun s => Real.exp (s / 2) * actualCorr x a s) (Icc 0 D) :=
    ((show Continuous (fun s : ℝ => Real.exp (s / 2)) by fun_prop).mul
      (corr_continuous x a ha)).integrableOn_Icc
  have he : (∫ s in Icc (0 : ℝ) D, f₂ s * actualCorr x a s) =
      (1 / 4) * ∫ s in Icc (0 : ℝ) D, Real.exp (s / 2) * actualCorr x a s := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s _
    dsimp [f₂]
    ring
  rw [he] at h
  dsimp only [Q, E, actualCorr, f₁] at h
  norm_num only [zero_div, Real.exp_zero] at h
  linear_combination h

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
end
