/- GID: D5/S3/CharacterSums/DirichletCyclicContinuation
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletCyclicContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized analytic continuation for the actual cyclic character Laplace transform. -/

import D5.S3.CharacterSums.DirichletCyclicLaplace
import D5.S3.Analytic.Isolation.VerticalNearestPole
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # The normalized cyclic continuation

The zeta factor is normalized before taking logarithmic derivatives. Pairing
each character factor with its Schwarz reflection gives positive weights for
the actual real-valued family and removes the artificial singularity at one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter MeasureTheory ZetaAsymptotics
open scoped Topology BigOperators
open D5.S3.CharacterSums.DirichletCyclicLaplace
open D5.S3.Analytic.Isolation.VerticalNearestPole

namespace D5.S3.CharacterSums.DirichletCyclicContinuation

/-- The normalized zeta factor and both Schwarz partners of every character power. -/
def analyticFactor {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Option (Fin (r - 1) × Bool) → ℂ → ℂ
  | none => riemannZeta₁
  | some (j, false) => (χ ^ (j.1 + 1)).LFunction
  | some (j, true) => fun s => star ((χ ^ (j.1 + 1)).LFunction (star s))

/-- Each reflected pair shares the original strictly positive cyclic weight. -/
def factorWeight (r : ℕ) : Option (Fin (r - 1) × Bool) → ℝ
  | none => 1
  | some _ => 1 / (2 * (3 * r + 1 : ℝ))

/-- The actual zero set includes the reflected partners required by real parts. -/
def actualZeros {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Set ℂ :=
  {s | 0 < s.re ∧ ∃ i, analyticFactor (r := r) χ i s = 0}

/-- A divided difference fills the removable value at one. -/
def continuation {N r : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  regularizedLogFamily (analyticFactor (r := r) χ) (factorWeight r) 1

private theorem factor_weight_pos (r : ℕ) (i : Option (Fin (r - 1) × Bool)) :
    0 < factorWeight r i := by
  cases i <;> simp only [factorWeight] <;> positivity

private theorem power_nonprincipal {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) (j : Fin (r - 1)) :
    χ ^ (j.1 + 1) ≠ 1 := by
  apply pow_ne_one_of_lt_orderOf (by omega)
  have := j.isLt
  omega

private theorem factors_entire {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ)
    (i : Option (Fin (r - 1) × Bool)) : Differentiable ℂ (analyticFactor χ i) := by
  cases i with
  | none => exact differentiable_riemannZeta₁
  | some i =>
    rcases i with ⟨j, b⟩
    have hd := DirichletCharacter.differentiable_LFunction (power_nonprincipal χ hr j)
    cases b
    · exact hd
    · intro s
      simpa only [analyticFactor, Function.comp_def, starRingEnd_apply, star_star] using
        (hd (star s)).conj_conj

private theorem factors_one_ne_zero {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ)
    (i : Option (Fin (r - 1) × Bool)) : analyticFactor χ i 1 ≠ 0 := by
  cases i with
  | none => simp [analyticFactor]
  | some i =>
    rcases i with ⟨j, b⟩
    have hn := DirichletCharacter.LFunction_apply_one_ne_zero (power_nonprincipal χ hr j)
    cases b <;> simpa [analyticFactor] using hn

private theorem reflected_logDeriv (f : ℂ → ℂ) (s : ℂ) :
    logDeriv (fun z => star (f (star z))) s = star (logDeriv f (star s)) := by
  have hd := congrFun (deriv_star_conj (f := f)) s
  change deriv (fun z => star (f (star z))) s = star (deriv f (star s)) at hd
  simp only [logDeriv_apply, hd, star_div₀]

private theorem logarithmic_sum {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    (∑ i, (factorWeight r i : ℂ) * logDeriv (analyticFactor χ i) s) =
      logDeriv riemannZeta₁ s + (1 / (3 * r + 1 : ℂ)) *
        ∑ j : Fin (r - 1),
          (logDeriv (χ ^ (j.1 + 1)).LFunction s +
            star (logDeriv (χ ^ (j.1 + 1)).LFunction (star s))) / 2 := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool,
    analyticFactor, factorWeight, reflected_logDeriv, Complex.ofReal_one, one_mul,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_ofNat]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [one_div, mul_inv]
  ring

private theorem zeta_transform_normalized {s : ℂ} (hs : 1 < s.re) :
    zetaTransform s =
      -(logDeriv riemannZeta₁ s - s * logDeriv riemannZeta₁ 1 + (1 - s)) /
        (s * (s - 1)) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hn : riemannZeta₁ s ≠ 0 := by
    intro h
    exact hz (by rw [riemannZeta_eq_inv_sub_mul hs1, h, mul_zero])
  have hl : logDeriv riemannZeta s = -(s - 1)⁻¹ + logDeriv riemannZeta₁ s := by
    rw [logDeriv_apply, logDeriv_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs1,
      riemannZeta_eq_inv_sub_mul hs1]
    field_simp [hn, sub_ne_zero.mpr hs1]
  have hone : logDeriv riemannZeta₁ 1 = (Real.eulerMascheroniConstant : ℂ) := by
    simp [logDeriv_apply]
  unfold zetaTransform
  simp only [neg_div, ← logDeriv_apply]
  rw [hl, hone]
  push_cast
  field_simp [hs0, sub_ne_zero.mpr hs1]
  <;> ring

private theorem character_transform_normalized {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    characterTransform χ s =
      -(logDeriv χ.LFunction s - s * logDeriv χ.LFunction 1) / (s * (s - 1)) := by
  simp only [characterTransform, logDeriv_apply]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  <;> ring

/-- The divided-difference continuation agrees with the actual convergent integral. -/
theorem continuation_half_plane_laplace {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) {s : ℂ} (hs : 1 < s.re) :
    (∫ u : ℝ in Ioi 0, Complex.exp (-s * u) *
      (gl1CyclicFamily (r := r) χ (Real.exp u) : ℂ)) = continuation (r := r) χ s := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hcs0 : star s ≠ 0 := by simpa using hs0
  have hcs1 : star s ≠ 1 := by
    intro h
    apply hs1
    have he := congrArg Star.star h
    simpa only [star_star, star_one] using he
  rw [(gl1CyclicFamily_half_plane_laplace χ hr hs).2]
  have heq := (regularized_positive_log_family (analyticFactor (r := r) χ)
    (factorWeight r) 1 (factors_entire χ hr) (factors_one_ne_zero χ hr)
      (factor_weight_pos r)).1 s hs1
  rw [show continuation (r := r) χ s = _ from heq, logarithmic_sum, logarithmic_sum]
  unfold cyclicTransform
  rw [zeta_transform_normalized hs]
  have hpair (j : Fin (r - 1)) :
      (characterTransform (χ ^ (j.1 + 1)) s +
        star (characterTransform (χ ^ (j.1 + 1)) (star s))) / 2 =
      -((logDeriv (χ ^ (j.1 + 1)).LFunction s +
          star (logDeriv (χ ^ (j.1 + 1)).LFunction (star s))) / 2 -
        s * ((logDeriv (χ ^ (j.1 + 1)).LFunction 1 +
          star (logDeriv (χ ^ (j.1 + 1)).LFunction 1)) / 2)) / (s * (s - 1)) := by
    rw [character_transform_normalized _ hs0 hs1,
      character_transform_normalized _ hcs0 hcs1]
    simp only [starRingEnd_apply, star_div₀, star_neg, star_sub, star_mul,
      star_one, star_star]
    field_simp [hs0, sub_ne_zero.mpr hs1]
    <;> ring
  simp_rw [hpair]
  simp only [star_one]
  simp only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  <;> ring

/-- The genuine finite family is analytic away from its actual zero set, has isolated zeros,
and has a nonzero simple pole at every member zero. The hypotheses concern only the character. -/
theorem continuation_actual_poles {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) :
    (∀ z : ℂ, 0 < z.re → z ∉ actualZeros (r := r) χ →
      AnalyticAt ℂ (continuation (r := r) χ) z) ∧
    (∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, w ∉ actualZeros (r := r) χ) ∧
    (∀ z ∈ actualZeros (r := r) χ,
      let c : ℝ := ∑ i, factorWeight r i * analyticOrderNatAt (analyticFactor χ i) z
      0 < c ∧ (-1 / (z * (z - 1))) * (c : ℂ) ≠ 0 ∧
        (∃ R : ℂ → ℂ, AnalyticAt ℂ R z ∧
          continuation (r := r) χ =ᶠ[𝓝[≠] z]
            fun w => ((-1 / (z * (z - 1))) * (c : ℂ)) / (w - z) + R w) ∧
        meromorphicOrderAt (continuation (r := r) χ) z = -1) := by
  have hp := regularized_positive_log_family (analyticFactor (r := r) χ)
    (factorWeight r) 1 (factors_entire χ hr) (factors_one_ne_zero χ hr) (factor_weight_pos r)
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hn
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz
    apply hp.2.1 z hz0
    intro i hzero
    exact hn ⟨hz, i, hzero⟩
  · intro z
    have hi (i : Option (Fin (r - 1) × Bool)) :
        ∀ᶠ w in 𝓝[≠] z, analyticFactor χ i w ≠ 0 := by
      have hf := (factors_entire χ hr i).analyticAt z
      rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
      · have hglobal : AnalyticOnNhd ℂ (analyticFactor χ i) univ :=
          fun w _ => (factors_entire χ hr i).analyticAt w
        exact False.elim ((factors_one_ne_zero χ hr i)
          (hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
            (mem_univ z) hzero (mem_univ 1)))
      · exact hnonzero
    filter_upwards [Filter.eventually_all.mpr hi] with w hw
    rintro ⟨_, i, hi⟩
    exact hw i hi
  · intro z hz
    have hz0 : z ≠ 0 := by intro h; have := hz.1; simp [h] at this
    exact hp.2.2 z hz0 hz.2

private theorem factors_nonzero_right {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) {z : ℂ} (hz : 1 ≤ z.re)
    (i : Option (Fin (r - 1) × Bool)) : analyticFactor χ i z ≠ 0 := by
  cases i with
  | none =>
    change riemannZeta₁ z ≠ 0
    by_cases hz1 : z = 1
    · simp [hz1]
    · intro hn
      exact (riemannZeta_ne_zero_of_one_le_re hz)
        (by rw [riemannZeta_eq_inv_sub_mul hz1, hn, mul_zero])
  | some i =>
    rcases i with ⟨j, b⟩
    have hp := power_nonprincipal χ hr j
    cases b
    · exact (χ ^ (j.1 + 1)).LFunction_ne_zero_of_one_le_re (.inl hp) hz
    · have hc := (χ ^ (j.1 + 1)).LFunction_ne_zero_of_one_le_re
        (.inl hp) (show 1 ≤ (star z).re by simpa using hz)
      simpa [analyticFactor] using hc

/-- Every actual pole is strictly to the left of the classical nonvanishing line. -/
theorem actualZeros_re_lt_one {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) {z : ℂ}
    (hz : z ∈ actualZeros (r := r) χ) : z.re < 1 := by
  by_contra! h
  obtain ⟨i, hi⟩ := hz.2
  exact factors_nonzero_right χ hr h i hi

/-- A real member zero has a positive real residue for the normalized transform. -/
theorem actual_real_residue_pos {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hr : r ≤ orderOf χ) {z : ℂ}
    (hz : z ∈ actualZeros (r := r) χ) (him : z.im = 0) :
    let c : ℝ := ∑ i, factorWeight r i * analyticOrderNatAt (analyticFactor χ i) z
    0 < (((-1 / (z * (z - 1))) * (c : ℂ))).re ∧
      (((-1 / (z * (z - 1))) * (c : ℂ))).im = 0 := by
  have hc := ((continuation_actual_poles χ hr).2.2 z hz).1
  have hbeta : z.re < 1 := actualZeros_re_lt_one χ hr hz
  have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  let c : ℝ := ∑ i, factorWeight r i * analyticOrderNatAt (analyticFactor χ i) z
  have heq : (-1 / (z * (z - 1))) * (c : ℂ) =
      ((-1 / (z.re * (z.re - 1)) * c : ℝ) : ℂ) := by
    rw [hzreal]
    push_cast
    rfl
  change 0 < (((-1 / (z * (z - 1))) * (c : ℂ))).re ∧
    (((-1 / (z * (z - 1))) * (c : ℂ))).im = 0
  rw [heq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
  have hden : z.re * (z.re - 1) < 0 := mul_neg_of_pos_of_neg hz.1 (by linarith)
  exact mul_pos (div_pos_of_neg_of_neg (by norm_num) hden) hc

/-- An ordinary zeta zero in the positive half-plane belongs to the actual pole set. -/
theorem zeta_zero_mem_actualZeros {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 0 < z.re)
    (hzero : riemannZeta z = 0) :
    z ∈ actualZeros (r := r) χ := by
  have hz1 : z ≠ 1 := by
    intro heq
    exact riemannZeta_one_ne_zero (heq ▸ hzero)
  refine ⟨hz, none, ?_⟩
  change riemannZeta₁ z = 0
  have he := riemannZeta_eq_inv_sub_mul hz1
  rw [hzero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr hz1))

/-- Each nontrivial cyclic power is among the actual analytic factors. -/
theorem member_zero_mem_actualZeros {N r : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 0 < z.re)
    (j : Fin (r - 1)) (hzero : (χ ^ (j.1 + 1)).LFunction z = 0) :
    z ∈ actualZeros (r := r) χ := ⟨hz, some (j, false), hzero⟩

end D5.S3.CharacterSums.DirichletCyclicContinuation
