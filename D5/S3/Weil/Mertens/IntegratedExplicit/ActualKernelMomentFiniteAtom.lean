/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentFiniteAtom
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentFiniteAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite atom and translated-family algebra for the literal V obstruction. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentResolvent
import Mathlib.Algebra.Group.ForwardDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

private lemma literal_correlation_zero (x : I → ℝ) (a : I → ℂ)
    (ha : ∑ i, a i = 0) : correlation x a 0 = energy x a := by
  have hre := integral_re (shifted_hinge_prefix_energy x a ha 0).1
  simp only [RCLike.re_to_complex] at hre
  rw [correlation, ← hre]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [add_zero]
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private def literalExpPair (x : I → ℝ) (a : I → ℂ) (t : ℝ) : ℝ :=
  (∑ i, ∑ j, star (a i) * a j * (Real.exp (-|t + x i - x j| / 2) : ℂ)).re

private lemma literalExpPair_neg (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    literalExpPair x a (-t) = literalExpPair x a t := by
  classical
  simp only [literalExpPair, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : |-t + x j - x i| = |t + x i - x j| := by
    rw [show -t + x j - x i = -(t + x i - x j) by ring, abs_neg]
  rw [he]
  simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma literalExpPair_shift (x : I → ℝ) (a : I → ℂ) (t : ℝ) :
    (quadratic (shiftedNodes x t) (shiftedCoeffs a 1)
      (fun s => Real.exp (-|s| / 2))).re =
      2 * literalExpPair x a 0 + 2 * literalExpPair x a t := by
  classical
  have hd : max t 0 - max (-t) 0 = t := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (by linarith : -t ≤ 0)]; ring
    · rw [max_eq_right ht, max_eq_left (by linarith : 0 ≤ -t)]; ring
  have he₁ (i j : I) : x i + max t 0 - (x j + max t 0) = x i - x j := by ring
  have he₂ (i j : I) : x i + max (-t) 0 - (x j + max (-t) 0) = x i - x j := by ring
  have he₃ (i j : I) : x i + max t 0 - (x j + max (-t) 0) = t + x i - x j := by
    linarith only [hd]
  have he₄ (i j : I) : x i + max (-t) 0 - (x j + max t 0) = -t + x i - x j := by
    linarith only [hd]
  simp only [quadratic, Fintype.sum_sum_type, shiftedNodes, shiftedCoeffs,
    Complex.ofReal_one, one_mul, he₁, he₂, he₃, he₄, Finset.sum_add_distrib,
    Complex.add_re]
  have heq : literalExpPair x a 0 + literalExpPair x a (-t) +
      (literalExpPair x a t + literalExpPair x a 0) =
      2 * literalExpPair x a 0 + 2 * literalExpPair x a t := by
    rw [literalExpPair_neg]
    ring
  simpa only [literalExpPair, zero_add] using heq

/-- Finite polarization of the actual resolvent, with support-safe shifts. -/
private lemma literal_S_finite (D : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) :
    S D x a t = correlation x a t - literalExpPair x a t := by
  have hx' : ∀ i, shiftedNodes x t i ∈ Icc (0 : ℝ) (D + |t|) := by
    intro i
    cases i with
    | inl i => exact ⟨add_nonneg (hx i).1 (le_max_right _ _),
        add_le_add (hx i).2 (max_le (le_abs_self t) (abs_nonneg t))⟩
    | inr i => exact ⟨add_nonneg (hx i).1 (le_max_right _ _),
        add_le_add (hx i).2 (max_le (neg_le_abs t) (abs_nonneg t))⟩
  have ha' : ∑ i, shiftedCoeffs a 1 i = 0 := by
    simp [shiftedCoeffs, Fintype.sum_sum_type, ← Finset.mul_sum, ha]
  have hp := shifted_W D hD x a hx ha t 1 (by norm_num)
  have hd := W_eq_exponential_deficit (D + |t|) (by positivity) _ _ hx' ha'
  have he := shifted_correlation x a ha t 1 0 (by norm_num)
  rw [literal_correlation_zero _ _ ha', literal_correlation_zero _ _ ha,
    zero_add, zero_sub, correlation_neg] at he
  rw [W_eq_exponential_deficit D hD x a hx ha] at hp
  rw [literalExpPair_shift] at hd
  have hq : (quadratic x a (fun s => Real.exp (-|s| / 2))).re =
      literalExpPair x a 0 := by simp [literalExpPair, quadratic]
  rw [hq] at hp
  linarith only [hp, hd, he]

def literalNuNodes (ell : ℝ) : Fin 3 → ℝ := ![0, ell / 2, ell]
def literalNuCoeffs (ell : ℝ) : Fin 3 → ℝ :=
  ![1, -(1 + Real.exp (-ell / 4)), Real.exp (-ell / 4)]
def literalStep (q : ℕ) : ℝ := 1 / (16 * (q : ℝ))
def literalNodes (q : ℕ) (i : Fin q × Fin 3 × Bool) : ℝ :=
  (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2.1 +
    if i.2.2 then Real.log 2 else 0
def literalCoeffs (q : ℕ) (i : Fin q × Fin 3 × Bool) : ℂ :=
  (((-1 : ℝ) ^ (i.1 : ℕ) * ((q - 1).choose (i.1 : ℕ) : ℝ) *
    literalNuCoeffs (literalStep q) i.2.1 * if i.2.2 then -1 else 1) : ℝ)

private lemma literalCoeffs_ofReal_re (q : ℕ) (i : Fin q × Fin 3 × Bool) :
    ((literalCoeffs q i).re : ℂ) = literalCoeffs q i := rfl

lemma literal_step_bounds (q : ℕ) (hq : 1 ≤ q) :
    0 < literalStep q ∧ literalStep q ≤ 1 / 16 ∧
      (q : ℝ) * literalStep q = 1 / 16 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  dsimp [literalStep]
  constructor
  · positivity
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * q) (by norm_num : (0 : ℝ) < 16)).mpr
    nlinarith
  · field_simp

lemma literal_support (q : ℕ) (hq : 1 ≤ q) (i : Fin q × Fin 3 × Bool) :
    literalNodes q i ∈ Icc (0 : ℝ) (1 / 16) ∪
      Icc (Real.log 2) (Real.log 2 + 1 / 16) := by
  have hl := literal_step_bounds q hq
  have hj : (i.1 : ℝ) + 1 ≤ q := by exact_mod_cast i.1.isLt
  have hk : 0 ≤ literalNuNodes (literalStep q) i.2.1 ∧
      literalNuNodes (literalStep q) i.2.1 ≤ literalStep q := by
    rcases i.2.1 with ⟨k, hk⟩
    interval_cases k <;> simp [literalNuNodes] <;> (try constructor) <;> linarith [hl.1]
  have hb : 0 ≤ (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2.1 ∧
      (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2.1 ≤ 1 / 16 := by
    constructor
    · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hl.1.le) hk.1
    · nlinarith [mul_le_mul_of_nonneg_right hj hl.1.le, hl.2.2]
  cases hb' : i.2.2
  · exact Or.inl (by simpa [literalNodes, hb'] using hb)
  · exact Or.inr (by simp only [literalNodes, hb', ite_true, mem_Icc]; constructor <;> linarith [hb.1, hb.2])

private lemma literalNu_mass (ell : ℝ) : ∑ k, (literalNuCoeffs ell k : ℂ) = 0 := by
  simp [literalNuCoeffs, Fin.sum_univ_succ]

private lemma literalNu_exp (ell : ℝ) :
    ∑ k, (literalNuCoeffs ell k : ℂ) * (Real.exp (literalNuNodes ell k / 2) : ℂ) = 0 := by
  have h₁ : Real.exp (-ell / 4) * Real.exp (ell / 4) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2 <;> ring
  have h₂ : Real.exp (-ell / 4) * Real.exp (ell / 2) = Real.exp (ell / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have hreal : ∑ k, literalNuCoeffs ell k * Real.exp (literalNuNodes ell k / 2) = 0 := by
    simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
      show ell / 2 / 2 = ell / 4 by ring]
    nlinarith only [h₁, h₂]
  exact_mod_cast hreal

private lemma literal_exp_cubic (z : ℝ) (hz : 0 ≤ z) :
    z ^ 3 / 6 ≤ (z - 2) * Real.exp z + z + 2 := by
  let f : ℝ → ℝ := fun t => (t - 1) * Real.exp t + 1 - t ^ 2 / 2
  have hf' (t : ℝ) : HasDerivAt f (t * (Real.exp t - 1)) t := by
    dsimp [f]
    convert (((hasDerivAt_id t).sub_const 1).mul (Real.hasDerivAt_exp t)).add_const 1 |>.sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1 <;> (try funext u) <;> dsimp <;> ring
  have hf : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [f]; fun_prop)
      (fun t _ => (hf' t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht : t ∈ Ici (0 : ℝ))
    exact mul_nonneg ht0 (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht0))
  have hf0 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
    have h := hf (by simp) ht ht
    simpa [f] using h
  let g : ℝ → ℝ := fun t => (t - 2) * Real.exp t + t + 2 - t ^ 3 / 6
  have hg' (t : ℝ) : HasDerivAt g (f t) t := by
    dsimp [g, f]
    convert (((((hasDerivAt_id t).sub_const 2).mul (Real.hasDerivAt_exp t)).add
      (hasDerivAt_id t)).add_const 2).sub (((hasDerivAt_id t).pow 3).div_const 6) using 1 <;> (try funext u) <;> dsimp <;> ring
  have hg : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (by dsimp [g]; fun_prop) (fun t _ => (hg' t).hasDerivWithinAt)
    intro t ht
    exact hf0 t (interior_subset ht)
  have h := hg (by simp) hz hz
  dsimp [g] at h
  norm_num at h
  linarith


private lemma literal_correlation_hinge (x : I → ℝ) (a : I → ℝ)
    (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ) :
    correlation x (fun i => (a i : ℂ)) t =
      -(∑ i, ∑ j, a i * a j * max (x i - x j - t) 0) := by
  have h := congrArg Complex.re (shifted_hinge_prefix_energy x (fun i => (a i : ℂ)) ha t).2.2.1
  simp only [Complex.re_sum, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.neg_re] at h
  change _ = -correlation x (fun i => (a i : ℂ)) t at h
  linarith only [h]

lemma literal_S_tail (D H : ℝ) (hD : 0 ≤ D)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (hxH : ∀ i, x i ∈ Icc (0 : ℝ) H) (ha : ∑ i, a i = 0)
    (hexp : ∑ i, a i * (Real.exp (x i / 2) : ℂ) = 0)
    (t : ℝ) (ht : H ≤ |t|) : S D x a t = 0 := by
  have hpos (s : ℝ) (hs : H ≤ s) : S D x a s = 0 := by
    have hc : correlation x a s = 0 := by
      have hh := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
      have hz (i j : I) : max (x i - x j - s) 0 = 0 :=
        max_eq_right (by linarith [(hxH i).2, (hxH j).1])
      simp only [hz, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero,
        Complex.zero_re, Complex.neg_re] at hh
      change 0 = -correlation x a s at hh
      linarith only [hh]
    have he (i j : I) : Real.exp (-|s + x i - x j| / 2) =
        Real.exp (-s / 2) * Real.exp (-x i / 2) * Real.exp (x j / 2) := by
      rw [abs_of_nonneg (by linarith [(hxH i).1, (hxH j).2]),
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hq : literalExpPair x a s = 0 := by
      dsimp only [literalExpPair]
      have hz (i : I) : (∑ j, star (a i) * a j * (Real.exp (-|s + x i - x j| / 2) : ℂ)) = 0 := by
        simp_rw [he, Complex.ofReal_mul]
        calc
          _ = (star (a i) * (Real.exp (-s / 2) : ℂ) *
              (Real.exp (-x i / 2) : ℂ)) *
              ∑ j, a j * (Real.exp (x j / 2) : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = 0 := by rw [hexp, mul_zero]
      simp only [hz, Finset.sum_const_zero, Complex.zero_re]
    rw [literal_S_finite D hD x a hx ha s, hc, hq, sub_self]
  rcases le_total 0 t with ht0 | ht0
  · exact hpos t (by simpa only [abs_of_nonneg ht0] using ht)
  · rw [← S_even D hD x a ha t]
    exact hpos (-t) (by simpa only [abs_of_nonpos ht0] using ht)

private lemma literalNu_support (ell : ℝ) (hl : 0 ≤ ell) (k : Fin 3) :
    literalNuNodes ell k ∈ Icc (0 : ℝ) ell := by
  rcases k with ⟨k, hk⟩
  interval_cases k <;> simp [literalNuNodes] <;> (try constructor) <;> linarith

private lemma literalNu_energy (ell : ℝ) (hl : 0 ≤ ell) :
    energy (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)) =
      ell * (1 + Real.exp (-ell / 4) ^ 2) / 2 := by
  rw [← literal_correlation_zero _ _ (literalNu_mass ell),
    literal_correlation_hinge _ _ (literalNu_mass ell)]
  have hh : 0 ≤ ell / 2 := by linarith
  have hn : -(ell / 2) ≤ 0 := by linarith
  have hn' : -ell ≤ 0 := by linarith
  simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
    max_eq_left hl, max_eq_left hh, max_eq_right hn, max_eq_right hn',
    show ell / 2 - ell = -(ell / 2) by ring,
    show ell - ell / 2 = ell / 2 by ring]
  ring

private lemma literal_quadratic_real (x : I → ℝ) (a : I → ℝ) (f : ℝ → ℝ) :
    (quadratic x (fun i => (a i : ℂ)) f).re =
      ∑ i, ∑ j, a i * a j * f (x i - x j) := by
  simp only [quadratic, Complex.re_sum, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re]

private lemma literalNu_W (D ell : ℝ) (hD : 0 ≤ D) (hl : 0 ≤ ell)
    (hlD : ell ≤ D) :
    W D (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)) =
      ell * (1 + Real.exp (-ell / 4) ^ 2) / 2 - 2 * (1 - Real.exp (-ell / 4) ^ 2) := by
  rw [W_eq_exponential_deficit D hD _ _
    (fun k => ⟨(literalNu_support ell hl k).1,
      (literalNu_support ell hl k).2.trans hlD⟩) (literalNu_mass ell), literalNu_energy ell hl]
  rw [literal_quadratic_real]
  have he : Real.exp (-ell / 2) = Real.exp (-ell / 4) ^ 2 := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hh : 0 ≤ ell / 2 := by linarith
  simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
    abs_of_nonneg hl, abs_of_nonneg hh, abs_of_nonpos (neg_nonpos.mpr hl),
    abs_of_nonpos (neg_nonpos.mpr hh),
    show ell / 2 - ell = -(ell / 2) by ring,
    show ell - ell / 2 = ell / 2 by ring,
    he, show -(ell / 2) / 2 = -ell / 4 by ring]
  ring

lemma literalNu_W_lower (D ell : ℝ) (hD : 0 ≤ D) (hl : 0 ≤ ell)
    (hlD : ell ≤ D) :
    Real.exp (-ell / 4) ^ 2 * ell ^ 3 / 48 ≤
      W D (literalNuNodes ell) (fun k => (literalNuCoeffs ell k : ℂ)) := by
  rw [literalNu_W D ell hD hl hlD]
  have he : Real.exp (-ell / 4) ^ 2 = Real.exp (-(ell / 2)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (ell / 2) * Real.exp (-(ell / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h := mul_le_mul_of_nonneg_left (literal_exp_cubic (ell / 2) (by linarith))
    (Real.exp_pos (-(ell / 2))).le
  rw [he]
  have heq : Real.exp (-(ell / 2)) *
      ((ell / 2 - 2) * Real.exp (ell / 2) + ell / 2 + 2) =
      ell * (1 + Real.exp (-(ell / 2))) / 2 - 2 * (1 - Real.exp (-(ell / 2))) := by
    calc
      _ = (ell / 2 - 2) * (Real.exp (ell / 2) * Real.exp (-(ell / 2))) +
          Real.exp (-(ell / 2)) * (ell / 2 + 2) := by ring
      _ = _ := by rw [hinv]; ring
  rw [heq] at h
  convert h using 1 <;> ring


private def literalMixed : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | h :: hs, f => literalMixed hs (fwdDiff h f)

private lemma literalMixed_mul (hs : List ℝ) (c : ℝ) (f : ℝ → ℝ) :
    literalMixed hs (fun t => c * f t) = fun t => c * literalMixed hs f t := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => c * f t) = fun t => c * fwdDiff h f t := by
      ext t; simp only [fwdDiff]; ring
    simp only [literalMixed, he, ih]

private lemma literalMixed_sum {J : Type*} (s : Finset J) (hs : List ℝ) (f : J → ℝ → ℝ) :
    literalMixed hs (fun t => ∑ j ∈ s, f j t) = fun t => ∑ j ∈ s, literalMixed hs (f j) t := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => ∑ j ∈ s, f j t) = fun t => ∑ j ∈ s, fwdDiff h (f j) t := by
      ext t; simp only [fwdDiff, Finset.sum_sub_distrib]
    simp only [literalMixed, he, ih]

private lemma literal_pow_difference (h : ℝ) (m : ℕ) :
    fwdDiff h (fun t : ℝ => t ^ m) =
      fun t => ∑ k ∈ Finset.range m, ((m.choose k : ℝ) * h ^ (m - k)) * t ^ k := by
  ext t
  simp only [fwdDiff, add_pow, Finset.sum_range_succ, Nat.sub_self,
    pow_zero, Nat.choose_self, Nat.cast_one, mul_one, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro k _
  ring

private lemma literalMixed_power (hs : List ℝ) (m : ℕ) (hm : m ≤ hs.length) (y : ℝ) :
    literalMixed hs (fun t => t ^ m) y =
      if m < hs.length then 0 else (m.factorial : ℝ) * hs.prod := by
  induction hs generalizing m y with
  | nil =>
    have hm0 : m = 0 := by simpa using hm
    subst m
    simp [literalMixed]
  | cons h hs ih =>
    have he : literalMixed (h :: hs) (fun t => t ^ m) y =
        ∑ k ∈ Finset.range m, ((m.choose k : ℝ) * h ^ (m - k)) *
          literalMixed hs (fun t => t ^ k) y := by
      simp only [literalMixed, literal_pow_difference, literalMixed_sum, literalMixed_mul]
    rw [he]
    by_cases hlt : m < (h :: hs).length
    · rw [if_pos hlt]
      apply Finset.sum_eq_zero
      intro k hk
      have hk0 : k < hs.length := by
        have := Finset.mem_range.mp hk
        simp only [List.length_cons] at hlt
        omega
      rw [ih k hk0.le y, if_pos hk0, mul_zero]
    · have hm0 : m = hs.length + 1 := by simp only [List.length_cons] at hm hlt; omega
      subst m
      rw [if_neg hlt, Finset.sum_range_succ]
      have hz : (∑ k ∈ Finset.range hs.length,
          ((hs.length + 1).choose k : ℝ) * h ^ (hs.length + 1 - k) *
            literalMixed hs (fun t => t ^ k) y) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have hk0 := Finset.mem_range.mp hk
        rw [ih k hk0.le y, if_pos hk0, mul_zero]
      rw [hz, zero_add, ih hs.length le_rfl y, if_neg (lt_irrefl _),
        Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, List.prod_cons]
      ring

private lemma literalMixed_shift (hs : List ℝ) (f : ℝ → ℝ) (c : ℝ) :
    literalMixed hs (fun t => f (t + c)) = fun t => literalMixed hs f (t + c) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => f (t + c)) = fun t => fwdDiff h f (t + c) := by
      ext t; simp [fwdDiff, add_right_comm]
    simp only [literalMixed, he, ih]

private lemma literalMixed_sub (hs : List ℝ) (f g : ℝ → ℝ) :
    literalMixed hs (fun t => f t - g t) = fun t => literalMixed hs f t - literalMixed hs g t := by
  induction hs generalizing f g with
  | nil => rfl
  | cons h hs ih =>
    have he : fwdDiff h (fun t => f t - g t) = fun t => fwdDiff h f t - fwdDiff h g t := by
      ext t; simp only [fwdDiff]; ring
    simp only [literalMixed, he, ih]

private lemma literalMixed_commute (hs : List ℝ) (h : ℝ) (f : ℝ → ℝ) :
    literalMixed hs (fwdDiff h f) = fwdDiff h (literalMixed hs f) := by
  induction hs generalizing f with
  | nil => rfl
  | cons k hs ih =>
    have he : fwdDiff k (fwdDiff h f) = fwdDiff h (fwdDiff k f) := by
      ext t; simp [fwdDiff, add_right_comm]; ring
    simp only [literalMixed, he, ih]

private lemma literalMixed_replicate (n : ℕ) (h : ℝ) (f : ℝ → ℝ) :
    literalMixed (List.replicate n h) f = (fwdDiff h)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, literalMixed, ih, Function.iterate_succ_apply]

private lemma literalMixed_append (hs ks : List ℝ) (f : ℝ → ℝ) :
    literalMixed (hs ++ ks) f = literalMixed ks (literalMixed hs f) := by
  induction hs generalizing f with
  | nil => rfl
  | cons h hs ih => simp only [List.cons_append, literalMixed, ih]

private lemma literal_binomial_difference (n : ℕ) (ell y : ℝ) (f : ℝ → ℝ) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
      f (y + (j : ℝ) * ell)) = (-1 : ℝ) ^ n * (fwdDiff ell)^[n] f y := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (j : ℕ) ≤ n := by omega
  have he : (-1 : ℝ) ^ n * (-1 : ℝ) ^ (n - (j : ℕ)) = (-1 : ℝ) ^ (j : ℕ) := by
    rw [← pow_add, show n + (n - (j : ℕ)) = 2 * (n - (j : ℕ)) + (j : ℕ) by omega,
      pow_add, pow_mul]
    norm_num
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, nsmul_eq_mul]
  rw [← he]
  ring

private lemma literal_stencil (n : ℕ) (f : ℝ → ℝ) :
    (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * f (literalNodes (n + 1) i)) =
    (-1 : ℝ) ^ n *
      (literalMixed (List.replicate n (literalStep (n + 1)) ++
          [Real.log 2, literalStep (n + 1) / 2]) f 0 -
        Real.exp (-literalStep (n + 1) / 4) *
          literalMixed (List.replicate n (literalStep (n + 1)) ++
            [Real.log 2, literalStep (n + 1) / 2]) f (literalStep (n + 1) / 2)) := by
  let ell := literalStep (n + 1)
  let r := Real.exp (-ell / 4)
  let g : ℝ → ℝ := fun t =>
    f t - (1 + r) * f (t + ell / 2) + r * f (t + ell) -
      (f (t + Real.log 2) - (1 + r) * f (t + Real.log 2 + ell / 2) +
        r * f (t + Real.log 2 + ell))
  have hsum : (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * f (literalNodes (n + 1) i)) =
      ∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
        g (0 + (j : ℝ) * ell) := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    simp [literalNodes, literalCoeffs, literalNuNodes, literalNuCoeffs,
      Fin.sum_univ_succ, Fintype.sum_bool, g, ell, r]
    ring
  have hg : g = fun t => fwdDiff (ell / 2) (fwdDiff (Real.log 2) f) t -
      r * fwdDiff (ell / 2) (fwdDiff (Real.log 2) f) (t + ell / 2) := by
    ext t
    dsimp [g, fwdDiff]
    simp only [show t + ell / 2 + Real.log 2 = t + Real.log 2 + ell / 2 by ring,
      show t + ell / 2 + ell / 2 = t + ell by ring,
      show t + ell / 2 + ell / 2 + Real.log 2 = t + Real.log 2 + ell by ring]
    ring
  rw [hsum, literal_binomial_difference n ell 0 g, ← literalMixed_replicate, hg,
    literalMixed_sub, literalMixed_mul, literalMixed_shift,
    literalMixed_commute, literalMixed_commute]
  simp only [literalMixed_append, literalMixed, zero_add]
  rfl

lemma literal_moments (q : ℕ) (hq : 1 ≤ q) (m : ℕ) (hm : m ≤ q) :
    ∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) ^ m = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have he := literal_stencil n (fun t => t ^ m)
  have hlen : m < (List.replicate n (literalStep (n + 1)) ++
      [Real.log 2, literalStep (n + 1) / 2]).length := by simp; omega
  rw [literalMixed_power _ m hlen.le, if_pos hlen,
    literalMixed_power _ m hlen.le, if_pos hlen] at he
  simp only [mul_zero, sub_self] at he
  have hc : ∑ i : Fin (n + 1) × Fin 3 × Bool,
      (((literalCoeffs (n + 1) i).re * literalNodes (n + 1) i ^ m : ℝ) : ℂ) = 0 := by
    exact_mod_cast he
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, literalCoeffs_ofReal_re] using hc

lemma literal_moment_residual (q : ℕ) (hq : 1 ≤ q) :
    (∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) ^ (q + 1)) =
      (((-1 : ℝ) ^ (q + 1) * ((q + 1).factorial : ℝ) * Real.log 2 *
        literalStep q ^ q * (1 - Real.exp (-literalStep q / 4)) / 2 : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have he := literal_stencil n (fun t => t ^ (n + 1 + 1))
  have hlen : (List.replicate n (literalStep (n + 1)) ++
      [Real.log 2, literalStep (n + 1) / 2]).length = n + 1 + 1 := by simp
  simp only [literalMixed_power _ _ (by omega : n + 1 + 1 ≤
    (List.replicate n (literalStep (n + 1)) ++ [Real.log 2, literalStep (n + 1) / 2]).length),
    hlen, lt_self_iff_false, if_false, List.prod_append, List.prod_replicate,
    List.prod_cons, List.prod_nil, mul_one] at he
  have hr : (-1 : ℝ) ^ (n + 1 + 1) = (-1 : ℝ) ^ n := by rw [show n + 1 + 1 = n + 2 by omega, pow_add]; norm_num
  have he' : (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * literalNodes (n + 1) i ^ (n + 1 + 1)) =
      (-1 : ℝ) ^ (n + 1 + 1) * ((n + 1 + 1).factorial : ℝ) * Real.log 2 *
        literalStep (n + 1) ^ (n + 1) * (1 - Real.exp (-literalStep (n + 1) / 4)) / 2 := by
    rw [he, hr, pow_succ]
    ring
  have hc := congrArg (fun z : ℝ => (z : ℂ)) he'
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    literalCoeffs_ofReal_re] using hc


private lemma literalNu_exp_real (ell : ℝ) :
    ∑ k, literalNuCoeffs ell k * Real.exp (literalNuNodes ell k / 2) = 0 := by
  have h := congrArg Complex.re (literalNu_exp ell)
  simpa only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.zero_re] using h

private lemma literal_exp_translate (x : I → ℝ) (a : I → ℝ) (c : ℝ) :
    (∑ i, a i * Real.exp ((c + x i) / 2)) =
      Real.exp (c / 2) * ∑ i, a i * Real.exp (x i / 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (c + x i) / 2 = c / 2 + x i / 2 by ring, Real.exp_add]
  ring

private lemma literal_exp_translate_weighted (x : I → ℝ) (a : I → ℝ)
    (ha : ∑ i, a i * Real.exp (x i / 2) = 0) (c : ℝ) :
    (∑ i, a i * (c + x i) * Real.exp ((c + x i) / 2)) =
      Real.exp (c / 2) * ∑ i, a i * x i * Real.exp (x i / 2) := by
  calc
    _ = Real.exp (c / 2) * (c * (∑ i, a i * Real.exp (x i / 2)) +
        ∑ i, a i * x i * Real.exp (x i / 2)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (c + x i) / 2 = c / 2 + x i / 2 by ring, Real.exp_add]
      ring
    _ = _ := by rw [ha, mul_zero, zero_add]

private lemma literalNu_exp_weighted (ell : ℝ) :
    (∑ k, literalNuCoeffs ell k * literalNuNodes ell k *
      Real.exp (literalNuNodes ell k / 2)) =
        (ell / 2) * (Real.exp (ell / 4) - 1) := by
  have h₁ : Real.exp (-ell / 4) * Real.exp (ell / 4) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 2 <;> ring
  have h₂ : Real.exp (-ell / 4) * Real.exp (ell / 2) = Real.exp (ell / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  simp [literalNuNodes, literalNuCoeffs, Fin.sum_univ_succ,
    show ell / 2 / 2 = ell / 4 by ring]
  linear_combination (ell / 2) * (-h₁) + ell * h₂

private lemma literal_binomial_exp (n : ℕ) (ell : ℝ) :
    (∑ j : Fin (n + 1), (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
      Real.exp ((j : ℝ) * ell / 2)) = (1 - Real.exp (ell / 2)) ^ n := by
  have he (j : ℕ) : Real.exp ((j : ℝ) * ell / 2) = Real.exp (ell / 2) ^ j := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [show 1 - Real.exp (ell / 2) = -Real.exp (ell / 2) + 1 by ring,
    add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [he]
  rw [neg_pow]
  simp only [one_pow, mul_one]
  ring

lemma literal_exp_null (q : ℕ) :
    ∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i *
      (Real.exp (literalNodes q i / 2) : ℂ) = 0 := by
  have hr : (∑ i : Fin q × Fin 3 × Bool, (literalCoeffs q i).re *
      Real.exp (literalNodes q i / 2)) = 0 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro j _
    let beta : ℝ := (-1 : ℝ) ^ (j : ℕ) * ((q - 1).choose (j : ℕ) : ℝ)
    have he : (∑ k : Fin 3, ∑ b : Bool,
        (literalCoeffs q (j, k, b)).re * Real.exp (literalNodes q (j, k, b) / 2)) =
        beta * ((∑ k, literalNuCoeffs (literalStep q) k *
          Real.exp (((j : ℝ) * literalStep q + literalNuNodes (literalStep q) k) / 2)) -
        ∑ k, literalNuCoeffs (literalStep q) k *
          Real.exp (((j : ℝ) * literalStep q + Real.log 2 + literalNuNodes (literalStep q) k) / 2)) := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Fintype.sum_bool, literalCoeffs, literalNodes, Complex.ofReal_re]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [beta]
      simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
      rw [show (j : ℝ) * literalStep q + literalNuNodes (literalStep q) k + Real.log 2 =
        (j : ℝ) * literalStep q + Real.log 2 + literalNuNodes (literalStep q) k by ring]
      ring
    rw [he, literal_exp_translate, literal_exp_translate, literalNu_exp_real]
    simp only [mul_zero, sub_self]
  have hc := congrArg (fun z : ℝ => (z : ℂ)) hr
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, literalCoeffs_ofReal_re, Complex.ofReal_zero] using hc

lemma literal_exp_residual (q : ℕ) (hq : 1 ≤ q) :
    (∑ i : Fin q × Fin 3 × Bool, literalCoeffs q i * (literalNodes q i : ℂ) *
      (Real.exp (literalNodes q i / 2) : ℂ)) =
      (((literalStep q / 2) * (1 - Real.exp (Real.log 2 / 2)) *
        (1 - Real.exp (literalStep q / 2)) ^ (q - 1) *
        (Real.exp (literalStep q / 4) - 1) : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let ell := literalStep (n + 1)
  let R := (ell / 2) * (Real.exp (ell / 4) - 1)
  have hrow (j : Fin (n + 1)) :
      (∑ k : Fin 3, ∑ b : Bool,
        (literalCoeffs (n + 1) (j, k, b)).re * literalNodes (n + 1) (j, k, b) *
          Real.exp (literalNodes (n + 1) (j, k, b) / 2)) =
      (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
        Real.exp ((j : ℝ) * ell / 2) * (1 - Real.exp (Real.log 2 / 2)) * R := by
    have he : (∑ k : Fin 3, ∑ b : Bool,
        (literalCoeffs (n + 1) (j, k, b)).re * literalNodes (n + 1) (j, k, b) *
          Real.exp (literalNodes (n + 1) (j, k, b) / 2)) =
      (-1 : ℝ) ^ (j : ℕ) * (n.choose (j : ℕ) : ℝ) *
      ((∑ k, literalNuCoeffs ell k * ((j : ℝ) * ell + literalNuNodes ell k) *
          Real.exp (((j : ℝ) * ell + literalNuNodes ell k) / 2)) -
      ∑ k, literalNuCoeffs ell k * ((j : ℝ) * ell + Real.log 2 + literalNuNodes ell k) *
          Real.exp (((j : ℝ) * ell + Real.log 2 + literalNuNodes ell k) / 2)) := by
      simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Fintype.sum_bool, literalCoeffs, literalNodes, Complex.ofReal_re,
        Nat.add_sub_cancel_right]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [ell]
      simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
      rw [show (j : ℝ) * literalStep (n + 1) + literalNuNodes (literalStep (n + 1)) k + Real.log 2 =
        (j : ℝ) * literalStep (n + 1) + Real.log 2 + literalNuNodes (literalStep (n + 1)) k by ring]
      ring
    rw [he, literal_exp_translate_weighted _ _ (literalNu_exp_real ell),
      literal_exp_translate_weighted _ _ (literalNu_exp_real ell), literalNu_exp_weighted]
    rw [show ((j : ℝ) * ell + Real.log 2) / 2 =
      (j : ℝ) * ell / 2 + Real.log 2 / 2 by ring, Real.exp_add]
    dsimp [R]
    ring
  have hr : (∑ i : Fin (n + 1) × Fin 3 × Bool,
      (literalCoeffs (n + 1) i).re * literalNodes (n + 1) i *
        Real.exp (literalNodes (n + 1) i / 2)) =
      (ell / 2) * (1 - Real.exp (Real.log 2 / 2)) *
        (1 - Real.exp (ell / 2)) ^ n * (Real.exp (ell / 4) - 1) := by
    simp only [Fintype.sum_prod_type, hrow]
    rw [← Finset.sum_mul, ← Finset.sum_mul, literal_binomial_exp]
    dsimp [R]
    ring
  have hc := congrArg (fun z : ℝ => (z : ℂ)) hr
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, literalCoeffs_ofReal_re,
    Nat.add_sub_cancel_right, Nat.succ_sub_one, ell] using hc


def literalPair (x : I → ℝ) (a : I → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * f (t + x i - x j)

private lemma literal_correlation_pair (x : I → ℝ) (a : I → ℝ)
    (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ) :
    correlation x (fun i => (a i : ℂ)) t = -literalPair x a (fun s => max s 0) t := by
  rw [← correlation_neg x (fun i => (a i : ℂ)) t, literal_correlation_hinge x a ha]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show x i - x j - -t = t + x i - x j by ring]

lemma literal_S_pair (D : ℝ) (hD : 0 ≤ D) (x : I → ℝ) (a : I → ℝ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, (a i : ℂ) = 0) (t : ℝ) :
    S D x (fun i => (a i : ℂ)) t =
      -literalPair x a (fun s => max s 0 + Real.exp (-|s| / 2)) t := by
  rw [literal_S_finite D hD _ _ hx ha t, literal_correlation_pair x a ha t]
  have he : literalExpPair x (fun i => (a i : ℂ)) t =
      literalPair x a (fun s => Real.exp (-|s| / 2)) t := by
    simp only [literalExpPair, literalPair, Complex.re_sum, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [he]
  simp only [literalPair, mul_add, Finset.sum_add_distrib]
  ring

private lemma literalPair_translates {J : Type*} [Fintype J]
    (x : I → ℝ) (a : I → ℝ) (s b : J → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    literalPair (fun i : J × I => s i.1 + x i.2)
      (fun i => b i.1 * a i.2) f t =
    ∑ j, ∑ k, b j * b k * literalPair x a f (t + s j - s k) := by
  classical
  simp only [literalPair, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  rw [show t + (s j + x i) - (s k + x l) = t + s j - s k + x i - x l by ring]
  ring

private lemma literalPair_two (x : I → ℝ) (a : I → ℝ) (L t : ℝ) (f : ℝ → ℝ) :
    literalPair (fun i : I × Bool => x i.1 + if i.2 then L else 0)
      (fun i => a i.1 * if i.2 then -1 else 1) f t =
      2 * literalPair x a f t - literalPair x a f (t + L) - literalPair x a f (t - L) := by
  classical
  have he (i j : I) :
      (∑ b : Bool, ∑ c : Bool,
        (a i * if b then -1 else 1) * (a j * if c then -1 else 1) *
          f (t + (x i + if b then L else 0) - (x j + if c then L else 0))) =
      2 * (a i * a j * f (t + x i - x j)) -
        a i * a j * f (t + L + x i - x j) -
        a i * a j * f (t - L + x i - x j) := by
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, add_zero]
    rw [show t + (x i + L) - (x j + L) = t + x i - x j by ring,
      show t + (x i + L) - x j = t + L + x i - x j by ring,
      show t + x i - (x j + L) = t - L + x i - x j by ring]
    ring
  unfold literalPair
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ i, ∑ j, ∑ b : Bool, ∑ c : Bool,
        (a i * if b then -1 else 1) * (a j * if c then -1 else 1) *
          f (t + (x i + if b then L else 0) - (x j + if c then L else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by simp only [he, Finset.sum_sub_distrib, Finset.mul_sum]

private def literalBeta (q : ℕ) (j : Fin q) : ℝ :=
  (-1 : ℝ) ^ (j : ℕ) * ((q - 1).choose (j : ℕ) : ℝ)
def literalEtaNodes (q : ℕ) (i : Fin q × Fin 3) : ℝ :=
  (i.1 : ℝ) * literalStep q + literalNuNodes (literalStep q) i.2
def literalEtaCoeffs (q : ℕ) (i : Fin q × Fin 3) : ℝ :=
  literalBeta q i.1 * literalNuCoeffs (literalStep q) i.2
def literalN (q : ℕ) : ℝ := ∑ j : Fin q, literalBeta q j ^ 2

lemma literal_eta_mass (q : ℕ) :
    ∑ i, (literalEtaCoeffs q i : ℂ) = 0 := by
  simp only [literalEtaCoeffs, Fintype.sum_prod_type, Complex.ofReal_mul,
    ← Finset.mul_sum, literalNu_mass, mul_zero, Finset.sum_const_zero]

lemma literal_eta_exp (q : ℕ) :
    ∑ i, (literalEtaCoeffs q i : ℂ) * (Real.exp (literalEtaNodes q i / 2) : ℂ) = 0 := by
  have hr : ∑ i, literalEtaCoeffs q i * Real.exp (literalEtaNodes q i / 2) = 0 := by
    simp only [literalEtaCoeffs, literalEtaNodes, Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro j _
    simp only [mul_assoc]
    rw [← Finset.mul_sum, literal_exp_translate, literalNu_exp_real, mul_zero, mul_zero]
  exact_mod_cast hr

lemma literal_eta_support (q : ℕ) (hq : 1 ≤ q) (i : Fin q × Fin 3) :
    literalEtaNodes q i ∈ Icc (0 : ℝ) (1 / 16) := by
  have hl := literal_step_bounds q hq
  have hk := literalNu_support (literalStep q) hl.1.le i.2
  have hj : (i.1 : ℝ) + 1 ≤ q := by exact_mod_cast i.1.isLt
  constructor
  · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hl.1.le) hk.1
  · dsimp [literalEtaNodes]
    nlinarith [mul_le_mul_of_nonneg_right hj hl.1.le, hl.2.2, hk.2]

lemma literal_N_pos (q : ℕ) (hq : 1 ≤ q) : 0 < literalN q := by
  have hq0 : 0 < q := by omega
  apply Finset.sum_pos'
  · intro j _; exact sq_nonneg _
  · refine ⟨⟨0, hq0⟩, Finset.mem_univ _, ?_⟩
    simp [literalBeta]

private lemma literal_eta_correlation (q : ℕ) (t : ℝ) :
    correlation (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t =
      ∑ j : Fin q, ∑ k : Fin q, literalBeta q j * literalBeta q k *
        correlation (literalNuNodes (literalStep q))
          (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
          (t + (j : ℝ) * literalStep q - (k : ℝ) * literalStep q) := by
  rw [literal_correlation_pair _ _ (literal_eta_mass q)]
  change -literalPair (fun i : Fin q × Fin 3 => (i.1 : ℝ) * literalStep q +
      literalNuNodes (literalStep q) i.2)
    (fun i => literalBeta q i.1 * literalNuCoeffs (literalStep q) i.2) _ _ = _
  rw [literalPair_translates (literalNuNodes (literalStep q)) (literalNuCoeffs (literalStep q))
    (fun j : Fin q => (j : ℝ) * literalStep q) (literalBeta q)]
  simp only [literal_correlation_pair _ _ (literalNu_mass (literalStep q)), mul_neg,
    Finset.sum_neg_distrib]

private lemma literal_eta_S (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : 1 / 16 ≤ D) (t : ℝ) :
    S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t =
      ∑ j : Fin q, ∑ k : Fin q, literalBeta q j * literalBeta q k *
        S D (literalNuNodes (literalStep q))
          (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
          (t + (j : ℝ) * literalStep q - (k : ℝ) * literalStep q) := by
  have hl := literal_step_bounds q hq
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  rw [literal_S_pair D hD0 _ _ (fun i => ⟨(literal_eta_support q hq i).1,
    (literal_eta_support q hq i).2.trans hD⟩) (literal_eta_mass q)]
  change -literalPair (fun i : Fin q × Fin 3 => (i.1 : ℝ) * literalStep q +
      literalNuNodes (literalStep q) i.2)
    (fun i => literalBeta q i.1 * literalNuCoeffs (literalStep q) i.2) _ _ = _
  rw [literalPair_translates (literalNuNodes (literalStep q)) (literalNuCoeffs (literalStep q))
    (fun j : Fin q => (j : ℝ) * literalStep q) (literalBeta q)]
  simp only [literal_S_pair D hD0 _ _ (fun i => ⟨(literalNu_support _ hl.1.le i).1,
    (literalNu_support _ hl.1.le i).2.trans (hl.2.1.trans hD)⟩)
      (literalNu_mass (literalStep q)), mul_neg, Finset.sum_neg_distrib]


private lemma literal_correlation_tail (H : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) H) (ha : ∑ i, a i = 0)
    (t : ℝ) (ht : H ≤ |t|) : correlation x a t = 0 := by
  have hp (s : ℝ) (hs : H ≤ s) : correlation x a s = 0 := by
    have hh := congrArg Complex.re (shifted_hinge_prefix_energy x a ha s).2.2.1
    have hz (i j : I) : max (x i - x j - s) 0 = 0 :=
      max_eq_right (by linarith [(hx i).2, (hx j).1])
    simp only [hz, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero,
      Complex.zero_re, Complex.neg_re] at hh
    change 0 = -correlation x a s at hh
    linarith only [hh]
  rcases le_total 0 t with ht0 | ht0
  · exact hp t (by simpa only [abs_of_nonneg ht0] using ht)
  · rw [← correlation_neg x a t]
    exact hp (-t) (by simpa only [abs_of_nonpos ht0] using ht)

private lemma literal_spacing (q : ℕ) (hq : 1 ≤ q) (j k : Fin q) (hjk : j ≠ k) :
    literalStep q ≤ |(j : ℝ) * literalStep q - (k : ℝ) * literalStep q| := by
  have hl := (literal_step_bounds q hq).1
  have hv : (j : ℕ) ≠ (k : ℕ) := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · have hr : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    rw [abs_of_nonpos (by nlinarith : (j : ℝ) * literalStep q - (k : ℝ) * literalStep q ≤ 0)]
    nlinarith
  · have hr : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by nlinarith : 0 ≤ (j : ℝ) * literalStep q - (k : ℝ) * literalStep q)]
    nlinarith

private lemma literal_diagonal {J : Type*} [Fintype J] (b s : J → ℝ) (F : ℝ → ℝ)
    (hf : ∀ j k, j ≠ k → F (s j - s k) = 0) :
    (∑ j, ∑ k, b j * b k * F (0 + s j - s k)) = (∑ j, b j ^ 2) * F 0 := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp only [zero_add, sub_self, pow_two]
  · intro k _ hkj
    rw [zero_add, hf j k (Ne.symm hkj), mul_zero]
  · simp

private lemma literal_eta_energy (q : ℕ) (hq : 1 ≤ q) :
    energy (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) =
      literalN q * (literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2) := by
  rw [← literal_correlation_zero _ _ (literal_eta_mass q), literal_eta_correlation]
  have hz (j k : Fin q) (hjk : j ≠ k) :
      correlation (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
        ((j : ℝ) * literalStep q - (k : ℝ) * literalStep q) = 0 :=
    literal_correlation_tail _ _ _ (literalNu_support _ (literal_step_bounds q hq).1.le)
      (literalNu_mass _) _ (literal_spacing q hq j k hjk)
  rw [literal_diagonal _ _ _ hz, literal_correlation_zero _ _ (literalNu_mass _),
    literalNu_energy _ (literal_step_bounds q hq).1.le]
  rfl

lemma literal_eta_W (q : ℕ) (hq : 1 ≤ q) (D : ℝ) (hD : 1 / 16 ≤ D) :
    W D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) =
      literalN q * W D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ)) := by
  have hl := literal_step_bounds q hq
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  rw [W, literal_eta_S q hq D hD]
  have hz (j k : Fin q) (hjk : j ≠ k) :
      S D (literalNuNodes (literalStep q))
        (fun i => (literalNuCoeffs (literalStep q) i : ℂ))
        ((j : ℝ) * literalStep q - (k : ℝ) * literalStep q) = 0 :=
    literal_S_tail D (literalStep q) hD0 _ _
      (fun i => ⟨(literalNu_support _ hl.1.le i).1,
        (literalNu_support _ hl.1.le i).2.trans (hl.2.1.trans hD)⟩)
      (literalNu_support _ hl.1.le) (literalNu_mass _) (literalNu_exp _) _
      (literal_spacing q hq j k hjk)
  rw [literal_diagonal _ _ _ hz]
  rfl

private lemma literal_two_pair (q : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    literalPair (literalNodes q) (fun i => (literalCoeffs q i).re) f t =
      2 * literalPair (literalEtaNodes q) (literalEtaCoeffs q) f t -
        literalPair (literalEtaNodes q) (literalEtaCoeffs q) f (t + Real.log 2) -
        literalPair (literalEtaNodes q) (literalEtaCoeffs q) f (t - Real.log 2) := by
  have h := literalPair_two (literalEtaNodes q) (literalEtaCoeffs q) (Real.log 2) t f
  simpa only [literalPair, Fintype.sum_prod_type, literalNodes, literalCoeffs,
    literalEtaNodes, literalEtaCoeffs, literalBeta, Complex.ofReal_re, mul_assoc] using h

private lemma literal_mass (q : ℕ) (hq : 1 ≤ q) :
    ∑ i, literalCoeffs q i = 0 := by
  simpa only [pow_zero, mul_one] using literal_moments q hq 0 (Nat.zero_le _)

lemma literal_support_D (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) (i : Fin q × Fin 3 × Bool) :
    literalNodes q i ∈ Icc (0 : ℝ) D := by
  rcases literal_support q hq i with h | h
  · exact ⟨h.1, by linarith [h.2, Real.log_pos (by norm_num : (1 : ℝ) < 2)]⟩
  · exact ⟨le_trans (Real.log_pos (by norm_num)).le h.1, h.2.trans hD⟩

lemma literal_two_S (q : ℕ) (hq : 1 ≤ q) (D : ℝ)
    (hD : Real.log 2 + 1 / 16 ≤ D) (t : ℝ) :
    S D (literalNodes q) (literalCoeffs q) t =
      2 * S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) t -
        S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) (t + Real.log 2) -
        S D (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) (t - Real.log 2) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ D := by linarith
  have hx := literal_support_D q hq D hD
  have hxe : ∀ i, literalEtaNodes q i ∈ Icc (0 : ℝ) D :=
    fun i => ⟨(literal_eta_support q hq i).1, by linarith [(literal_eta_support q hq i).2]⟩
  have hreal : (fun i => ((literalCoeffs q i).re : ℂ)) = literalCoeffs q :=
    funext (literalCoeffs_ofReal_re q)
  rw [← hreal, literal_S_pair D hD0 _ _ hx (by simpa only [hreal] using literal_mass q hq),
    literal_two_pair]
  simp only [literal_S_pair D hD0 _ _ hxe (literal_eta_mass q)]
  ring

lemma literal_energy_double (q : ℕ) (hq : 1 ≤ q) :
    energy (literalNodes q) (literalCoeffs q) =
      2 * literalN q * (literalStep q * (1 + Real.exp (-literalStep q / 4) ^ 2) / 2) := by
  have hL : 1 / 16 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hr : (fun i => ((literalCoeffs q i).re : ℂ)) = literalCoeffs q :=
    funext (literalCoeffs_ofReal_re q)
  rw [← literal_correlation_zero _ _ (literal_mass q hq), ← hr,
    literal_correlation_pair _ _ (by simpa only [hr] using literal_mass q hq), literal_two_pair]
  have he (s : ℝ) : -literalPair (literalEtaNodes q) (literalEtaCoeffs q)
      (fun z => max z 0) s =
      correlation (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) s :=
    (literal_correlation_pair _ _ (literal_eta_mass q) s).symm
  have hz (s : ℝ) (hs : 1 / 16 ≤ |s|) :
      correlation (literalEtaNodes q) (fun i => (literalEtaCoeffs q i : ℂ)) s = 0 :=
    literal_correlation_tail _ _ _ (literal_eta_support q hq) (literal_eta_mass q) s hs
  have hp := hz (Real.log 2) (by rwa [abs_of_nonneg (by linarith)])
  have hn := hz (-Real.log 2) (by rwa [abs_neg, abs_of_nonneg (by linarith)])
  have h0 := he 0
  have h1 := he (Real.log 2)
  have h2 := he (-Real.log 2)
  rw [literal_correlation_zero _ _ (literal_eta_mass q), literal_eta_energy q hq] at h0
  simp only [zero_add, zero_sub] at *
  linarith only [hp, hn, h0, h1, h2]


end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
