/- GID: D5/S3/CharacterSums/DirichletCompletion
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conductor-normalized Dirichlet completions satisfy symmetry and global growth bounds. -/

import D5.S3.CharacterSums.NonprincipalCharacterGrowth
import Mathlib.NumberTheory.LSeries.Nonvanishing
import D5.S3.CharacterSums.DirichletCompletionGamma
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Conductor-normalized Dirichlet completions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace D5.S3.CharacterSums.DirichletCompletion

/-- The conductor-normalized completion. -/
def completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) * χ.completedLFunction s

/-- Nonprincipal completions are entire, without a primitivity hypothesis. -/
theorem differentiable_completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) : Differentiable ℂ (completion χ) := by
  exact ((differentiable_const _).mul differentiable_id).cexp.mul
    (DirichletCharacter.differentiable_completedLFunction hne)

/-- The conductor factor removes the variable power in the functional equation. -/
theorem completion_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completion χ (1 - s) = χ.rootNumber * completion χ⁻¹ s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hc : Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (1 - s)) *
      (q : ℂ) ^ (s - 1 / 2) =
      Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero hq,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only [completion]
  rw [hχ.completedLFunction_one_sub]
  calc
    _ = (Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (1 - s)) *
        (q : ℂ) ^ (s - 1 / 2)) * χ.rootNumber * χ⁻¹.completedLFunction s := by ring
    _ = _ := by rw [hc]; ring

/-- The completion is nonzero on the closed right half-plane, except at a principal pole. -/
theorem completion_ne_zero_of_one_le_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    completion χ s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hL := χ.LFunction_ne_zero_of_one_le_re hχs hs
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro h
  exact hL (by rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0), h, zero_div])

/-- Primitive root numbers are nonzero for every positive modulus. -/
theorem rootNumber_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have he := completion_one_sub hχ (-1)
  rw [h, zero_mul] at he
  have hn := completion_ne_zero_of_one_le_re χ (s := 2) (.inr (by norm_num))
    (by norm_num)
  exact hn (by convert he using 1 <;> norm_num)

/-- Nonprincipal primitive completions are also nonzero on the closed left half-plane. -/
theorem completion_ne_zero_of_re_le_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : s.re ≤ 0) : completion χ s ≠ 0 := by
  have hni : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hn := completion_ne_zero_of_one_le_re χ⁻¹ (s := 1 - s) (.inl hni)
    (by simp only [sub_re, one_re]; linarith)
  have he := completion_one_sub hχ (1 - s)
  rw [sub_sub_cancel] at he
  rw [he]
  exact mul_ne_zero (rootNumber_ne_zero hχ) hn

private theorem gammaFactor_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

private theorem completed_eq_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    χ.completedLFunction s = χ.gammaFactor s * χ.LFunction s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have he := (div_eq_iff (gammaFactor_ne_zero χ hs)).mp
    (χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0)).symm
  exact he.trans (mul_comm _ _)

private theorem gammaFactor_inv_conj {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    χ⁻¹.gammaFactor (conj s) = conj (χ.gammaFactor s) := by
  classical
  have hi (x : ZMod q) : χ⁻¹ x = conj (χ x) := (MulChar.star_apply' χ x).symm
  have he : χ⁻¹.Even ↔ χ.Even := by
    simp only [DirichletCharacter.Even, hi]
    constructor
    · intro h
      simpa using congrArg conj h
    · intro h
      simp [h]
  simp only [DirichletCharacter.gammaFactor, he]
  split_ifs
  · exact Complex.Gammaℝ_conj s
  · simpa using Complex.Gammaℝ_conj (s + 1)

private theorem LFunction_inv_conj_right {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    χ⁻¹.LFunction (conj s) = conj (χ.LFunction s) := by
  rw [χ⁻¹.LFunction_eq_LSeries (by simpa using hs), χ.LFunction_eq_LSeries hs,
    LSeries, LSeries, Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀]
  congr 1
  · exact (MulChar.star_apply' χ _).symm
  · have ha : (n : ℂ).arg ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    simpa using Complex.cpow_conj (n : ℂ) s ha

private theorem completion_conj_right {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    completion χ⁻¹ (conj s) = conj (completion χ s) := by
  have hp : 0 < s.re := by linarith
  dsimp only [completion]
  rw [completed_eq_mul χ hp, completed_eq_mul χ⁻¹ (by simpa using hp),
    gammaFactor_inv_conj, LFunction_inv_conj_right χ hs, map_mul, map_mul,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

/-- Conjugation exchanges a nonprincipal character and its inverse. -/
theorem completion_inv_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (s : ℂ) :
    completion χ⁻¹ (conj s) = conj (completion χ s) := by
  let g : ℂ → ℂ := fun z => conj (completion χ (conj z))
  have hd : Differentiable ℂ g := by
    intro z
    simpa [g, Function.comp_def] using
      (differentiable_completion χ hne (conj z)).conj_conj
  have hg : completion χ⁻¹ = g :=
    ((differentiable_completion χ⁻¹ (inv_ne_one.mpr hne)).differentiableOn.analyticOnNhd
      isOpen_univ).eq_of_eventuallyEq
      (hd.differentiableOn.analyticOnNhd isOpen_univ) (by
        filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
          (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
        simpa [g] using completion_conj_right χ (s := conj z) (by simpa using hz))
  simpa [g] using congrFun hg (conj s)

/-- Every primitive character has a root number of unit norm. -/
theorem norm_rootNumber {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : ‖χ.rootNumber‖ = 1 := by
  by_cases hne : χ = 1
  · have hq : q = 1 := by
      simpa only [DirichletCharacter.IsPrimitive, hne,
        DirichletCharacter.conductor_one] using hχ.symm
    subst q
    rw [DirichletCharacter.rootNumber_modOne, norm_one]
  have hi (t : ℝ) : ‖completion χ⁻¹ t‖ = ‖completion χ t‖ := by
    have h := congrArg norm (completion_inv_conj χ hne (t : ℂ))
    simpa using h
  have ha := congrArg norm (completion_one_sub hχ (-1))
  have hb := congrArg norm (completion_one_sub hχ 2)
  norm_num only [show (1 : ℂ) - -1 = 2 by norm_num,
    show (1 : ℂ) - 2 = -1 by norm_num, norm_mul] at ha hb
  have him : ‖completion χ⁻¹ (-1)‖ = ‖completion χ (-1)‖ := by simpa using hi (-1)
  have hi2 : ‖completion χ⁻¹ 2‖ = ‖completion χ 2‖ := by simpa using hi 2
  rw [him] at ha
  rw [hi2] at hb
  have hp : 0 < ‖completion χ (-1)‖ := norm_pos_iff.mpr
    (completion_ne_zero_of_re_le_zero hχ hne (by norm_num))
  have hsq : ‖χ.rootNumber‖ ^ 2 = 1 := by
    have he : (‖χ.rootNumber‖ ^ 2 - 1) * ‖completion χ (-1)‖ = 0 := by
      rw [ha] at hb
      nlinarith only [hb]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hp.ne')
  nlinarith [norm_nonneg χ.rootNumber]

/-- The fixed constant in the archimedean estimate. -/
def gammaConstant : ℝ := max 1 (Real.Gamma (1 / 4))

/-- An explicit coefficient for the logarithmic global growth estimate. -/
def growthConstant (q : ℕ) : ℝ :=
  max (Real.log (gammaConstant * (q.totient : ℝ)) +
    Real.log (q : ℝ) / 2 + 2 * Real.log 2) 3

private theorem gamma_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} {R : ℝ} (hs : 1 / 2 ≤ s.re) (hR : 1 ≤ R) (hn : ‖s‖ ≤ R) :
    ‖χ.gammaFactor s‖ ≤ gammaConstant *
      Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  classical
  have hb (t : ℂ) (ht : 1 / 2 ≤ t.re) (htR : t.re ≤ R + 1) :
      ‖Complex.Gammaℝ t‖ ≤ gammaConstant *
        Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
    have ht0 : 0 < t.re := by linarith
    have hp : Real.pi ^ (-t.re / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi) (by linarith)
    have hx : 1 ≤ t.re / 2 + 1 := by linarith
    have hU : t.re / 2 + 1 ≤ (R + 3) / 2 := by linarith
    have hl := Real.log_le_log (by linarith : 0 < t.re / 2 + 1) hU
    have hg := DirichletCompletionGamma.Gamma_le_exp_bound
      (u := t.re / 2) (by linarith)
    calc
      _ ≤ Real.pi ^ (-t.re / 2) * Real.Gamma (t.re / 2) :=
        DirichletCompletionGamma.norm_GammaReal_le ht0
      _ ≤ Real.Gamma (t.re / 2) :=
        mul_le_of_le_one_left (Real.Gamma_pos_of_pos (by linarith)).le hp
      _ ≤ _ := hg.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul hU hl (Real.log_nonneg hx)
          (by linarith))) (by positivity))
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact hb s hs ((Complex.re_le_norm s).trans (hn.trans (by linarith)))
  · apply hb (s + 1)
    · simp only [add_re, one_re]; linarith
    · simp only [add_re, one_re]; linarith [Complex.re_le_norm s]

private theorem right_growth_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ} {R : ℝ}
    (hs : 1 / 2 ≤ s.re) (hR : 1 ≤ R) (hn : ‖s‖ ≤ R) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * R *
      Real.exp (Real.log (q : ℝ) / 2 * R +
        ((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  have hp : 0 < s.re := by linarith
  have hq : 0 ≤ Real.log (q : ℝ) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact Real.log_nonneg (by exact_mod_cast NeZero.one_le (n := q))
  have hL : ‖χ.LFunction s‖ < (q.totient : ℝ) * R := by
    refine (NonprincipalCharacterGrowth.nonprincipal_growth χ hne hp).trans_le ?_
    calc
      _ ≤ (q.totient : ℝ) * ‖s‖ := by
        apply (div_le_iff₀ hp).mpr
        have hh := mul_nonneg (Nat.cast_nonneg q.totient) (norm_nonneg s)
        nlinarith only [mul_nonneg hh (sub_nonneg.mpr hs)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
  have hE : Real.exp (Real.log (q : ℝ) / 2 * s.re) ≤
      Real.exp (Real.log (q : ℝ) / 2 * R) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      ((Complex.re_le_norm s).trans hn) hq)
  have hG := gamma_bound χ hs hR hn
  have hG0 : 0 < ‖χ.gammaFactor s‖ := norm_pos_iff.mpr (gammaFactor_ne_zero χ hp)
  rw [completion, completed_eq_mul χ hp, norm_mul, norm_mul, Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  calc
    _ < (Real.exp (Real.log (q : ℝ) / 2 * s.re) * ‖χ.gammaFactor s‖) *
        ((q.totient : ℝ) * R) := by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_left hL
        (mul_pos (Real.exp_pos _) hG0)
    _ ≤ (Real.exp (Real.log (q : ℝ) / 2 * R) *
        (gammaConstant * Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)))) *
        ((q.totient : ℝ) * R) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hE hG (norm_nonneg _)
        (Real.exp_pos _).le) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

/-- A global bound retaining the radial Gamma argument and its multiplicative constant. -/
theorem completion_growth_explicit {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * (1 + ‖s‖) *
      Real.exp (Real.log (q : ℝ) / 2 * (1 + ‖s‖) +
        ((‖s‖ + 4) / 2) * Real.log ((‖s‖ + 4) / 2)) := by
  have hR : 1 ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  by_cases hs : 1 / 2 ≤ s.re
  · convert right_growth_radius χ hne hs hR
      (show ‖s‖ ≤ 1 + ‖s‖ by linarith) using 1 <;> ring_nf
  · have ht : 1 / 2 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hn : ‖1 - s‖ ≤ 1 + ‖s‖ := by simpa using norm_sub_le (1 : ℂ) s
    have hb := right_growth_radius χ⁻¹ (inv_ne_one.mpr hne) ht hR hn
    have he := congrArg norm (completion_one_sub hχ (1 - s))
    rw [sub_sub_cancel, norm_mul, norm_rootNumber hχ, one_mul] at he
    rw [he]
    convert hb using 1 <;> ring_nf

/-- The completion has an explicit global bound of size exp(C R (1 + log R)). -/
theorem completion_growth_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    ‖completion χ s‖ < Real.exp
      (growthConstant q * (1 + ‖s‖) * (1 + Real.log (1 + ‖s‖))) := by
  let R := 1 + ‖s‖
  let A := gammaConstant * (q.totient : ℝ)
  let b := Real.log (q : ℝ) / 2
  let U := (‖s‖ + 4) / 2
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hRp : 0 < R := by linarith
  have hA : 1 ≤ A := by
    apply one_le_mul_of_one_le_of_one_le
    · exact le_max_left _ _
    · exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hAp : 0 < A := by linarith
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  have hU : 1 ≤ U := by dsimp [U, R] at *; linarith
  have hUR : U ≤ 2 * R := by dsimp [U, R] at *; linarith
  have hlU : Real.log U ≤ Real.log 2 + Real.log R := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
    exact Real.log_le_log (by linarith) hUR
  have hUl : U * Real.log U ≤ 2 * R * (Real.log 2 + Real.log R) :=
    mul_le_mul hUR hlU (Real.log_nonneg hU) (by linarith)
  have hC : Real.log A + b + 2 * Real.log 2 ≤ growthConstant q := le_max_left _ _
  have hC3 : 3 ≤ growthConstant q := le_max_right _ _
  have hAlog : Real.log A ≤ Real.log A * R := le_mul_of_one_le_right hlA hR
  have hRlog : Real.log R ≤ R * Real.log R := le_mul_of_one_le_left hlR hR
  have he : Real.log A + Real.log R + (b * R + U * Real.log U) ≤
      growthConstant q * R * (1 + Real.log R) := by
    calc
      _ ≤ (Real.log A + b + 2 * Real.log 2) * R + 3 * (R * Real.log R) := by
        nlinarith only [hUl, hAlog, hRlog]
      _ ≤ growthConstant q * R + growthConstant q * (R * Real.log R) :=
        add_le_add (mul_le_mul_of_nonneg_right hC hRp.le)
          (mul_le_mul_of_nonneg_right hC3 (mul_nonneg hRp.le hlR))
      _ = _ := by ring
  refine (completion_growth_explicit hχ hne s).trans_le ?_
  change A * R * Real.exp (b * R + U * Real.log U) ≤ _
  calc
    _ = Real.exp (Real.log A + Real.log R + (b * R + U * Real.log U)) := by
      simp only [Real.exp_add, Real.exp_log hAp, Real.exp_log hRp]
    _ ≤ _ := Real.exp_le_exp.mpr he

end D5.S3.CharacterSums.DirichletCompletion
