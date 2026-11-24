/- GID: D5/S3/CharacterSums/DirichletCompletion
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Modulus-normalized Dirichlet completions satisfy symmetry and global growth bounds. -/

import D5.S3.CharacterSums.NonprincipalCharacterGrowth
import Mathlib.NumberTheory.LSeries.Nonvanishing
import D5.S3.CharacterSums.DirichletCompletionGamma
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Real.Pi.Bounds
import D5.S3.Weil.ZetaExplicit.GammaRBracket
import D5.S3.Weil.ZetaSeam.ZetaReflect
import D5.S3.Weil.ZetaExplicit.XiLogDeriv
import D5.S3.Analytic.Resolvent.EntireLogDerivDifference

/-! # Modulus-normalized Dirichlet completions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate Classical
open ConjectureMachines.Semantics.Riemann.DigammaBinet

namespace D5.S3.CharacterSums.DirichletCompletion

/-- The modulus-normalized completion. -/
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
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1 ∨ q = 1) (hs : 1 ≤ s.re) :
    completion χ s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hL : χ.LFunction s ≠ 0 := by
    rcases hχs with hne | hs1 | hq1
    · exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs
    · exact χ.LFunction_ne_zero_of_one_le_re (.inr hs1) hs
    · subst q
      rw [DirichletCharacter.LFunction_modOne_eq]
      by_cases hs1 : s = 1
      · simpa [hs1] using riemannZeta_one_ne_zero
      · exact riemannZeta_ne_zero_of_one_le_re hs
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro h
  exact hL (by rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0), h, zero_div])

/-- Primitive root numbers are nonzero for every positive modulus. -/
theorem rootNumber_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have he := completion_one_sub hχ (-1)
  rw [h, zero_mul] at he
  have hn := completion_ne_zero_of_one_le_re χ (s := 2) (.inr (.inl (by norm_num)))
    (by norm_num)
  exact hn (by convert he using 1 <;> norm_num)

/-- Primitive completions are nonzero on the closed left half-plane. -/
theorem completion_ne_zero_of_re_le_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive)
    {s : ℂ} (hs : s.re ≤ 0) : completion χ s ≠ 0 := by
  have hni : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 ∨ q = 1 := by
    by_cases hne : χ = 1
    · right; right
      simpa only [DirichletCharacter.IsPrimitive, hne,
        DirichletCharacter.conductor_one] using hχ.symm
    · exact .inl (inv_ne_one.mpr hne)
  have hn := completion_ne_zero_of_one_le_re χ⁻¹ (s := 1 - s) hni
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

private theorem mellin_conj_real (f : ℝ → ℂ) (hf : ∀ t, conj (f t) = f t)
    (s : ℂ) : mellin f (conj s) = conj (mellin f s) := by
  rw [mellin, mellin, ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul, map_mul]
  rw [hf]
  have htarg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht.le]
    exact Real.pi_pos.ne
  rw [show conj s - 1 = conj (s - 1) by simp,
    cpow_conj (t : ℂ) (s - 1) htarg]
  simp

private theorem hurwitz_conj (a : UnitAddCircle) (s : ℂ) :
    HurwitzZeta.completedHurwitzZetaEven a (conj s) =
      conj (HurwitzZeta.completedHurwitzZetaEven a s) ∧
    HurwitzZeta.completedHurwitzZetaOdd a (conj s) =
      conj (HurwitzZeta.completedHurwitzZetaOdd a s) := by
  have he (z : ℂ) :
      (HurwitzZeta.hurwitzEvenFEPair a).Λ₀ (conj z) =
        conj ((HurwitzZeta.hurwitzEvenFEPair a).Λ₀ z) := by
    apply mellin_conj_real
    intro t
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      Function.comp_apply, smul_eq_mul, one_mul]
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> by_cases hu : t ∈ Ioo (0 : ℝ) 1 <;>
      by_cases ha : a = 0 <;> simp [ht, hu, ha]
  have ho (z : ℂ) :
      (HurwitzZeta.hurwitzOddFEPair a).Λ₀ (conj z) =
        conj ((HurwitzZeta.hurwitzOddFEPair a).Λ₀ z) := by
    apply mellin_conj_real
    intro t
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzOddFEPair,
      Function.comp_apply, smul_eq_mul, one_mul, sub_zero, mul_zero]
    by_cases ht : t ∈ Ioi (1 : ℝ) <;> by_cases hu : t ∈ Ioo (0 : ℝ) 1 <;>
      simp [ht, hu]
  constructor
  · unfold HurwitzZeta.completedHurwitzZetaEven WeakFEPair.Λ
    rw [show conj s / 2 = conj (s / 2) by simp [map_ofNat], he]
    by_cases ha : a = 0 <;> simp [map_ofNat, HurwitzZeta.hurwitzEvenFEPair, ha]
  · unfold HurwitzZeta.completedHurwitzZetaOdd WeakFEPair.Λ
    rw [show (conj s + 1) / 2 = conj ((s + 1) / 2) by simp [map_ofNat], ho]
    simp [map_ofNat, HurwitzZeta.hurwitzOddFEPair]

/-- Conjugation exchanges any character and its inverse, including totalized pole values. -/
theorem completion_inv_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) : completion χ⁻¹ (conj s) = conj (completion χ s) := by
  have hqarg : (q : ℂ).arg ≠ Real.pi := by
    rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg q)]
    exact Real.pi_pos.ne
  have hc : (q : ℂ) ^ (-conj s) = conj ((q : ℂ) ^ (-s)) := by
    simpa using Complex.cpow_conj (q : ℂ) (-s) hqarg
  unfold completion DirichletCharacter.completedLFunction ZMod.completedLFunction
  rw [show (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * conj s) =
      conj (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) by rw [map_mul, Complex.conj_ofReal],
    Complex.exp_conj, hc]
  simp only [map_mul, map_add, map_sum]
  congr 2 <;> congr 1 <;> apply Finset.sum_congr rfl <;> intro j _
  · rw [(MulChar.star_apply' χ j).symm, (hurwitz_conj _ s).1]
    rfl
  · rw [(MulChar.star_apply' χ j).symm, (hurwitz_conj _ s).2]
    rfl

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
    have h := congrArg norm (completion_inv_conj χ (t : ℂ))
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
    (completion_ne_zero_of_re_le_zero hχ (by norm_num))
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
    {s : ℂ} {R : ℝ} (hs : 1 / 2 ≤ s.re) (hn : ‖s‖ ≤ R) :
    ‖χ.gammaFactor s‖ ≤ gammaConstant *
      Real.exp (((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  classical
  have hR : 1 / 2 ≤ R := hs.trans ((Complex.re_le_norm s).trans hn)
  have hB : 0 ≤ gammaConstant := (zero_le_one.trans (le_max_left _ _))
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
    have hg' : Real.Gamma (t.re / 2) ≤ gammaConstant *
        Real.exp ((t.re / 2 + 1) * Real.log (t.re / 2 + 1)) := by
      have hmax := hg.elim (fun h => h.trans (le_max_left _ _))
        (fun h => h.le.trans (le_max_right _ _))
      refine hmax.trans (max_le ?_ ?_)
      · exact (le_max_right 1 _).trans (le_mul_of_one_le_right
          (show 0 ≤ gammaConstant from hB) (Real.one_le_exp
            (mul_nonneg (by linarith) (Real.log_nonneg hx))))
      · exact le_mul_of_one_le_left (Real.exp_pos _).le (le_max_left _ _)
    calc
      _ ≤ Real.pi ^ (-t.re / 2) * Real.Gamma (t.re / 2) :=
        DirichletCompletionGamma.norm_GammaReal_le ht0
      _ ≤ Real.Gamma (t.re / 2) :=
        mul_le_of_le_one_left (Real.Gamma_pos_of_pos (by linarith)).le hp
      _ ≤ _ := hg'.trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul hU hl (Real.log_nonneg hx)
          (by linarith))) hB)
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact hb s hs ((Complex.re_le_norm s).trans (hn.trans (by linarith)))
  · apply hb (s + 1)
    · simp only [add_re, one_re]; linarith
    · simp only [add_re, one_re]; linarith [Complex.re_le_norm s]

theorem right_growth_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) {s : ℂ} {R : ℝ}
    (hs : 1 / 2 ≤ s.re) (hn : ‖s‖ ≤ R) :
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
  have hG := gamma_bound χ hs hn
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
        (Real.exp_pos _).le) (mul_nonneg (Nat.cast_nonneg _)
          (by linarith [hs.trans ((Complex.re_le_norm s).trans hn)]))
    _ = _ := by rw [Real.exp_add]; ring

/-- A free-radius bound; primitivity is needed only when reflection is used. -/
theorem completion_growth_radius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) (R : ℝ)
    (hside : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) (hn : 1 / 2 ≤ s.re → ‖s‖ ≤ R)
    (href : s.re < 1 / 2 → ‖1 - s‖ ≤ R) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * R *
      Real.exp (Real.log (q : ℝ) / 2 * R +
        ((R + 3) / 2) * Real.log ((R + 3) / 2)) := by
  by_cases hs : 1 / 2 ≤ s.re
  · exact right_growth_radius χ hne hs (hn hs)
  · have hχ := hside.resolve_left hs
    have ht : 1 / 2 ≤ (1 - s).re := by simp only [sub_re, one_re]; linarith
    have hb := right_growth_radius χ⁻¹ (inv_ne_one.mpr hne) ht (href (lt_of_not_ge hs))
    have he := congrArg norm (completion_one_sub hχ (1 - s))
    rw [sub_sub_cancel, norm_mul, norm_rootNumber hχ, one_mul] at he
    rwa [he]

/-- A global bound retaining the radial Gamma argument and its multiplicative constant. -/
theorem completion_growth_explicit {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (s : ℂ) (hχ : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) :
    ‖completion χ s‖ < gammaConstant * (q.totient : ℝ) * (1 + ‖s‖) *
      Real.exp (Real.log (q : ℝ) / 2 * (1 + ‖s‖) +
        ((‖s‖ + 4) / 2) * Real.log ((‖s‖ + 4) / 2)) := by
  convert completion_growth_radius χ hne s (1 + ‖s‖) hχ
    (fun _ => by linarith) (fun _ => by simpa using norm_sub_le (1 : ℂ) s) using 1 <;> ring_nf

/-- The completion has an explicit global bound of size exp(C R (1 + log R)). -/
theorem completion_growth_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (s : ℂ) (hχ : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) :
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
  refine (completion_growth_explicit hne s hχ).trans_le ?_
  change A * R * Real.exp (b * R + U * Real.log U) ≤ _
  calc
    _ = Real.exp (Real.log A + Real.log R + (b * R + U * Real.log U)) := by
      simp only [Real.exp_add, Real.exp_log hAp, Real.exp_log hRp]
    _ ≤ _ := Real.exp_le_exp.mpr he

theorem completion_power_growth {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) (s : ℂ) (hside : 1 / 2 ≤ s.re ∨ χ.IsPrimitive) :
    ‖completion χ s‖ < Real.exp (3 * growthConstant q * (1 + ‖s‖) ^ (3 / 2 : ℝ)) := by
  let R := 1 + ‖s‖
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hp : 0 < R := by linarith
  have hroot : 1 ≤ R ^ (1 / 2 : ℝ) := Real.one_le_rpow hR (by norm_num)
  have hl : Real.log R ≤ 2 * R ^ (1 / 2 : ℝ) := by
    have hh := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hC : 0 ≤ growthConstant q := (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_right _ _)
  refine (completion_growth_log hne s hside).trans_le (Real.exp_le_exp.mpr ?_)
  change growthConstant q * R * (1 + Real.log R) ≤ _
  have he : R ^ (3 / 2 : ℝ) = R * R ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp, Real.rpow_one]
  change _ ≤ 3 * growthConstant q * R ^ (3 / 2 : ℝ)
  rw [he]
  nlinarith [mul_nonneg (mul_nonneg hC hp.le) (by linarith :
    0 ≤ 3 * R ^ (1 / 2 : ℝ) - (1 + Real.log R))]

/-- Nonprincipal completions have finite order at every point, and positive order at zeros. -/
theorem completion_zero_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (ρ : ℂ) : analyticOrderAt (completion χ) ρ ≠ ⊤ ∧
      (completion χ ρ = 0 ↔ 0 < analyticOrderNatAt (completion χ) ρ) := by
  have ha := (differentiable_completion χ hne).analyticAt
  have hn := completion_ne_zero_of_one_le_re χ (s := 2) (.inl hne) (by norm_num)
  have han : AnalyticOnNhd ℂ (completion χ) Set.univ := fun z _ => ha z
  have hf : analyticOrderAt (completion χ) ρ ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ 2) (mem_univ ρ)
      (by rw [(ha 2).analyticOrderAt_eq_zero.mpr hn]; simp)
  refine ⟨hf, ?_⟩
  rw [Nat.pos_iff_ne_zero, analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero]
  simp only [not_or, hf, not_false_eq_true, and_true]
  exact (ha ρ).analyticOrderAt_ne_zero.symm

/-- Every zero of a primitive completion lies in the open critical strip. -/
theorem completion_zero_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {ρ : ℂ} (hρ : completion χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra! h
    exact completion_ne_zero_of_re_le_zero hχ h hρ
  · by_contra! h
    have hn : χ ≠ 1 ∨ ρ ≠ 1 ∨ q = 1 := by
      by_cases hc : χ = 1
      · right; right
        simpa only [DirichletCharacter.IsPrimitive, hc,
          DirichletCharacter.conductor_one] using hχ.symm
      · exact .inl hc
    exact completion_ne_zero_of_one_le_re χ hn h hρ

/-- Reflection in the critical line is conjugate covariance with the root number. -/
theorem completion_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completion χ (1 - conj s) = χ.rootNumber * conj (completion χ s) := by
  rw [completion_one_sub hχ, completion_inv_conj]

/-- Critical-line reflection preserves the zero divisor, including analytic multiplicity. -/
theorem completion_reflect_order {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    (completion χ (1 - conj s) = 0 ↔ completion χ s = 0) ∧
    analyticOrderAt (completion χ) (1 - conj s) =
      analyticOrderAt (completion χ) s := by
  have hFi := differentiable_completion χ⁻¹ (inv_ne_one.mpr hne)
  have hi : analyticOrderAt (completion χ⁻¹) (conj s) =
      analyticOrderAt (completion χ) s := by
    have he : completion χ⁻¹ = fun z => conj (completion χ (conj z)) := by
      funext z
      simpa using completion_inv_conj χ (conj z)
    rw [he]
    exact Zeta23.analyticOrderAt_conj_conj (completion χ) s
  have heq : (fun z : ℂ => completion χ (1 - z)) =
      fun z => χ.rootNumber * completion χ⁻¹ z := funext (completion_one_sub hχ)
  have hc := analyticOrderAt_comp_of_deriv_ne_zero (f := completion χ)
    (g := fun z : ℂ => 1 - z) (z₀ := conj s) (by fun_prop) (by simp)
  have hm := analyticOrderAt_mul (f := fun _ : ℂ => χ.rootNumber)
    analyticAt_const (hFi.analyticAt (conj s))
  change analyticOrderAt (fun z => χ.rootNumber * completion χ⁻¹ z) (conj s) = _ at hm
  have hr : analyticOrderAt (fun _ : ℂ => χ.rootNumber) (conj s) = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (rootNumber_ne_zero hχ)
  have ho : analyticOrderAt (completion χ) (1 - conj s) =
      analyticOrderAt (completion χ) s := by
    rw [Function.comp_def, heq, hm, hr, zero_add] at hc
    exact hc.symm.trans hi
  refine ⟨?_, ho⟩
  rw [completion_reflect hχ, mul_eq_zero]
  simp [rootNumber_ne_zero hχ]

private theorem logDeriv_reflect {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    logDeriv (completion χ) (1 - conj s) = -conj (logDeriv (completion χ) s) := by
  have hF := differentiable_completion χ hne
  have heq : completion χ⁻¹ = conj ∘ completion χ ∘ conj := by
    funext z; simpa using completion_inv_conj χ (conj z)
  have hd : deriv (completion χ⁻¹) (conj s) = conj (deriv (completion χ) s) := by
    rw [heq, deriv_conj_conj]
    simp only [Function.comp_apply, conj_conj]
  have hl : logDeriv (completion χ⁻¹) (conj s) = conj (logDeriv (completion χ) s) := by
    simp only [logDeriv_apply, hd, completion_inv_conj, map_div₀]
  have he : (completion χ) ∘ (fun z : ℂ => 1 - z) =
      fun z => χ.rootNumber * completion χ⁻¹ z := funext (completion_one_sub hχ)
  have hh := logDeriv_comp (x := conj s) (f := completion χ)
    (g := fun z : ℂ => 1 - z) (hF _) (by fun_prop)
  rw [he, logDeriv_const_mul _ _ (rootNumber_ne_zero hχ), hl] at hh
  have hh' : conj (logDeriv (completion χ) s) =
      logDeriv (completion χ) (1 - conj s) * (-1) := by simpa using hh
  linear_combination hh'

/-- The positive vertical resolvent, summed with the actual zero multiplicities. -/
theorem completion_vertical_resolvent {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (σ t : ℝ) (hσ : 1 ≤ σ) :
    HasSum (fun ρ : {z : ℂ // completion χ z = 0} =>
      (analyticOrderNatAt (completion χ) ρ.1 : ℝ) * (σ - ρ.1.re) /
        ((σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2))
      (logDeriv (completion χ) ((σ : ℂ) + t * I)).re := by
  let F := completion χ
  let s : ℂ := σ + t * I
  let a : ℂ := 1 - conj s
  let k := fun ρ : {z : ℂ // F z = 0} =>
    (analyticOrderNatAt F ρ.1 : ℝ) * (σ - ρ.1.re) /
      ((σ - ρ.1.re) ^ 2 + (t - ρ.1.im) ^ 2)
  let e : {z : ℂ // F z = 0} ≃ {z : ℂ // F z = 0} :=
    { toFun := fun ρ => ⟨1 - conj ρ.1, (completion_reflect_order hχ hne ρ.1).1.mpr ρ.2⟩
      invFun := fun ρ => ⟨1 - conj ρ.1, (completion_reflect_order hχ hne ρ.1).1.mpr ρ.2⟩
      left_inv := by intro ρ; apply Subtype.ext; simp
      right_inv := by intro ρ; apply Subtype.ext; simp }
  have ho (ρ : {z : ℂ // F z = 0}) :
      analyticOrderNatAt F (e ρ).1 = analyticOrderNatAt F ρ.1 :=
    congrArg ENat.toNat (completion_reflect_order hχ hne ρ.1).2
  have hk (ρ : {z : ℂ // F z = 0}) : 0 ≤ k ρ := by
    have hr := (completion_zero_strip hχ ρ.2).2
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : F s ≠ 0 := completion_ne_zero_of_one_le_re χ (.inl hne) (by simpa [s] using hσ)
  have ha : F a ≠ 0 := completion_ne_zero_of_re_le_zero hχ (by simp [a, s]; linarith)
  have hh := Complex.hasSum_re
    (D5.S3.Analytic.Resolvent.EntireLogDerivDifference.entire_logDeriv_difference_hasSum
      (differentiable_completion χ hne) (by norm_num : (3 / 2 : ℝ) < 2)
      (fun z => (completion_power_growth hne z (.inr hχ)).le) ha hs)
  have hv : (logDeriv F s - logDeriv F a).re = 2 * (logDeriv F s).re := by
    rw [show logDeriv F a = -conj (logDeriv F s) from logDeriv_reflect hχ hne s]
    simp
    <;> ring
  have hp (ρ : {z : ℂ // F z = 0}) :
      ((analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)).re =
        k ρ + k (e ρ) := by
    dsimp only [k]
    rw [ho]
    simp [e, a, s, Complex.inv_re, Complex.normSq_apply]
    ring_nf
  change HasSum (fun ρ : {z : ℂ // F z = 0} =>
    ((analyticOrderNatAt F ρ.1 : ℂ) * ((s - ρ.1)⁻¹ - (a - ρ.1)⁻¹)).re)
    (logDeriv F s - logDeriv F a).re at hh
  have hh' : HasSum (fun ρ => k ρ + k (e ρ)) (2 * (logDeriv F s).re) := by
    simpa only [hp, hv] using hh
  have hks : Summable k := Summable.of_nonneg_of_le hk
    (fun ρ => le_add_of_nonneg_right (hk (e ρ))) hh'.summable
  have he : HasSum (fun ρ => k (e ρ)) (∑' ρ, k ρ) := e.hasSum_iff.mpr hks.hasSum
  have heq := (hks.hasSum.add he).unique hh'
  have hval : (∑' ρ, k ρ) = (logDeriv F s).re := by linarith
  exact hval ▸ hks.hasSum

/-- The Dirichlet logarithmic derivative on the line two has norm strictly below one. -/
theorem norm_logDeriv_LFunction_two {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖logDeriv χ.LFunction (2 + t * I)‖ ≤
      (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  let s : ℂ := 2 + t * I
  have hs : 1 < s.re := by simp [s]
  have he : logDeriv χ.LFunction s = -LSeries ((fun n : ℕ => χ n) *
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s := by
    rw [logDeriv_apply, χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs,
      χ.LSeries_twist_vonMangoldt_eq hs]
    ring
  have hterm (n : ℕ) : ‖LSeries.term ((fun n : ℕ => χ n) *
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s n‖ ≤ Real.log n / (n : ℝ) ^ 2 := by
    by_cases hn : n = 0
    · simp [hn]
    rw [LSeries.norm_term_eq, if_neg hn]
    simp only [Pi.mul_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hb : ‖χ n‖ * ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
      (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
        ArithmeticFunction.vonMangoldt_le_log
    simpa [s, Real.rpow_two] using
      div_le_div_of_nonneg_right hb (sq_nonneg (n : ℝ))
  rw [he, norm_neg]
  exact (norm_tsum_le_tsum_norm
    (χ.LSeriesSummable_twist_vonMangoldt hs).norm).trans
    ((χ.LSeriesSummable_twist_vonMangoldt hs).norm.tsum_le_tsum hterm
      DirichletCompletionGamma.logarithmic_series_bound.1)

/-- The completed logarithmic derivative separates conductor, Gamma and Dirichlet factors. -/
theorem completion_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) (hpole : s ≠ 1 ∨ χ ≠ 1) :
    logDeriv (completion χ) s = ((Real.log (q : ℝ) - Real.log Real.pi) / 2 : ℝ) +
      (1 / 2 : ℂ) * Complex.digamma ((s + (if χ.Even then 0 else 1)) / 2) +
      logDeriv χ.LFunction s := by
  classical
  let b : ℂ := (Real.log (q : ℝ) / 2 : ℝ)
  have hpos : 0 < s.re := hs
  have hdG : DifferentiableAt ℂ χ.gammaFactor s := by
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Zeta23.WeilEF.differentiableAt_Gammaℝ hpos
    · exact (Zeta23.WeilEF.differentiableAt_Gammaℝ
        (by simp only [add_re, one_re]; linarith)).comp s (by fun_prop)
  have hlocal : completion χ =ᶠ[𝓝 s] fun z => Complex.exp (b * z) *
      (χ.gammaFactor z * χ.LFunction z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hpos] with z hz
    exact congrArg (fun w => Complex.exp (b * z) * w) (completed_eq_mul χ hz)
  rw [(logDeriv_congr_nhds hlocal).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ => Complex.exp (b * z))
      (g := fun z => χ.gammaFactor z * χ.LFunction z) s
      (Complex.exp_ne_zero _) (mul_ne_zero (gammaFactor_ne_zero χ hpos) hL)
      (by fun_prop) (hdG.mul (χ.differentiableAt_LFunction s hpole)),
    logDeriv_fun_mul (f := χ.gammaFactor) (g := χ.LFunction) s
      (gammaFactor_ne_zero χ hpos) hL hdG
      (χ.differentiableAt_LFunction s hpole)]
  have hexp : logDeriv (fun z : ℂ => Complex.exp (b * z)) s = b := by
    have hd : HasDerivAt (fun z : ℂ => Complex.exp (b * z))
        (Complex.exp (b * s) * b) s := by
      simpa using ((hasDerivAt_id s).const_mul b).cexp
    rw [logDeriv_apply, hd.deriv]
    exact mul_div_cancel_left₀ b (Complex.exp_ne_zero _)
  rw [hexp]
  unfold DirichletCharacter.gammaFactor
  split_ifs with heven
  · rw [Zeta23.WeilEF.logDeriv_Gammaℝ hpos]
    simp only [add_zero]
    dsimp [b]
    push_cast
    ring
  · have hc := logDeriv_comp (x := s) (f := Complex.Gammaℝ)
      (g := fun z : ℂ => z + 1)
      (Zeta23.WeilEF.differentiableAt_Gammaℝ (by simp only [add_re, one_re]; linarith))
      (by fun_prop)
    simp only [Function.comp_def, deriv_add_const, deriv_id'', mul_one] at hc
    rw [hc, Zeta23.WeilEF.logDeriv_Gammaℝ (by simp only [add_re, one_re]; linarith)]
    dsimp [b]
    push_cast
    ring

/-- Every character has the upper bound; primitive nonprincipal characters have positivity. -/
theorem completion_vertical_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (logDeriv (completion χ) (2 + t * I)).re ≤
        (Real.log (q : ℝ) - Real.log Real.pi + Real.log (|t| + 3) - Real.log 2 + 1 / 2 -
          (1 / ((2 + t * I) + (if χ.Even then 0 else 1))).re) / 2 +
          (∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) ∧
      (χ.IsPrimitive → χ ≠ 1 → 0 ≤ (logDeriv (completion χ) (2 + t * I)).re) := by
  constructor
  · let z : ℂ := ((2 + t * I) + (if χ.Even then 0 else 1)) / 2
    have hz : 1 ≤ z.re ∧ z.re ≤ 3 / 2 := by
      dsimp [z]; split_ifs <;> norm_num
    have him : 2 * |z.im| = |t| := by
      dsimp [z]; split_ifs <;> simp [abs_div] <;> ring
    have hp := DirichletCompletionGamma.digamma_re_lt_log_height hz.1 hz.2
    have hinv : 2 * z = (2 + t * I) + (if χ.Even then 0 else 1) := by
      dsimp [z]; ring
    rw [him, hinv] at hp
    have hL := (Complex.re_le_norm _).trans (norm_logDeriv_LFunction_two χ t)
    have he := congrArg Complex.re
      (completion_logDeriv χ (s := 2 + t * I) (by simp)
        (χ.LFunction_ne_zero_of_one_le_re (.inr (by
          intro h; have := congrArg Complex.re h; norm_num at this)) (by simp))
        (.inl (by intro h; have := congrArg Complex.re h; norm_num at this)))
    change _ = _ + ((1 / 2 : ℂ) * Complex.digamma z).re + _ at he
    norm_num [Complex.add_re, Complex.mul_re, Complex.log_re] at he
    linarith
  · intro hχ hne
    have hs := completion_vertical_resolvent hχ hne 2 t (by norm_num)
    norm_num at hs
    rw [← hs.tsum_eq]
    apply tsum_nonneg
    intro ρ
    have hr := (completion_zero_strip hχ ρ.2).2
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))

end D5.S3.CharacterSums.DirichletCompletion
