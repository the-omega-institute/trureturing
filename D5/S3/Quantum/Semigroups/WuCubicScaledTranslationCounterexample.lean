import D5.S3.Quantum.Semigroups.WuCubicHotInnerMixedTransfer
import Mathlib.Analysis.Matrix.Order

/-! An exact counterexample to scaled-translation monotonicity in Wu v1,
Remark 3.15 (3.54), for the ordinary-trace two-mode cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder Kronecker

namespace D5.S3.Quantum.Semigroups.WuCubicScaledTranslationCounterexample

open WuCubicOperatorBridge (Mat D)
open WuCubicOperatorNormalization (operatorDeficit)
open WuCubicHotInnerPartialTrace (Local lift)
open WuCubicHotInnerMixedTransfer (physical operatorDeficit_physical)
open WuCubicHotInnerMixed (v w lower upper cubicLog spectral diagonalLow diagonalHigh
  mass charges energy deficit)
open WuRepeatedMiddleCubic (alpha)
open private gibbsLow gibbsHigh gibbsOccupation from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic
open private log_lower log_upper from D5.S3.Quantum.Semigroups.WuCubicDirectedOccupationCap
open private gaugeConj gauge_entries operatorDeficit_gauge_smul from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerMixedTransfer

private abbrev r : ℝ := 1049 / 1000
private abbrev eps : ℝ := 1 / 10000
private abbrev a : ℝ := gibbsLow r
private abbrev b : ℝ := gibbsHigh r
private abbrev u : ℝ := 1 / r
private abbrev κ : ℝ := 3 * (r ^ 2 - 1) / (4 * (r ^ 2 + r + 1))

private def t (s : ℝ) : ℝ := (s - r / s + eps * (b + r * a)) / (r - 1)

private def point (s : ℝ) : Local := physical r (1 / t s) (eps / t s)

private theorem point_pos {s : ℝ} (hs : s = 12 ∨ s = 24) : (point s).PosDef := by
  unfold point physical
  apply D5.S3.Quantum.Matrix.SpectralPower.posDef_two
  all_goals rcases hs with rfl | rfl <;> norm_num [t, gibbsLow, gibbsHigh]

private def low (s : ℝ) : ℝ := (t s + eps * b - r / s) / (r * t s)
private def high (s : ℝ) : ℝ := (r * (t s - eps * a) + r / s) / (r * t s)
private abbrev z (s : ℝ) : ℝ := (1 / t s) ^ 2
private abbrev y (s : ℝ) : ℝ := eps / t s
private abbrev total (s : ℝ) : ℝ := mass u a b (z s) (y s)

private theorem levels {s : ℝ} (hs : s = 12 ∨ s = 24) :
    lower u (v u b (y s)) (w a (y s)) (z s) = low s ∧
    upper u (v u b (y s)) (w a (y s)) (z s) = high s := by
  have hsq : (w a (y s) - v u b (y s)) ^ 2 + 4 * u * z s =
      ((s + r / s) / (r * t s)) ^ 2 := by
    rcases hs with rfl | rfl <;> norm_num [t, v, w, z, y, gibbsLow, gibbsHigh]
  have hnonneg : 0 ≤ (s + r / s) / (r * t s) := by
    rcases hs with rfl | rfl <;> norm_num [t, gibbsLow, gibbsHigh]
  simp only [lower, upper, hsq, Real.sqrt_sq hnonneg]
  rcases hs with rfl | rfl <;> norm_num [low, high, t, v, w, y, gibbsLow, gibbsHigh]

private def logCoeff (s : ℝ) : ℝ :=
  t s ^ 4 * b * ((9 / 8) * energy u a b (z s) (y s) -
    3 * κ * (high s ^ 3 - diagonalHigh u a b (z s) (y s)))

private def lowCoeff (s : ℝ) : ℝ := -(t s ^ 4 * b * 3 * κ * low s ^ 3)
private def highCoeff (s : ℝ) : ℝ := -(t s ^ 4 * b * 3 * κ * high s ^ 3)
private def massCoeff (s : ℝ) : ℝ := t s ^ 4 * b * κ * total s

private def scaled (s : ℝ) : ℝ := t s ^ 4 * operatorDeficit r (lift (point s))

private theorem log_r_pos : 0 < Real.log r := Real.log_pos (by norm_num)

private theorem scaled_log_form {s : ℝ} (hs : s = 12 ∨ s = 24) :
    Real.log r * scaled s =
      logCoeff s * Real.log r + lowCoeff s * Real.log (r * low s) +
        highCoeff s * Real.log (high s) + massCoeff s * Real.log (b * total s) := by
  have hlevels := levels hs
  have hl : low s ≠ 0 := by
    rcases hs with rfl | rfl <;> norm_num [low, t, gibbsLow, gibbsHigh]
  have htotal : total s ≠ 0 := by
    rcases hs with rfl | rfl <;>
      norm_num [total, z, y, mass, diagonalLow, diagonalHigh, w, v, t, gibbsLow, gibbsHigh]
  have hmass : total s = low s ^ 3 + high s ^ 3 := by
    rcases hs with rfl | rfl <;>
      norm_num [total, z, y, mass, diagonalLow, diagonalHigh, low, high, w, v, t,
        gibbsLow, gibbsHigh]
  have hb : Real.log b = 3 * Real.log r + Real.log a := by
    change Real.log (r ^ 3 * a) = _
    rw [Real.log_mul (by norm_num : r ^ 3 ≠ 0)
      (by norm_num [gibbsLow] : a ≠ 0), Real.log_pow]
    norm_num
  have hlogprod : Real.log (b * total s) =
      3 * Real.log r + Real.log a + Real.log (total s) := by
    rw [Real.log_mul (by norm_num [gibbsHigh, gibbsLow] : b ≠ 0) htotal, hb]
  have hsplit : Real.log (r * low s) = Real.log r + Real.log (low s) :=
    Real.log_mul (by norm_num) hl
  have hα : alpha r = κ / Real.log r := by
    unfold alpha
    rw [ite_eq_right (by norm_num : r ≠ 1), div_div]
  have hcharge : diagonalLow u a b (z s) (y s) =
      total s - diagonalHigh u a b (z s) (y s) := by
    simp only [total, mass]
    ring
  unfold scaled point
  rw [operatorDeficit_physical (by norm_num : 1 ≤ r) _ _ (point_pos hs)]
  unfold deficit spectral cubicLog charges logCoeff lowCoeff highCoeff massCoeff
  simp only [total] at hmass hlogprod hcharge ⊢
  rw [hlevels.1, hlevels.2, hα, hsplit, hlogprod, hb, hcharge]
  simp only [hmass]
  field_simp [log_r_pos.ne']
  ring_nf

private def logCoord (x : ℝ) : ℝ := (x - 1) / (x + 1)

private theorem log_interval {x lo hi : ℝ} (hx : 0 < x)
    (hlo : lo ≤ 2 * ((∑ j ∈ Finset.range 5, logCoord x ^ (2 * j + 1) / (2 * j + 1)) -
      |logCoord x| ^ 11 / (1 - logCoord x ^ 2)))
    (hhi : 2 * ((∑ j ∈ Finset.range 8, logCoord x ^ (2 * j + 1) / (2 * j + 1)) +
      |logCoord x| ^ 17 / (1 - logCoord x ^ 2)) ≤ hi) :
    lo ≤ Real.log x ∧ Real.log x ≤ hi := by
  have hp : 0 < x + 1 := by positivity
  have hc : |logCoord x| < 1 := by
    rw [abs_lt]
    unfold logCoord
    constructor
    · exact (lt_div_iff₀ hp).2 (by linarith)
    · exact (div_lt_iff₀ hp).2 (by linarith)
  have hr : (1 + logCoord x) / (1 - logCoord x) = x := by
    have hd : 1 - logCoord x ≠ 0 := by linarith [(abs_lt.mp hc).2]
    apply (div_eq_iff hd).2
    unfold logCoord
    field_simp [hp.ne']
    ring
  exact ⟨log_lower _ _ _ hc hr hlo, log_upper _ _ _ hc hr hhi⟩

-- The common denominator keeps the interval endpoints small for the linear comparison.
private abbrev den : ℝ := 10 ^ 18
private abbrev cutoff : ℝ := 233 / 125

private theorem log_r_interval :
    47837329414160117 / den ≤ Real.log r ∧ Real.log r ≤ 47837329414160124 / den := by
  apply log_interval <;> norm_num [logCoord, Finset.sum_range_succ]

private theorem earlier_scaled : cutoff < scaled 12 := by
  have hl : -359411860279121 / den ≤ Real.log (r * low 12) ∧
      Real.log (r * low 12) ≤ -359411860279120 / den := by
    apply log_interval <;> norm_num [logCoord, low, t, gibbsHigh, gibbsLow, Finset.sum_range_succ]
  have hh : 342522255845171 / den ≤ Real.log (high 12) ∧
      Real.log (high 12) ≤ 342522255845172 / den := by
    apply log_interval <;> norm_num [logCoord, high, t, gibbsHigh, gibbsLow, Finset.sum_range_succ]
  have hm : 50639588236667 / den ≤ Real.log (b * total 12) ∧
      Real.log (b * total 12) ≤ 50639588236668 / den := by
    apply log_interval <;>
      norm_num [logCoord, total, z, y, mass, diagonalLow, diagonalHigh, v, w, t, gibbsHigh,
        gibbsLow, Finset.sum_range_succ]
  apply (mul_lt_mul_iff_of_pos_left log_r_pos).mp
  rw [scaled_log_form (Or.inl rfl)]
  have h₀ := log_r_interval.1
  have h₁ := hl.2
  have h₂ := hh.2
  have h₃ := hm.1
  norm_num [logCoeff, lowCoeff, highCoeff, massCoeff, total, energy, z, y, mass, diagonalLow,
    diagonalHigh, v, w, low, high, t, gibbsHigh, gibbsLow] at h₀ h₁ h₂ h₃ ⊢
  linarith only [h₀, h₁, h₂, h₃]

private theorem later_scaled : scaled 24 < cutoff := by
  have hl : -89294671947834 / den ≤ Real.log (r * low 24) ∧
      Real.log (r * low 24) ≤ -89294671947833 / den := by
    apply log_interval <;> norm_num [logCoord, low, t, gibbsHigh, gibbsLow, Finset.sum_range_succ]
  have hh : 85125723496396 / den ≤ Real.log (high 24) ∧
      Real.log (high 24) ≤ 85125723496397 / den := by
    apply log_interval <;> norm_num [logCoord, high, t, gibbsHigh, gibbsLow, Finset.sum_range_succ]
  have hm : 12522034880748 / den ≤ Real.log (b * total 24) ∧
      Real.log (b * total 24) ≤ 12522034880749 / den := by
    apply log_interval <;>
      norm_num [logCoord, total, z, y, mass, diagonalLow, diagonalHigh, v, w, t, gibbsHigh,
        gibbsLow, Finset.sum_range_succ]
  apply (mul_lt_mul_iff_of_pos_left log_r_pos).mp
  rw [scaled_log_form (Or.inr rfl)]
  have h₀ := log_r_interval.2
  have h₁ := hl.1
  have h₂ := hh.1
  have h₃ := hm.2
  norm_num [logCoeff, lowCoeff, highCoeff, massCoeff, total, energy, z, y, mass, diagonalLow,
    diagonalHigh, v, w, low, high, t, gibbsHigh, gibbsLow] at h₀ h₁ h₂ h₃ ⊢
  linarith only [h₀, h₁, h₂, h₃]

private def m : ℝ := (Real.sqrt (4 + eps ^ 2) - eps * (b - a)) / 2

private theorem m_bounds : 0 < m ∧ m < 2 := by
  have hlo : 2 ≤ Real.sqrt (4 + eps ^ 2) :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hhi : Real.sqrt (4 + eps ^ 2) < 3 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  norm_num [m, gibbsHigh, gibbsLow] at hlo hhi ⊢
  constructor <;> linarith only [hlo, hhi]

private theorem t_gt_two {s : ℝ} (hs : s = 12 ∨ s = 24) : 2 < t s := by
  rcases hs with rfl | rfl <;> norm_num [t, gibbsHigh, gibbsLow]

private def perturbation : Local := !![(eps * b : ℝ), Complex.I; -Complex.I, (-eps * a : ℝ)]

private def direction : Mat := m⁻¹ • lift perturbation

private theorem translate_as_lift (x : ℝ) :
    (x / m) • (1 : Mat) + direction = m⁻¹ • lift (x • (1 : Local) + perturbation) := by
  simp only [direction, lift, Matrix.kronecker_add, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, smul_add, smul_smul, div_eq_mul_inv, mul_comm]

private theorem phase_unit : Complex.I * star Complex.I = 1 := by
  simp [Complex.conj_I, Complex.I_mul_I]

private theorem translate_at_point {s : ℝ} (hs : s = 12 ∨ s = 24) :
    (t s / m) • (1 : Mat) + direction = lift ((t s / m) • gaugeConj Complex.I (point s)) := by
  rw [translate_as_lift, gauge_entries phase_unit]
  have hpoint : t s • (1 : Local) + perturbation =
      t s • !![point s 0 0, Complex.I * point s 0 1;
        point s 1 0 * star Complex.I, point s 1 1] := by
    have ht : (t s : ℂ) ≠ 0 := by exact_mod_cast (lt_trans zero_lt_two (t_gt_two hs)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [point, physical, perturbation, Matrix.smul_apply, Complex.real_smul,
        Complex.conj_I] <;>
      field_simp [ht]
    rw [sub_eq_add_neg]
  rw [hpoint]
  simp only [lift, Matrix.kronecker_smul, smul_smul, div_eq_mul_inv, mul_comm]

private theorem translated_scaled {s : ℝ} (hs : s = 12 ∨ s = 24) :
    (t s / m) * operatorDeficit r ((t s / m) • (1 : Mat) + direction) =
      scaled s / m ^ 4 := by
  have ht : 0 < t s / m := div_pos (lt_trans zero_lt_two (t_gt_two hs)) m_bounds.1
  rw [translate_at_point hs,
    operatorDeficit_gauge_smul (by norm_num : 1 ≤ r) _ (point_pos hs) phase_unit ht, scaled]
  ring

private theorem centered : (D r * direction).trace = 0 := by
  simp [D, direction, lift, perturbation, Matrix.trace, Matrix.diagonal_mul,
    Matrix.smul_apply, gibbsOccupation, Fintype.sum_prod_type,
    Fin.sum_univ_two, Complex.real_smul]
  ring

private def edge : Local := m • (1 : Local) + perturbation

private theorem edge_entries : edge =
    !![((m + eps * b : ℝ) : ℂ), Complex.I; -Complex.I, ((m - eps * a : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [edge, perturbation, Matrix.smul_apply, Complex.real_smul, sub_eq_add_neg]

private theorem edge_product : (m + eps * b) * (m - eps * a) = 1 := by
  have hab : a + b = 1 := by norm_num [gibbsHigh, gibbsLow]
  have hs := Real.sq_sqrt (show 0 ≤ 4 + eps ^ 2 by positivity)
  have h₁ : m + eps * b = (Real.sqrt (4 + eps ^ 2) + eps) / 2 := by
    unfold m
    linear_combination eps / 2 * hab
  have h₂ : m - eps * a = (Real.sqrt (4 + eps ^ 2) - eps) / 2 := by
    unfold m
    linear_combination -eps / 2 * hab
  rw [h₁, h₂]
  linear_combination hs / 4

private theorem edge_posSemidef : edge.PosSemidef := by
  let p := m + eps * b
  have hp : 0 < p := add_pos m_bounds.1 (by norm_num [gibbsHigh, gibbsLow])
  have hq : (p : ℂ) * ((m - eps * a : ℝ) : ℂ) = 1 := by exact_mod_cast edge_product
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (p : ℂ)⁻¹ = ((m - eps * a : ℝ) : ℂ) := by
    calc
      (p : ℂ)⁻¹ = (p : ℂ)⁻¹ * ((p : ℂ) * ((m - eps * a : ℝ) : ℂ)) := by rw [hq, mul_one]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hp', one_mul]
  let f : Fin 2 → ℂ := ![(p : ℂ), -Complex.I]
  have he : p⁻¹ • vecMulVec f (star f) = edge := by
    rw [edge_entries]
    ext i j
    fin_cases i <;> fin_cases j
    · change p⁻¹ • ((p : ℂ) * star (p : ℂ)) = (p : ℂ)
      simp [Complex.real_smul, hp']
    · change p⁻¹ • ((p : ℂ) * star (-Complex.I)) = Complex.I
      simp [Complex.real_smul, hp']
    · change p⁻¹ • (-Complex.I * star (p : ℂ)) = -Complex.I
      rw [Complex.real_smul, Complex.ofReal_inv]
      simp only [Complex.star_def, Complex.conj_ofReal]
      calc
        _ = ((p : ℂ)⁻¹ * (p : ℂ)) * (-Complex.I) := by ring
        _ = _ := by rw [inv_mul_cancel₀ hp', one_mul]
    · change p⁻¹ • (-Complex.I * star (-Complex.I)) = ((m - eps * a : ℝ) : ℂ)
      simpa [Complex.real_smul, Complex.I_mul_I] using hq'
  rw [← he]
  exact (Matrix.posSemidef_vecMulVec_self_star f).smul (inv_nonneg.mpr hp.le)

private theorem edge_singular : edge.det = 0 := by
  have h : ((m + eps * b : ℝ) : ℂ) * ((m - eps * a : ℝ) : ℂ) = 1 := by
    exact_mod_cast edge_product
  rw [edge_entries, Matrix.det_fin_two]
  change ((m + eps * b : ℝ) : ℂ) * ((m - eps * a : ℝ) : ℂ) - Complex.I * (-Complex.I) = 0
  rw [h]
  simp [Complex.I_mul_I]

private theorem direction_edge : (1 : Mat) + direction = m⁻¹ • lift edge := by
  simpa [div_self m_bounds.1.ne', edge] using translate_as_lift m

private theorem direction_edge_posSemidef : ((1 : Mat) + direction).PosSemidef := by
  rw [direction_edge]
  exact (Matrix.PosSemidef.one.kronecker edge_posSemidef).smul (inv_pos.mpr m_bounds.1).le

private theorem direction_edge_singular : ((1 : Mat) + direction).det = 0 := by
  rw [direction_edge]
  change (((m⁻¹ : ℝ) : ℂ) • lift edge).det = 0
  simp [lift, Matrix.det_kronecker, edge_singular]

private theorem translated_pos {s : ℝ} (hs : s = 12 ∨ s = 24) :
    ((t s / m) • (1 : Mat) + direction).PosDef := by
  have ht : 1 < t s / m := (lt_div_iff₀ m_bounds.1).2 (by
    simpa using m_bounds.2.trans (t_gt_two hs))
  have hdecomp : (t s / m) • (1 : Mat) + direction =
      (t s / m - 1) • (1 : Mat) + (1 + direction) := by
    symm
    calc
      (t s / m - 1) • (1 : Mat) + (1 + direction) =
          ((t s / m - 1) + 1) • (1 : Mat) + direction := by
        rw [add_smul, one_smul, add_assoc]
      _ = _ := by rw [sub_add_cancel]
  rw [hdecomp]
  exact (Matrix.PosDef.one.smul (sub_pos.mpr ht)).add_posSemidef direction_edge_posSemidef

/-- For the two-mode cubic deficit at `r = 1049/1000`, a centered Hermitian
direction with least eigenvalue `-1` has strictly decreasing scaled deficit
between two of its positive definite scalar translates. The positive
semidefinite singular shift by the identity certifies the least eigenvalue. -/
theorem counterexample :
    ∃ (A : Mat) (t₁ t₂ : ℝ), A.IsHermitian ∧ (D r * A).trace = 0 ∧
      ((1 : Mat) + A).PosSemidef ∧ ((1 : Mat) + A).det = 0 ∧
      1 < t₁ ∧ t₁ < t₂ ∧ (t₁ • (1 : Mat) + A).PosDef ∧ (t₂ • (1 : Mat) + A).PosDef ∧
      t₂ * operatorDeficit r (t₂ • (1 : Mat) + A) <
        t₁ * operatorDeficit r (t₁ • (1 : Mat) + A) := by
  refine ⟨direction, t 12 / m, t 24 / m, ?_, centered, direction_edge_posSemidef,
    direction_edge_singular, ?_, ?_, translated_pos (Or.inl rfl), translated_pos (Or.inr rfl), ?_⟩
  · simpa using direction_edge_posSemidef.isHermitian.sub
      (Matrix.isHermitian_one (n := Fin 2 × Fin 2) (α := ℂ))
  · exact (lt_div_iff₀ m_bounds.1).2 (by simpa using m_bounds.2.trans (t_gt_two (Or.inl rfl)))
  · exact (div_lt_div_iff_of_pos_right m_bounds.1).2 (by norm_num [t, gibbsHigh, gibbsLow])
  · rw [translated_scaled (Or.inl rfl), translated_scaled (Or.inr rfl)]
    exact (div_lt_div_iff_of_pos_right (pow_pos m_bounds.1 4)).2
      (later_scaled.trans earlier_scaled)

end D5.S3.Quantum.Semigroups.WuCubicScaledTranslationCounterexample
