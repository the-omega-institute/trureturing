import D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
import Mathlib.Tactic.FinCases
import OmegaBuild.Commands

/-! Scalar thermal degree and absolute Bohr charge coefficients for Wu's
two-mode equal-cap cubic problem. The matrix Hessian identification is a
separate mathematical obligation. -/

compile_only_with_mathlib

set_option autoImplicit false

namespace WuCubicThermalBohrGap

open D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
  (coth one_le_self_mul_coth)

noncomputable section

/-- The thermal response in the scalar quadratic symbol, including its
tracial endpoint. -/
def g (v : ℝ) : ℝ :=
  if v = 0 then 1 / 2 else (v / 18) * (coth (v / 3) + coth (v / 6))

theorem half_le_g {v : ℝ} (hv : 0 ≤ v) : 1 / 2 ≤ g v := by
  rcases hv.eq_or_lt with rfl | hv
  · norm_num [g]
  rw [g, ite_eq_right (ne_of_gt hv)]
  have ha := one_le_self_mul_coth (x := v / 3) (by positivity)
  have hb := one_le_self_mul_coth (x := v / 6) (by positivity)
  linarith only [ha, hb]

private theorem g_pos {v : ℝ} (hv : 0 ≤ v) : 0 < g v :=
  lt_of_lt_of_le (by norm_num) (half_le_g hv)

private theorem coth_double {x : ℝ} (hx : 0 < x) :
    coth (2 * x) = (coth x + Real.tanh x) / 2 := by
  unfold coth
  rw [Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.sinh_pos_iff.mpr hx), ne_of_gt (Real.cosh_pos x)]

private theorem coth_sum_mul_tanh {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (coth a + coth b) * (Real.tanh a * Real.tanh b) =
      Real.tanh a + Real.tanh b := by
  unfold coth
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp [ne_of_gt (Real.sinh_pos_iff.mpr ha), ne_of_gt (Real.sinh_pos_iff.mpr hb),
    ne_of_gt (Real.cosh_pos a), ne_of_gt (Real.cosh_pos b)]
  ring

/-- The double-charge response is exactly one plus the product of two
hyperbolic tangents at positive physical temperature parameter. -/
theorem g_double_ratio {beta : ℝ} (hbeta : 0 < beta) :
    g (2 * beta) / g beta = 1 + Real.tanh (beta / 3) * Real.tanh (beta / 6) := by
  have ha : 0 < beta / 3 := by positivity
  have hb : 0 < beta / 6 := by positivity
  apply (div_eq_iff (ne_of_gt (g_pos hbeta.le))).2
  simp only [g, ite_eq_right (ne_of_gt hbeta),
    ite_eq_right (ne_of_gt (show 0 < 2 * beta by positivity))]
  rw [show 2 * beta / 3 = 2 * (beta / 3) by ring,
    show 2 * beta / 6 = 2 * (beta / 6) by ring, coth_double ha, coth_double hb]
  have h := coth_sum_mul_tanh ha hb
  calc
    _ = (beta / 18) * ((coth (beta / 3) + coth (beta / 6)) +
        (Real.tanh (beta / 3) + Real.tanh (beta / 6))) := by ring
    _ = _ := by rw [← h]; ring

private theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.cosh_pos x).le

/-- The three possible absolute Bohr charges are represented by `Fin 3`. -/
def chargeRatio (beta : ℝ) (q : Fin 3) : ℝ :=
  g ((q.val : ℝ) * beta) / g beta

/-- The scalar symbol at thermal degree `d` and absolute Bohr charge `q`. -/
def coefficient (beta : ℝ) (d : ℕ) (q : Fin 3) : ℝ :=
  (9 / 4) * Real.cosh ((q.val : ℝ) * beta / 6) * ((d : ℝ) - chargeRatio beta q)

private theorem chargeRatio_zero_le_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    chargeRatio beta 0 ≤ 1 := by
  have hq : ((0 : Fin 3).val : ℝ) = 0 := by norm_num
  rw [chargeRatio, hq, zero_mul, div_le_iff₀ (g_pos hbeta), one_mul]
  simpa [g] using half_le_g hbeta

@[simp] theorem chargeRatio_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    chargeRatio beta 1 = 1 := by
  have hq : ((1 : Fin 3).val : ℝ) = 1 := by norm_num
  rw [chargeRatio, hq, one_mul, div_self (ne_of_gt (g_pos hbeta))]

theorem chargeRatio_two {beta : ℝ} (hbeta : 0 ≤ beta) :
    chargeRatio beta 2 = 1 + Real.tanh (beta / 3) * Real.tanh (beta / 6) := by
  change g (2 * beta) / g beta = _
  rcases hbeta.eq_or_lt with rfl | hbeta
  · norm_num [g, Real.tanh_zero]
  exact g_double_ratio hbeta

/-- Every charge response is strictly below degree two at every finite
nonnegative temperature parameter. -/
theorem chargeRatio_lt_two {beta : ℝ} (hbeta : 0 ≤ beta) (q : Fin 3) :
    chargeRatio beta q < 2 := by
  have hq : q = 0 ∨ q = 1 ∨ q = 2 := by fin_cases q <;> decide
  rcases hq with rfl | rfl | rfl
  · exact lt_of_le_of_lt (chargeRatio_zero_le_one hbeta) (by norm_num)
  · rw [chargeRatio_one hbeta]
    norm_num
  · rw [chargeRatio_two hbeta]
    have h := mul_le_mul_of_nonneg_right (Real.tanh_lt_one (beta / 3)).le
      (tanh_nonneg (x := beta / 6) (by positivity))
    linarith [Real.tanh_lt_one (beta / 6)]

/-- Degree two at absolute charge two attains the same coefficient at
every nonnegative temperature parameter, including the tracial endpoint. -/
theorem coefficient_two_two {beta : ℝ} (hbeta : 0 ≤ beta) :
    coefficient beta 2 2 = 9 / 4 := by
  have hcore : Real.cosh (beta / 3) *
      (1 - Real.tanh (beta / 3) * Real.tanh (beta / 6)) = 1 := by
    calc
      _ = Real.cosh (beta / 3 - beta / 6) / Real.cosh (beta / 6) := by
        rw [Real.cosh_sub, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
        field_simp [ne_of_gt (Real.cosh_pos (beta / 3)),
          ne_of_gt (Real.cosh_pos (beta / 6))]
      _ = 1 := by
        rw [show beta / 3 - beta / 6 = beta / 6 by ring,
          div_self (ne_of_gt (Real.cosh_pos (beta / 6)))]
  have hq : ((2 : Fin 3).val : ℝ) = 2 := by norm_num
  rw [coefficient, hq, show 2 * beta / 6 = beta / 3 by ring, chargeRatio_two hbeta]
  push_cast
  calc
    _ = (9 / 4) * (Real.cosh (beta / 3) *
        (1 - Real.tanh (beta / 3) * Real.tanh (beta / 6))) := by ring
    _ = _ := by rw [hcore, mul_one]

/-- The sharp uniform lower bound for all degrees at least two and all
three absolute Bohr charges. -/
theorem coefficient_lower_bound {beta : ℝ} (hbeta : 0 ≤ beta) {d : ℕ} (hd : 2 ≤ d)
    (q : Fin 3) : 9 / 4 ≤ coefficient beta d q := by
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmono : coefficient beta 2 q ≤ coefficient beta d q := by
    unfold coefficient
    push_cast
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hd' _) (by positivity)
  apply le_trans _ hmono
  have hunit (r : Fin 3) (hr : chargeRatio beta r ≤ 1) :
      9 / 4 ≤ coefficient beta 2 r := by
    have hgap : (1 : ℝ) ≤ 2 - chargeRatio beta r := by linarith
    unfold coefficient
    push_cast
    calc
      (9 / 4 : ℝ) = (9 / 4) * 1 * 1 := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.one_le_cosh _) (by norm_num))
        hgap zero_le_one (by positivity)
  have hq : q = 0 ∨ q = 1 ∨ q = 2 := by fin_cases q <;> decide
  rcases hq with rfl | rfl | rfl
  · exact hunit 0 (chargeRatio_zero_le_one hbeta)
  · exact hunit 1 (chargeRatio_one hbeta).le
  · exact (coefficient_two_two hbeta).ge

/-- Strict positivity holds for every degree at least two, in particular
for degree two at each of the three charges. -/
theorem coefficient_pos {beta : ℝ} (hbeta : 0 ≤ beta) {d : ℕ} (hd : 2 ≤ d)
    (q : Fin 3) : 0 < coefficient beta d q := by
  exact lt_of_lt_of_le (by norm_num) (coefficient_lower_bound hbeta hd q)

/-- At degree one the allowed absolute charge is one and the symbol vanishes. -/
theorem coefficient_degree_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    coefficient beta 1 1 = 0 := by
  simp [coefficient, chargeRatio_one hbeta]

/-- On the admissible nonconstant degree-charge labels, the only zeros
are the degree-one labels. -/
theorem coefficient_eq_zero_iff {beta : ℝ} (hbeta : 0 ≤ beta) {d : ℕ} {q : Fin 3}
    (hadm : (d = 1 ∧ q = 1) ∨ 2 ≤ d) :
    coefficient beta d q = 0 ↔ d = 1 := by
  rcases hadm with ⟨rfl, rfl⟩ | hd
  · simp [coefficient_degree_one hbeta]
  · have hp := coefficient_pos hbeta hd q
    have hne : d ≠ 1 := by omega
    simp [ne_of_gt hp, hne]

private theorem coth_anti_on_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    coth y ≤ coth x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  unfold coth
  apply (div_le_div_iff₀ (Real.sinh_pos_iff.mpr hy)
    (Real.sinh_pos_iff.mpr hx)).2
  have hdiff : 0 ≤ Real.sinh (y - x) :=
    Real.sinh_nonneg_iff.mpr (sub_nonneg.mpr hxy)
  rw [Real.sinh_sub] at hdiff
  linarith

private theorem g_div_arg_anti_on_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    g y / y ≤ g x / x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hthree : x / 3 ≤ y / 3 := by linarith
  have hsix : x / 6 ≤ y / 6 := by linarith
  have hthree' : 0 < x / 3 := by positivity
  have hsix' : 0 < x / 6 := by positivity
  have hsum : coth (y / 3) + coth (y / 6) ≤ coth (x / 3) + coth (x / 6) :=
    add_le_add (coth_anti_on_pos hthree' hthree) (coth_anti_on_pos hsix' hsix)
  rw [g, ite_eq_right hy.ne', g, ite_eq_right hx.ne']
  field_simp
  exact hsum

/-- The scalar thermal symbol is bounded below by `(9 / 4) * (q / 2)`
for every real charge `q ≥ 2` and degree `d ≥ q`. -/
theorem coefficient_real_q_lower_bound {beta q d : ℝ} (hbeta : 0 ≤ beta)
    (hq : 2 ≤ q) (hd : q ≤ d) :
    (9 / 4) * Real.cosh (q * beta / 6) * (d - g (q * beta) / g beta) ≥
      (9 / 4) * (q / 2) := by
  rcases hbeta.eq_or_lt with rfl | hbeta
  · norm_num [g]
    linarith
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqbeta : 0 < q * beta := mul_pos hqpos hbeta
  have h2beta : 0 < 2 * beta := by positivity
  have hmono : g (q * beta) / (q * beta) ≤ g (2 * beta) / (2 * beta) := by
    apply g_div_arg_anti_on_pos h2beta
    nlinarith
  have hscaled : g (q * beta) ≤ (q / 2) * g (2 * beta) := by
    calc
      g (q * beta) = (q * beta) * (g (q * beta) / (q * beta)) := by
        field_simp
      _ ≤ (q * beta) * (g (2 * beta) / (2 * beta)) :=
        mul_le_mul_of_nonneg_left hmono hqbeta.le
      _ = (q / 2) * g (2 * beta) := by
        field_simp
  have hratio : g (q * beta) / g beta ≤
      (q / 2) * (g (2 * beta) / g beta) := by
    calc
      g (q * beta) / g beta ≤ ((q / 2) * g (2 * beta)) / g beta :=
        div_le_div_of_nonneg_right hscaled (g_pos hbeta.le).le
      _ = (q / 2) * (g (2 * beta) / g beta) := by ring
  have hgap : (q / 2) * (2 - g (2 * beta) / g beta) ≤
      d - g (q * beta) / g beta := by
    nlinarith
  have hcore : Real.cosh (2 * beta / 6) *
      (2 - g (2 * beta) / g beta) = 1 := by
    have htwo := coefficient_two_two (beta := beta) hbeta.le
    change (9 / 4) * Real.cosh (2 * beta / 6) *
      (2 - g (2 * beta) / g beta) = 9 / 4 at htwo
    nlinarith only [htwo]
  have hfactor : 0 ≤ 2 - g (2 * beta) / g beta := by
    exact sub_nonneg.mpr (chargeRatio_lt_two hbeta.le 2).le
  have hcosh : Real.cosh (2 * beta / 6) ≤ Real.cosh (q * beta / 6) := by
    apply (Real.cosh_le_cosh).2
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    nlinarith
  have hcosh_factor : 1 ≤ Real.cosh (q * beta / 6) *
      (2 - g (2 * beta) / g beta) := by
    calc
      1 = Real.cosh (2 * beta / 6) * (2 - g (2 * beta) / g beta) := hcore.symm
      _ ≤ Real.cosh (q * beta / 6) * (2 - g (2 * beta) / g beta) :=
        mul_le_mul_of_nonneg_right hcosh hfactor
  calc
    (9 / 4) * (q / 2) ≤ (9 / 4) * (q / 2) *
        (Real.cosh (q * beta / 6) * (2 - g (2 * beta) / g beta)) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hcosh_factor
          (show 0 ≤ (9 / 4 : ℝ) * (q / 2) by positivity)
    _ = (9 / 4) * Real.cosh (q * beta / 6) *
        ((q / 2) * (2 - g (2 * beta) / g beta)) := by ring
    _ ≤ (9 / 4) * Real.cosh (q * beta / 6) *
        (d - g (q * beta) / g beta) := by
      exact mul_le_mul_of_nonneg_left hgap
        (mul_nonneg (by norm_num) (Real.cosh_pos _).le)

private theorem hasDerivAt_mul_coth {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y * coth y)
      ((Real.sinh x * Real.cosh x - x) / Real.sinh x ^ 2) x := by
  have hs : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have h := ((hasDerivAt_id x).fun_mul (Real.hasDerivAt_cosh x)).fun_div
    (Real.hasDerivAt_sinh x) hs
  have heq : (fun y : ℝ => y * coth y) = (fun y => y * Real.cosh y / Real.sinh y) := by
    funext y
    rw [coth, mul_div_assoc']
  rw [heq]
  convert h using 1
  have hnum : (1 * Real.cosh x + x * Real.sinh x) * Real.sinh x -
      (x * Real.cosh x) * Real.cosh x = Real.sinh x * Real.cosh x - x := by
    calc
      _ = Real.sinh x * Real.cosh x -
          x * (Real.cosh x ^ 2 - Real.sinh x ^ 2) := by ring
      _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; ring
  rw [hnum]

private theorem strictMonoOn_mul_coth :
    StrictMonoOn (fun x : ℝ => x * coth x) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact (hasDerivAt_mul_coth (Set.mem_Ioi.mp hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : 0 < x := hx
    rw [(hasDerivAt_mul_coth hx').deriv]
    have hs := Real.self_lt_sinh_iff.mpr (show 0 < 2 * x by positivity)
    rw [Real.sinh_two_mul] at hs
    exact div_pos (by nlinarith only [hs]) (sq_pos_of_pos (Real.sinh_pos_iff.mpr hx'))

/-- The thermal response is strictly increasing on the full nonnegative axis. -/
theorem g_strictMonoOn_nonneg : StrictMonoOn g (Set.Ici 0) := by
  have hpos (x y : ℝ) (hx : 0 < x) (hxy : x < y) : g x < g y := by
    have hy : 0 < y := hx.trans hxy
    have h3 : (x / 3) * coth (x / 3) < (y / 3) * coth (y / 3) :=
      strictMonoOn_mul_coth (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by linarith)
    have h6 : (x / 6) * coth (x / 6) < (y / 6) * coth (y / 6) :=
      strictMonoOn_mul_coth (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity)) (by linarith)
    rw [g, ite_eq_right hx.ne', g, ite_eq_right hy.ne']
    nlinarith only [h3, h6]
  intro x hx y hy hxy
  rcases (Set.mem_Ici.mp hx).eq_or_lt with rfl | hx'
  · have hy' : 0 < y := hxy
    have h := hpos (y / 2) y (by positivity) (by linarith)
    have hfloor := half_le_g (v := y / 2) (by positivity)
    have hg0 : g 0 = 1 / 2 := by norm_num [g]
    rw [hg0]
    exact hfloor.trans_lt h
  · exact hpos x y hx' hxy

private theorem g_half_ratio_core {v : ℝ} (hv : 0 ≤ v) :
    Real.cosh (v / 6) * (2 - g v / g (v / 2)) = 1 := by
  have htwo := coefficient_two_two (beta := v / 2) (by positivity)
  change (9 / 4) * Real.cosh (2 * (v / 2) / 6) *
    (2 - g (2 * (v / 2)) / g (v / 2)) = 9 / 4 at htwo
  rw [show 2 * (v / 2) = v by ring] at htwo
  nlinarith only [htwo]

/-- The sharp scalar lower bound under an arbitrary bounded modal charge,
including the tracial endpoint. The degree may be any real number at least two. -/
theorem coefficient_capped_lower_bound {beta d v : ℝ} (hbeta : 0 ≤ beta)
    (hd : 2 ≤ d) (hv : 0 ≤ v) (hcap : v ≤ d * beta) :
    9 / 4 ≤ (9 / 4) * Real.cosh (v / 6) * (d - g v / g beta) ∧
      ((9 / 4) * Real.cosh (v / 6) * (d - g v / g beta) = 9 / 4 ↔
        d = 2 ∧ v = 2 * beta) := by
  have hc : 0 < (9 / 4 : ℝ) * Real.cosh (v / 6) := by positivity
  by_cases hvlow : v ≤ 2 * beta
  · have hv2 : 0 ≤ v / 2 := by positivity
    have hv2beta : v / 2 ≤ beta := by linarith
    have hgm : g (v / 2) ≤ g beta :=
      g_strictMonoOn_nonneg.monotoneOn hv2 hbeta hv2beta
    have hratio : g v / g beta ≤ g v / g (v / 2) :=
      div_le_div_of_nonneg_left (g_pos hv).le (g_pos hv2) hgm
    have hcore := g_half_ratio_core hv
    have hbase : (9 / 4 : ℝ) * Real.cosh (v / 6) *
        (2 - g v / g (v / 2)) = 9 / 4 := by nlinarith only [hcore]
    have hgap : 2 - g v / g (v / 2) ≤ d - g v / g beta := by linarith
    have hbound := mul_le_mul_of_nonneg_left hgap hc.le
    rw [hbase] at hbound
    refine ⟨hbound, ?_⟩
    constructor
    · intro heq
      have hgap_eq : d - g v / g beta = 2 - g v / g (v / 2) := by
        apply mul_left_cancel₀ hc.ne'
        rw [heq, hbase]
      have hd_eq : d = 2 := by linarith
      have hratio_eq : g v / g beta = g v / g (v / 2) := by linarith
      have hv_eq : v = 2 * beta := by
        by_contra hne
        have hlt : v / 2 < beta := by
          have h := lt_of_le_of_ne hvlow hne
          linarith
        have hgm_lt := g_strictMonoOn_nonneg hv2 hbeta hlt
        have hratio_lt : g v / g beta < g v / g (v / 2) :=
          div_lt_div_of_pos_left (g_pos hv) (g_pos hv2) hgm_lt
        linarith
      exact ⟨hd_eq, hv_eq⟩
    · rintro ⟨rfl, rfl⟩
      exact (show (9 / 4 : ℝ) * Real.cosh (2 * beta / 6) *
        (2 - g (2 * beta) / g beta) = 9 / 4 from coefficient_two_two hbeta)
  · have hb : 0 < beta := by
      by_contra h
      have hb0 : beta = 0 := by linarith
      apply hvlow
      simpa [hb0] using hcap
    have hq : 2 < v / beta := (lt_div_iff₀ hb).2 (lt_of_not_ge hvlow)
    have hqd : v / beta ≤ d := (div_le_iff₀ hb).2 (by simpa [mul_comm] using hcap)
    have hreal := coefficient_real_q_lower_bound hbeta hq.le hqd
    have hscale : v / beta * beta = v := by field_simp [hb.ne']
    rw [hscale] at hreal
    have hstrict : (9 / 4 : ℝ) < (9 / 4) * (v / beta / 2) := by linarith
    have hstrict' := hstrict.trans_le hreal
    refine ⟨hstrict'.le, ?_⟩
    constructor
    · intro heq
      linarith
    · rintro ⟨_, hv_eq⟩
      exact False.elim (hvlow hv_eq.le)

/-- Degree one has a nonnegative scalar coefficient under the cap, with
zero attained precisely at the cap. -/
theorem coefficient_capped_degree_one {beta v : ℝ} (hbeta : 0 ≤ beta)
    (hv : 0 ≤ v) (hcap : v ≤ beta) :
    0 ≤ (9 / 4) * Real.cosh (v / 6) * (1 - g v / g beta) ∧
      ((9 / 4) * Real.cosh (v / 6) * (1 - g v / g beta) = 0 ↔ v = beta) := by
  have hc : 0 < (9 / 4 : ℝ) * Real.cosh (v / 6) := by positivity
  have hratio : g v / g beta ≤ 1 := by
    apply (div_le_iff₀ (g_pos hbeta)).2
    simpa using g_strictMonoOn_nonneg.monotoneOn hv hbeta hcap
  refine ⟨mul_nonneg hc.le (sub_nonneg.mpr hratio), ?_⟩
  constructor
  · intro hz
    have hzero : 1 - g v / g beta = 0 := (mul_eq_zero.mp hz).resolve_left hc.ne'
    have heq : g v / g beta = 1 := by linarith
    have hgeq := (div_eq_one_iff_eq (g_pos hbeta).ne').mp heq
    exact (g_strictMonoOn_nonneg.eq_iff_eq hv hbeta).mp hgeq
  · rintro rfl
    rw [div_self (g_pos hbeta).ne']
    ring

#print axioms g_strictMonoOn_nonneg
#print axioms coefficient_capped_lower_bound
#print axioms coefficient_capped_degree_one
#print axioms g_double_ratio
#print axioms coefficient_two_two
#print axioms coefficient_lower_bound
#print axioms coefficient_pos
#print axioms coefficient_eq_zero_iff
#print axioms coefficient_real_q_lower_bound

end
end WuCubicThermalBohrGap
