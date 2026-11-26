import OmegaMath.NumberTheory.GRH.Lib.Weil.Fock.OscillatorPair
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Products of theta forms detect all good forms (see New.Rows.Separation).

This file: Explicit degree-uniform decay of Heisenberg matrix coefficients of homogeneous Fock
vectors. -/

open MeasureTheory Real Fintype MvPolynomial Matrix.Norms.L2Operator Heisenberg IsVacuum Rep WithLp

/-- Let P be homogeneous of degree d in |ι| > 0 variables, v = v_P, σ in U(ε), A ≥ d + |ι| and n
natural numbers, y ≠ 0. Then |⟨v, ϱ(y)ω(σ)v⟩| ≤ (4(A+n))^n |y|^{−2n} ‖σ‖^{|ι|+2n} ⟨v,v⟩,
with Euclidean and ℓ² operator norms. -/
lemma norm_realInner_realHeisOp_le {ι : Type} [Fintype ι] [Nonempty ι] {ε P v y} (σ : USign (n := ι)
  ε) (hv : v = polyVector ε P) {d A n} (hP : ∀ (c : ℝ) x, eval (c • x) P = c ^ d * eval x P) (hA :
  d + card ι ≤ A) (h0 : A ≠ 0) (hy : 0 < ‖toLp 2 y‖) : ‖realInner v (realHeisOp y (realWeil σ v))‖ ≤
  ‖σ.1.1‖ ^ (card ι + 2 * n) * (realInner v v).re * (4 * (A + n)) ^ n * ‖toLp 2 y‖⁻¹ ^ (2 * n) := by
  let c := √(n / A + 1)
  obtain ⟨i, p⟩ := (integrable_norm_sq v).comp_smul (R := c⁻¹) (by positivity),
    ((realAction ε).2 σ).add_left _ y
  have j := p.integrable_comp_of_integrable i
  rw [← (realInner v).comp_apply]; simp [↓map_integrated_eq_integral, weilRep, realAction,
    modelInner_self]
  grw [norm_realMultiplier_le, norm_integral_le_of_norm_le ((i.add j).mul_const ((4 * (A + n) *
    (‖σ.1.1‖ / ‖toLp 2 y‖) ^ 2) ^ n / (c ^ 2) ^ card ι / 2)) (.of_forall ?_)]
  simp [mul_comm _ 2, ↓integral_mul_const, ↓integral_add' i j, ↓p.hasLaw.integral_comp i.1, mul_pow,
    pow_mul, ← two_mul, ↓Measure.integral_comp_inv_smul _ (‖v ·‖ ^ 2), div_pow, pow_add, field]
  simp_intro x [fun x ↦ (by simp (disch := positivity) [*, realVac, star_dot_self_eq_norm_sq, sq, c,
    ← exp_nat_mul, mul_assoc, ← exp_add, field, star_trivial] : ‖v (c⁻¹ • x)‖ = ‖v x‖ * exp
    (‖toLp 2 x‖ ^ 2 / (n + A) / 2) ^ n / |c| ^ d), ↓modelInner_heisOp_vacElem,
    ← conj_modelInner]; grw [← two_mul_le_add_sq]
  simp [field, pow_right_comm _ d, mul_assoc, ← pow_add, ← mul_pow, ← exp_add]
  grw [sq_sqrt (by bound), add_one_le_exp, ← exp_nat_mul, hA, mul_div_left_comm,
    div_self_le_one, exp_nat_mul, ← exp_one_mul_le_exp]; gcongr; field_simp
  grw [norm_le_add_norm_add, σ.1.1.l2_opNorm_mulVec (toLp 2 x), ← one_mul ‖_ + _‖,
    U.one_le_norm σ, add_sq_le]; linarith!
