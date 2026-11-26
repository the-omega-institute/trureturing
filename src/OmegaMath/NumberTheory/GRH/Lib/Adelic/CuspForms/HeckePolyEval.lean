import OmegaMath.NumberTheory.GRH.Lib.Weil.Unramified.SphericalHecke
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up used by: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular
forms.

This file: Two normalisations of the Hecke polynomial are reciprocal to each other. -/

lemma eval_heckePoly {E n} [Field E] [NumberField E] [Fintype n] (w : FinPlace E) t {x} (h :
  x ≠ 0) : (heckePoly w.q (Fintype.card n) t).eval x = x ^ Fintype.card n * heckePolyEval n w t
  x⁻¹ := by erw [Polynomial.eval_finsetSum, Finset.mul_sum]; congr!; simp_all [pow_sub₀]; ring
