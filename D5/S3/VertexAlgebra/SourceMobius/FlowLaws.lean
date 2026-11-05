/- GID: D5/S3/VertexAlgebra/SourceMobius/FlowLaws
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceMobius/FlowLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial source flow is an additive one-parameter algebra group. -/
import D5.S3.VertexAlgebra.SourceMobius.FiniteFlow
import Mathlib.Algebra.Polynomial.Taylor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.VertexAlgebra.SourceMobius
open LatticeGeneratingFieldLocality LatticeSugawaraCurrents MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open scoped BigOperators

private theorem flow_commute (D : LatticeData) (a : Charge D) (u : ℂ) (p : Oscillator D) :
    sectorL1 D a (sectorFlow D a u p) = sectorFlow D a u (sectorL1 D a p) := by
  let R := weightedTotalDegree (sourceWeight D) p
  have hp := sectorL1_degree_bound D a p
  have hdp : ((sectorL1 D a).toLinearMap ^ (R+1)) (sectorL1 D a p) = 0 := by
    change ((sectorL1 D a).toLinearMap ^ (R+1)) ((sectorL1 D a).toLinearMap p) = 0
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hp, map_zero]
  rw [sectorFlow_eq_sum_of_killed D a u p R hp,
    sectorFlow_eq_sum_of_killed D a u (sectorL1 D a p) R hdp, map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(sectorL1 D a).map_smul]
  congr 1
  change (sectorL1 D a).toLinearMap (((sectorL1 D a).toLinearMap ^ n) p) =
    ((sectorL1 D a).toLinearMap ^ n) ((sectorL1 D a).toLinearMap p)
  rw [← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]

private theorem flow_pow_commute (D : LatticeData) (a : Charge D) (u : ℂ)
    (p : Oscillator D) (n : ℕ) :
    ((sectorL1 D a).toLinearMap ^ n) (sectorFlow D a u p) =
      sectorFlow D a u (((sectorL1 D a).toLinearMap ^ n) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change sectorL1 D a (sectorFlow D a u (((sectorL1 D a).toLinearMap ^ n) p)) = _
    rw [flow_commute, Module.End.mul_apply]
    rfl

private theorem flow_iterate_derivative (D : LatticeData) (a : Charge D)
    (p : Oscillator D) (n : ℕ) :
    Polynomial.derivative^[n] (flowPolynomial D a p) =
      flowPolynomial D a (((sectorL1 D a).toLinearMap ^ n) p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, flowPolynomial_derivative,
      pow_succ', Module.End.mul_apply]
    rfl

private theorem flowPolynomial_taylor (D : LatticeData) (a : Charge D)
    (u : ℂ) (p : Oscillator D) :
    Polynomial.taylor (C u) (flowPolynomial D a p) = flowPolynomial D a (sectorFlow D a u p) := by
  apply Polynomial.ext
  intro n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply smul_right_injective (M := Oscillator D) hf
  change (n.factorial : ℂ) • _ = (n.factorial : ℂ) • _
  rw [Polynomial.taylor_coeff, flowPolynomial_coeff, smul_smul,
    mul_inv_cancel₀ hf, one_smul, flow_pow_commute]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := Oscillator D) (k := n))
    (flowPolynomial D a p)
  simp only [LinearMap.smul_apply] at h
  rw [flow_iterate_derivative] at h
  have h' : (n.factorial : ℂ) • Polynomial.hasseDeriv n (flowPolynomial D a p) =
      flowPolynomial D a (((sectorL1 D a).toLinearMap ^ n) p) := by
    simpa only [← Nat.cast_smul_eq_nsmul ℂ] using h
  have hh := congrArg (Polynomial.eval (C u)) h'
  rw [Polynomial.eval_smul] at hh
  exact hh

/-- The algebra flow has the additive composition law on every source polynomial. -/
theorem sectorFlow_add (D : LatticeData) (a : Charge D) (u v : ℂ) (p : Oscillator D) :
    sectorFlow D a (u+v) p = sectorFlow D a u (sectorFlow D a v p) := by
  have h := congrArg (Polynomial.eval (C u)) (flowPolynomial_taylor D a v p)
  rw [Polynomial.taylor_eval, ← map_add] at h
  exact h

end D5.S3.VertexAlgebra.SourceMobius
