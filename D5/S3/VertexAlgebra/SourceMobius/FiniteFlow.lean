/- GID: D5/S3/VertexAlgebra/SourceMobius/FiniteFlow
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceMobius/FiniteFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Polynomial algebra flow of the actual locally nilpotent source mode. -/
import D5.S3.VertexAlgebra.SourceMobius.Nilpotence
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace D5.S3.VertexAlgebra.SourceMobius
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents MvPolynomial
open LatticeHalfFockFiniteCorrection (sourceWeight)
open scoped BigOperators

/-- The zero-constant polynomial primitive over the complex oscillator algebra. -/
private def primitive (D : LatticeData) (q : Polynomial (Oscillator D)) :
    Polynomial (Oscillator D) :=
  ∑ n ∈ q.support, Polynomial.monomial (n+1) ((n+1 : ℂ)⁻¹ • q.coeff n)

private theorem primitive_coeff_zero (D : LatticeData) (q : Polynomial (Oscillator D)) :
    (primitive D q).coeff 0 = 0 := by
  classical
  simp [primitive, Polynomial.coeff_sum, Polynomial.coeff_monomial]

private theorem primitive_coeff_succ (D : LatticeData) (q : Polynomial (Oscillator D)) (n : ℕ) :
    (primitive D q).coeff (n+1) = (n+1 : ℂ)⁻¹ • q.coeff n := by
  classical
  by_cases hn : n ∈ q.support
  · simp [primitive, Polynomial.coeff_sum, Polynomial.coeff_monomial, hn]
  · have hz : q.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [primitive, Polynomial.coeff_sum, Polynomial.coeff_monomial, hn, hz]

private theorem derivative_primitive (D : LatticeData) (q : Polynomial (Oscillator D)) :
    (primitive D q).derivative = q := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_derivative, primitive_coeff_succ]
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [show (n + 1 : Oscillator D) = C (n + 1 : ℂ) by simp]
  simp only [smul_eq_C_mul]
  rw [mul_right_comm, ← map_mul, inv_mul_cancel₀ hn, map_one, one_mul]

/-- Polynomial flow coordinates are constructed by integration of the actual
lowering recurrence, including the charge term at oscillator order zero. -/
def flowVariable (D : LatticeData) (a : Charge D) (i : Fin D.rank) :
    ℕ → Polynomial (Oscillator D)
  | 0 => Polynomial.C (X (i,0)) +
      Polynomial.monomial 1 (C (bilinear D (unitCharge D i) a : ℂ))
  | r+1 => Polynomial.C (X (i,r+1)) + (r+2 : ℂ) • primitive D (flowVariable D a i r)

/-- Algebra substitution on every finite original oscillator polynomial. -/
def flowPolynomial (D : LatticeData) (a : Charge D) :
    Oscillator D →ₐ[ℂ] Polynomial (Oscillator D) :=
  aeval (fun x : Index D => flowVariable D a x.1 x.2)

private theorem flowVariable_coeff_zero (D : LatticeData) (a : Charge D)
    (i : Fin D.rank) (r : ℕ) : (flowVariable D a i r).coeff 0 = X (i,r) := by
  cases r <;> simp [flowVariable, primitive_coeff_zero]

private theorem flowVariable_derivative (D : LatticeData) (a : Charge D)
    (x : Index D) :
    (flowVariable D a x.1 x.2).derivative = flowPolynomial D a (sectorL1 D a (X x)) := by
  rcases x with ⟨i,r⟩
  cases r with
  | zero => simp [flowVariable, flowPolynomial, sectorL1, loweringVariable]
  | succ r =>
    simp [flowVariable, flowPolynomial, sectorL1, loweringVariable,
      derivative_primitive, Polynomial.derivative_smul]

private theorem flowPolynomial_coeff_zero (D : LatticeData) (a : Charge D)
    (p : Oscillator D) : (flowPolynomial D a p).coeff 0 = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [flowPolynomial, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    simp [flowPolynomial, flowVariable_coeff_zero]

/-- Polynomial differential equation on all source polynomials, proved from
Leibniz and the actual charge-sensitive generator action. -/
theorem flowPolynomial_derivative (D : LatticeData) (a : Charge D)
    (p : Oscillator D) :
    (flowPolynomial D a p).derivative = flowPolynomial D a (sectorL1 D a p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [flowPolynomial, algebraMap_eq]
  | add p q hp hq => simp only [map_add, Polynomial.derivative_add, hp, hq]
  | mul_X p x hp =>
    rw [map_mul, Polynomial.derivative_mul, hp]
    rw [show flowPolynomial D a (X x) = flowVariable D a x.1 x.2 by simp [flowPolynomial],
      flowVariable_derivative, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    rw [show flowPolynomial D a (X x) = flowVariable D a x.1 x.2 by simp [flowPolynomial]]
    ring

/-- Each polynomial coefficient is the factorial-normalized actual derivation
power. This is an all-polynomial calculation, not a variable lookup table. -/
theorem flowPolynomial_coeff (D : LatticeData) (a : Charge D) (p : Oscillator D) (n : ℕ) :
    (flowPolynomial D a p).coeff n = (n.factorial : ℂ)⁻¹ •
      ((sectorL1 D a).toLinearMap ^ n) p := by
  induction n generalizing p with
  | zero => simpa using flowPolynomial_coeff_zero D a p
  | succ n ih =>
    have recurrence := congrArg (fun q : Polynomial (Oscillator D) => q.coeff n)
      (flowPolynomial_derivative D a p)
    rw [Polynomial.coeff_derivative, ih] at recurrence
    have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have normalized := congrArg (fun q : Oscillator D => (n+1 : ℂ)⁻¹ • q) recurrence
    rw [show (n + 1 : Oscillator D) = C (n + 1 : ℂ) by simp,
      mul_comm, ← smul_eq_C_mul, smul_smul, inv_mul_cancel₀ hn, one_smul] at normalized
    rw [normalized, pow_succ, Module.End.mul_apply]
    simp only [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, smul_smul]
    congr 1
    push_cast
    ring

/-- Actual finite charge-sector source flow, as an algebra operation. -/
def sectorFlow (D : LatticeData) (a : Charge D) (u : ℂ) : Oscillator D →ₐ[ℂ] Oscillator D :=
  (Polynomial.eval₂AlgHom (AlgHom.id ℂ (Oscillator D)) (C u)
    (fun _ => Commute.all _ _)).comp (flowPolynomial D a)


/-- Finite Taylor expansion at any annihilating bound. -/
theorem flowPolynomial_eq_sum (D : LatticeData) (a : Charge D) (p : Oscillator D)
    (R : ℕ) (h : ((sectorL1 D a).toLinearMap ^ (R+1)) p = 0) :
    flowPolynomial D a p = ∑ n ∈ Finset.range (R+1),
      Polynomial.monomial n ((n.factorial : ℂ)⁻¹ • ((sectorL1 D a).toLinearMap ^ n) p) := by
  classical
  ext n
  rw [flowPolynomial_coeff]
  by_cases hn : n < R+1
  · simp [Polynomial.coeff_sum, Polynomial.coeff_monomial, hn]
  · have vanish : ((sectorL1 D a).toLinearMap ^ n) p = 0 := by
      rw [show n = (n-(R+1))+(R+1) by omega, pow_add, Module.End.mul_apply, h, map_zero]
    simp [Polynomial.coeff_sum, Polynomial.coeff_monomial, hn, vanish]

/-- The algebra substitution is exactly the finite factorial exponential at
any actual annihilating bound. -/
theorem sectorFlow_eq_sum_of_killed (D : LatticeData) (a : Charge D) (u : ℂ)
    (p : Oscillator D) (R : ℕ) (h : ((sectorL1 D a).toLinearMap ^ (R+1)) p = 0) :
    sectorFlow D a u p = ∑ n ∈ Finset.range (R+1),
      (u ^ n / (n.factorial : ℂ)) • ((sectorL1 D a).toLinearMap ^ n) p := by
  classical
  change Polynomial.eval₂ (RingHom.id (Oscillator D)) (C u) (flowPolynomial D a p) = _
  rw [flowPolynomial_eq_sum D a p R h, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Polynomial.eval₂_monomial, RingHom.id_apply, smul_eq_C_mul,
    map_div₀, map_pow, div_eq_mul_inv, map_mul]
  ring

/-- Existing oscillator weighted degree supplies the finite cutoff. -/
theorem sectorFlow_eq_sum (D : LatticeData) (a : Charge D) (u : ℂ) (p : Oscillator D) :
    sectorFlow D a u p = ∑ n ∈ Finset.range (weightedTotalDegree (sourceWeight D) p + 1),
      (u ^ n / (n.factorial : ℂ)) • ((sectorL1 D a).toLinearMap ^ n) p :=
  sectorFlow_eq_sum_of_killed D a u p _ (sectorL1_degree_bound D a p)

/-- Padding by zero coefficients permits a common cutoff for finite charge support. -/
theorem sectorFlow_eq_sum_of_bound (D : LatticeData) (a : Charge D) (u : ℂ)
    (p : Oscillator D) (R : ℕ) (h : weightedTotalDegree (sourceWeight D) p ≤ R) :
    sectorFlow D a u p = ∑ n ∈ Finset.range (R+1),
      (u ^ n / (n.factorial : ℂ)) • ((sectorL1 D a).toLinearMap ^ n) p := by
  rw [sectorFlow_eq_sum]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hnot
  have high : weightedTotalDegree (sourceWeight D) p + 1 ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hnot
  have vanish : ((sectorL1 D a).toLinearMap ^ n) p = 0 := by
    rw [show n = (n-(weightedTotalDegree (sourceWeight D) p+1)) +
      (weightedTotalDegree (sourceWeight D) p+1) by omega, pow_add, Module.End.mul_apply,
      sectorL1_degree_bound, map_zero]
  rw [vanish, smul_zero]

end D5.S3.VertexAlgebra.SourceMobius

