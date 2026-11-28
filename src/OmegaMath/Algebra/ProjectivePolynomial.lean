module

public import OmegaBuild.Commands
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
Omega original.

Binary forms in an affine chart are polynomials with an assigned homogeneous degree.
Infinity contributes the difference between that assigned degree and the affine degree.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.ProjectivePolynomial

open Polynomial

variable {K : Type*} [Field K]

/-- The affine polynomial of the homogeneous linear factor vanishing at a point. -/
noncomputable def rayFactor : Option K → K[X]
  | none => 1
  | some z => X - C z

/-- The homogeneous degree-two form with the two indicated linear factors. -/
noncomputable def nodalQuadratic (r s : Option K) : K[X] := rayFactor r * rayFactor s

/-- Multiplicity of a projective root in the given homogeneous degree. -/
noncomputable def multiplicity (d : ℕ) (r : Option K) (p : K[X]) : ℕ :=
  r.elim (d - p.natDegree) (fun z => p.rootMultiplicity z)

/-- Evaluation in the two standard projective trivializations. -/
noncomputable def eval (d : ℕ) (r : Option K) (p : K[X]) : K :=
  r.elim (p.coeff d) (fun z => p.eval z)

private theorem factor_monic (r : Option K) : (rayFactor r).Monic := by
  cases r <;> simp [rayFactor, monic_X_sub_C]

theorem nodal_monic (r s : Option K) : (nodalQuadratic r s).Monic :=
  (factor_monic r).mul (factor_monic s)

theorem nodal_degree_le (r s : Option K) : (nodalQuadratic r s).natDegree ≤ 2 := by
  cases r <;> cases s <;> simp [nodalQuadratic, rayFactor, natDegree_mul,
    (monic_X_sub_C _).ne_zero]

theorem nodal_square_eval_ne_zero (r s t : Option K) (hr : t ≠ r) (hs : t ≠ s) :
    eval 4 t (nodalQuadratic r s ^ 2) ≠ 0 := by
  cases t with
  | none =>
    cases r with
    | none => exact (hr rfl).elim
    | some a =>
      cases s with
      | none => exact (hs rfl).elim
      | some b =>
        have hm := (nodal_monic (some a) (some b)).pow 2
        have hd : (nodalQuadratic (some a) (some b) ^ 2).natDegree = 4 := by
          rw [(nodal_monic _ _).natDegree_pow]
          simp [nodalQuadratic, rayFactor, natDegree_mul, (monic_X_sub_C _).ne_zero]
        rw [eval, Option.elim_none, ← hd, coeff_natDegree, hm.leadingCoeff]
        exact one_ne_zero
  | some z =>
    have h (v : Option K) (hv : some z ≠ v) : (rayFactor v).eval z ≠ 0 := by
      cases v <;> simpa [rayFactor, sub_ne_zero] using hv
    simpa only [eval, Option.elim_some, eval_pow, eval_mul, nodalQuadratic] using
      pow_ne_zero 2 (mul_ne_zero (h r hr) (h s hs))

theorem eval_smul (d : ℕ) (r : Option K) (a : K) (p : K[X]) :
    eval d r (a • p) = a * eval d r p := by
  cases r <;> simp [eval, smul_eq_C_mul]

theorem multiplicity_smul {a : K} (ha : a ≠ 0) {p : K[X]} (hp : p ≠ 0)
    (d : ℕ) (r : Option K) : multiplicity d r (a • p) = multiplicity d r p := by
  rw [smul_eq_C_mul]
  cases r with
  | none => simp [multiplicity, natDegree_C_mul ha]
  | some z =>
    simp only [multiplicity, Option.elim_some, rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr ha) hp),
      rootMultiplicity_C, zero_add]

theorem nodal_square_multiplicity (r s : Option K) (h : r ≠ s) :
    multiplicity 4 r (nodalQuadratic r s ^ 2) = 2 := by
  classical
  cases r <;> cases s
  · exact (h rfl).elim
  · simp [multiplicity, nodalQuadratic, rayFactor, (monic_X_sub_C _).natDegree_pow]
  · simp [multiplicity, nodalQuadratic, rayFactor, rootMultiplicity_X_sub_C_pow]
  · rename_i a b
    have hab : a ≠ b := fun e => h (congrArg some e)
    simp only [multiplicity, Option.elim_some, nodalQuadratic, rayFactor, mul_pow]
    rw [rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (monic_X_sub_C _).ne_zero)
      (pow_ne_zero _ (monic_X_sub_C _).ne_zero)), rootMultiplicity_X_sub_C_pow]
    have hn : ¬ IsRoot ((X - C b : K[X]) ^ 2) a := by
      simp [IsRoot, sub_eq_zero, hab]
    rw [rootMultiplicity_eq_zero hn, add_zero]

private theorem quotient_constant (m p : K[X]) (hp : p ≠ 0) (hd : p.natDegree ≤ m.natDegree)
    (hh : m ∣ p) : ∃ a : K, p = a • m := by
  obtain ⟨q, hq⟩ := hh
  have hprod : m * q ≠ 0 := hq ▸ hp
  have hdeg : q.natDegree = 0 := by
    rw [hq, natDegree_mul (left_ne_zero_of_mul hprod) (right_ne_zero_of_mul hprod)] at hd
    omega
  exact ⟨q.coeff 0, by rw [hq, eq_C_of_natDegree_eq_zero hdeg, smul_eq_C_mul, mul_comm]; simp⟩

/-- Two distinct projective double roots determine a binary quartic up to scalar. -/
theorem quartic_eq_smul_nodal_square {p : K[X]} (hp : p ≠ 0) (hd : p.natDegree ≤ 4)
    {r s : Option K} (hrs : r ≠ s)
    (hr : multiplicity 4 r p = 2) (hs : multiplicity 4 s p = 2) :
    ∃ a : K, p = a • nodalQuadratic r s ^ 2 := by
  have hfin (z : K) (hz : multiplicity 4 (some z) p = 2) : (X - C z) ^ 2 ∣ p :=
    (le_rootMultiplicity_iff hp).1 (le_of_eq hz.symm)
  have hinf (h : multiplicity 4 none p = 2) : p.natDegree ≤ 2 := by
    change 4 - p.natDegree = 2 at h
    omega
  cases r <;> cases s
  · exact (hrs rfl).elim
  · rename_i b
    simpa [nodalQuadratic, rayFactor] using
      quotient_constant _ p hp (by simpa [(monic_X_sub_C _).natDegree_pow] using hinf hr)
        (hfin b hs)
  · rename_i a
    simpa [nodalQuadratic, rayFactor] using
      quotient_constant _ p hp (by simpa [(monic_X_sub_C _).natDegree_pow] using hinf hs)
        (hfin a hr)
  · rename_i a b
    have hab : a ≠ b := fun e => hrs (congrArg some e)
    have hc : IsCoprime (X - C a) (X - C b) :=
      isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hab).isUnit
    have hdiv := hc.pow.mul_dvd (hfin a hr) (hfin b hs)
    apply quotient_constant _ p hp _ (by simpa [nodalQuadratic, rayFactor, mul_pow] using hdiv)
    rw [(nodal_monic _ _).natDegree_pow]
    simpa [nodalQuadratic, rayFactor, natDegree_mul, (monic_X_sub_C _).ne_zero] using hd

end Omega.ProjectivePolynomial
