/- GID: D5/S1/Recurrence/Algebraic/AlgebraicPrimitiveDescent
   generality: I
   mirror-B: D5/B/S1/Recurrence/Algebraic/AlgebraicPrimitiveDescent
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.Derivation.MapCoeffs, mathlib/module/Mathlib.FieldTheory.Minpoly.Field, mathlib/module/Mathlib.Tactic.FieldSimp, mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: An algebraic primitive of a base-field element descends to a characteristic-zero differential field. -/

import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The coefficient-wise differentiation and minimal-polynomial APIs are reused
directly. The coefficient of degree one below the leading term yields a
primitive in the base field, without requiring a normal closure or a trace.

proof_shape: exists_primitive_of_isAlgebraic: content
escape_witness: the derivative of the next-to-leading minimal-polynomial
coefficient is the negative of the degree times the prescribed derivative.
-/

set_option autoImplicit false

open Polynomial
open scoped Differential

namespace D5.S1.Recurrence.Algebraic.AlgebraicPrimitiveDescent

variable {K L : Type*} [Field K] [CharZero K] [Differential K]
  [CommRing L] [Nontrivial L] [Differential L] [Algebra K L]
  [DifferentialAlgebra K L]

/-- If an algebraic element has derivative in the base differential field,
that derivative already has a primitive in the base field. -/
theorem exists_primitive_of_isAlgebraic (x : L) (g : K)
    (hx : IsAlgebraic K x) (hg : x′ = algebraMap K L g) :
    ∃ h : K, h′ = g := by
  let p : K[X] := minpoly K x
  have hi : IsIntegral K x := hx.isIntegral
  have hm : p.Monic := minpoly.monic hi
  have hn : 0 < p.natDegree := minpoly.natDegree_pos hi
  let q : K[X] := Differential.mapCoeffs p + C g * derivative p
  have hqeval : aeval x q = 0 := by
    have hd := Differential.deriv_aeval_eq x p
    have heval : aeval x p = 0 := minpoly.aeval K x
    rw [heval, map_zero, hg] at hd
    simpa [q, mul_comm] using hd.symm
  have hqdegree : q.degree < p.degree := by
    rw [degree_eq_natDegree hm.ne_zero]
    apply (degree_lt_iff_coeff_zero q p.natDegree).mpr
    intro m hnm
    simp only [q, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul,
      coeff_derivative]
    have hs : p.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hs, zero_mul, mul_zero, add_zero]
    rcases eq_or_lt_of_le hnm with he | hl
    · rw [← he, coeff_natDegree, hm.leadingCoeff]
      simp
    · rw [coeff_eq_zero_of_natDegree_lt hl]
      simp
  have hqzero : q = 0 := by
    by_contra hq
    exact (not_lt_of_ge (minpoly.degree_le_of_ne_zero K x hq hqeval)) hqdegree
  have hcoeff := congrArg (fun r : K[X] => r.coeff (p.natDegree - 1)) hqzero
  have hindex : p.natDegree - 1 + 1 = p.natDegree := by omega
  simp only [q, coeff_add, Differential.coeff_mapCoeffs, coeff_C_mul,
    coeff_derivative, hindex, coeff_natDegree, hm.leadingCoeff, one_mul,
    coeff_zero] at hcoeff
  have hcast : ((p.natDegree - 1 : ℕ) : K) + 1 = (p.natDegree : K) := by
    exact_mod_cast hindex
  rw [hcast] at hcoeff
  have hnzero : (p.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine ⟨-p.coeff (p.natDegree - 1) / (p.natDegree : K), ?_⟩
  rw [Derivation.leibniz_div_const _ _ _ (by simp), smul_eq_mul, map_neg]
  have hc : (p.coeff (p.natDegree - 1))′ = -(g * (p.natDegree : K)) :=
    eq_neg_of_add_eq_zero_left hcoeff
  rw [hc, neg_neg]
  field_simp [hnzero]

#print axioms exists_primitive_of_isAlgebraic

end D5.S1.Recurrence.Algebraic.AlgebraicPrimitiveDescent
