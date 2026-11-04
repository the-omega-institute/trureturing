/- GID: D5/S3/Analytic/Zeta/QuadraticClassNumberSquare
   generality: G
   mirror-B: D5/B/S3/Analytic/Zeta/QuadraticClassNumberSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual imaginary quadratic ideal class number and squared finite quadratic excess. -/

import D5.S3.Analytic.Zeta.QuadraticZetaFactorization
import D5.S3.Arith.QuadraticFields.QuadraticImaginaryInvariants
import Mathlib.Tactic.FinCases

namespace D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary

open Filter DirichletCharacter
open D5.S3.Analytic.Zeta.PrimeQuadraticLValues
open scoped Topology BigOperators

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

/-- The value at one is obtained from the genuine number-field residue and the
quadratic Euler factorization. No finite character-sum formula is assumed. -/
theorem LFunction_one_eq_classNumber (hp : 3 < p) :
    LFunction (primeCharacter p) 1 =
      (Real.pi * (NumberField.classNumber (Field p) : ℝ) / Real.sqrt (p : ℝ) : ℂ) := by
  have hp2 : p ≠ 2 := by omega
  have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : (1 : ℝ) < s := hs
      intro heq
      change (s : ℂ) = 1 at heq
      apply (ne_of_gt hs')
      exact_mod_cast heq
  have hζ := riemannZeta_residue_one.comp ht
  have hL : Tendsto (fun s : ℝ => LFunction (primeCharacter p) s)
      (𝓝[>] 1) (𝓝 (LFunction (primeCharacter p) 1)) := by
    exact ((differentiable_LFunction (primeCharacter_nontrivial p hp2)).continuous.tendsto 1).comp
      (by simpa using (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds)
  have hprod : Tendsto (fun s : ℝ =>
      ((s : ℂ) - 1) * NumberField.dedekindZeta (Field p) s)
      (𝓝[>] 1) (𝓝 (LFunction (primeCharacter p) 1)) := by
    have h := hζ.mul hL
    simp only [Function.comp_def, one_mul] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [dedekindZeta_eq_riemannZeta_mul_LFunction p (by simpa using hs)]
    ring
  have hres := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (Field p)
  rw [zeta_residue p hp] at hres
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_div] using
    tendsto_nhds_unique hprod hres

/-- The squared functional equation suffices: its sign need not be computed to
identify the square of L(0) with the square of the actual ideal class number. -/
theorem LFunction_zero_sq_classNumber (hp : 3 < p) :
    LFunction (primeCharacter p) 0 ^ 2 =
      (NumberField.classNumber (Field p) : ℂ) ^ 2 := by
  have hp2 : p ≠ 2 := by omega
  have hp1 : p ≠ 1 := by omega
  have hself : (primeCharacter p)⁻¹ = primeCharacter p :=
    (primeCharacter_quadratic p).inv
  have h := D5.S3.Analytic.Zeta.QuadraticLValueSquare.zero_sq p hp1 (primeCharacter p)
    (primeCharacter_primitive p hp2) hself (primeCharacter_nontrivial p hp2)
    (primeCharacter_odd p Fact.out)
  rw [LFunction_one_eq_classNumber p hp] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p)
  have hsne : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)).ne'
  calc
    _ = (p : ℂ) *
        ((Real.pi * (NumberField.classNumber (Field p) : ℝ) /
          Real.sqrt (p : ℝ) : ℂ) / (Real.pi : ℂ)) ^ 2 := h
    _ = _ := by
      push_cast
      field_simp [hπ, hsne]
      rw [hs]
      ring

/-- An integer-valued half-interval character sum, including its zero term.
The value is independent of the class-number definition. -/
noncomputable def quadraticExcess : ℤ :=
  ∑ x : ZMod p, if x.val ≤ (p - 1) / 2 then quadraticChar (ZMod p) x else 0

/-- Sufficient actual-class-number bridge for congruences depending on h squared.
In particular, this does not redefine h as a character sum. -/
theorem quadraticExcess_sq_classNumber (hp : 3 < p) :
    quadraticExcess p ^ 2 =
      (2 - legendreSym p 2) ^ 2 * (NumberField.classNumber (Field p) : ℤ) ^ 2 := by
  have hp2 : p ≠ 2 := by omega
  have hc := half_sum_eq_LFunction_zero p hp2 (primeCharacter p)
    (primeCharacter_nontrivial p hp2) (primeCharacter_quadratic p)
  have hc' : (quadraticExcess p : ℂ) =
      (2 - (legendreSym p 2 : ℂ)) * LFunction (primeCharacter p) 0 := by
    simpa [quadraticExcess, primeCharacter, legendreSym, Int.cast_sum] using hc
  have heq : (quadraticExcess p : ℂ) ^ 2 =
      (2 - (legendreSym p 2 : ℂ)) ^ 2 * (NumberField.classNumber (Field p) : ℂ) ^ 2 := by
    rw [hc', mul_pow, LFunction_zero_sq_classNumber p hp]
  exact_mod_cast heq

/-- Least representatives identify the excess with its literal finite positive interval;
the additional index zero contributes zero. -/
theorem quadraticExcess_eq_range :
    quadraticExcess p =
      ∑ j ∈ Finset.range ((p - 1) / 2 + 1), legendreSym p (j : ℤ) := by
  classical
  have hp0 := (Fact.out : p.Prime).pos
  unfold quadraticExcess
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact Finset.mem_range.mpr (by omega)
  · intro x _ y _ h
    exact ZMod.val_injective p h
  · intro j hj
    have hj' := Finset.mem_range.mp hj
    have hjp : j < p := by omega
    refine ⟨(j : ZMod p), ?_, ZMod.val_cast_of_lt hjp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ZMod.val_cast_of_lt hjp]
    omega
  · intro x _
    simp [legendreSym]

/-- Every nonzero lower-half character value is odd, so the excess has the parity
of the interval length. In this prime family that length is odd. -/
theorem quadraticExcess_mod_two : (quadraticExcess p : ZMod 2) = 1 := by
  have hp4 : p % 4 = 3 := Fact.out
  have hn : ((p - 1) / 2) % 2 = 1 := by omega
  have hterm (i : ℕ) (hi : i ∈ Finset.range ((p - 1) / 2)) :
      (legendreSym p ((i + 1 : ℕ) : ℤ) : ZMod 2) = 1 := by
    have hi' := Finset.mem_range.mp hi
    have hip : i + 1 < p := by omega
    have hiz : ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_cast_of_lt hip, ZMod.val_zero] at hv
      omega
    rcases legendreSym.eq_one_or_neg_one p (a := ((i + 1 : ℕ) : ℤ))
      (by simpa using hiz) with h | h <;> rw [h] <;> norm_num <;> decide
  rw [quadraticExcess_eq_range, Int.cast_sum, Finset.sum_range_succ']
  simp only [Nat.cast_zero, legendreSym.at_zero, Int.cast_zero, add_zero]
  calc
    _ = ∑ _i ∈ Finset.range ((p - 1) / 2), (1 : ZMod 2) :=
      Finset.sum_congr rfl hterm
    _ = (((p - 1) / 2 : ℕ) : ZMod 2) := by simp
    _ = 1 := by rw [← ZMod.natCast_mod ((p - 1) / 2) 2, hn]; norm_num

/-- Oddness of the genuine maximal-order class number follows from the proved
squared bridge and the parity of the finite interval. -/
theorem classNumber_odd (hp : 3 < p) : Odd (NumberField.classNumber (Field p)) := by
  have hp2 : p ≠ 2 := by omega
  have htwo : (2 : ZMod p) ≠ 0 :=
    Ring.two_ne_zero ((ZMod.ringChar_zmod_n p).substr hp2)
  have hcoef : (((2 - legendreSym p 2 : ℤ) : ZMod 2)) = 1 := by
    rcases legendreSym.eq_one_or_neg_one p (a := 2) (by simpa using htwo) with h | h <;>
      rw [h] <;> norm_num <;> decide
  have h := congrArg (fun z : ℤ => (z : ZMod 2)) (quadraticExcess_sq_classNumber p hp)
  simp only [Int.cast_pow, Int.cast_mul, Int.cast_natCast] at h
  rw [quadraticExcess_mod_two, hcoef, one_pow, one_mul] at h
  have hsq : ∀ x : ZMod 2, x ^ 2 = x := by decide
  rw [hsq] at h
  apply Nat.odd_iff.mpr
  have hh := (ZMod.natCast_eq_natCast_iff'
    (NumberField.classNumber (Field p)) 1 2).mp (by simpa using h.symm)
  simpa using hh

end D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.PrimeImaginary
