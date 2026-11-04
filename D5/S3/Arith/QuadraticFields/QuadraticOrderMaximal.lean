/- GID: D5/S3/Arith/QuadraticFields/QuadraticOrderMaximal
   generality: G
   mirror-B: D5/B/S3/Arith/QuadraticFields/QuadraticOrderMaximal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A monogenic quadratic integer order with squarefree discriminant is maximal. -/

import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

namespace D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal

open QuadraticAlgebra
open scoped NumberField

/-- A squarefree integer cannot cancel a nontrivial square denominator. -/
theorem integer_of_squarefree_mul_sq_integral {d : ℤ} (hd : Squarefree d) (q : ℚ)
    (hq : IsIntegral ℤ ((d : ℚ) * q ^ 2)) : ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq
  change (k : ℚ) = (d : ℚ) * q ^ 2 at hk
  have heq : d * q.num ^ 2 = (q.den : ℤ) ^ 2 * k := by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hk]
    calc
      (d : ℚ) * (q.num : ℚ) ^ 2 = d * (q * q.den) ^ 2 := by rw [Rat.mul_den_eq_num]
      _ = (q.den : ℚ) ^ 2 * (d * q ^ 2) := by ring
  have hdiv : (q.den : ℤ) ^ 2 ∣ d * q.num ^ 2 := ⟨k, heq⟩
  have hc : IsCoprime ((q.den : ℤ) ^ 2) (q.num ^ 2) :=
    q.isCoprime_num_den.symm.pow
  have hu : IsUnit (q.den : ℤ) := hd _ (by simpa [sq] using hc.dvd_of_dvd_mul_right hdiv)
  have hden : q.den = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact_mod_cast h
    · have := q.den_pos
      omega
  exact ⟨q.num, (Rat.den_eq_one_iff q).mp hden⟩

/-- Every integral element of a squarefree-discriminant quadratic order has integral coordinates.
The discriminant here is that of the order, not an assumed field discriminant. -/
theorem integral_coordinates {a b : ℤ} (hD : Squarefree (QuadraticAlgebra.discr a b))
    (z : QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) (hz : IsIntegral ℤ z) :
    ∃ r s : ℤ, z.re = r ∧ z.im = s := by
  have hs : IsIntegral ℤ (star z) := map_isIntegral_int (starRingEnd _) hz
  have ht : IsIntegral ℤ (QuadraticAlgebra.trace z) := by
    apply (isIntegral_algebraMap_iff (A := ℚ) (B := QuadraticAlgebra ℚ (a : ℚ) (b : ℚ))).mp
    rw [QuadraticAlgebra.algebraMap_trace_eq_add_star]
    exact hz.add hs
  have hn : IsIntegral ℤ (QuadraticAlgebra.norm z) := by
    apply (isIntegral_algebraMap_iff (A := ℚ) (B := QuadraticAlgebra ℚ (a : ℚ) (b : ℚ))).mp
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact hz.mul hs
  have him : IsIntegral ℤ ((QuadraticAlgebra.discr a b : ℤ) * z.im ^ 2 : ℚ) := by
    rw [← QuadraticAlgebra.discr_intCast, mul_comm, QuadraticAlgebra.im_sq_mul_discr]
    exact (ht.pow 2).sub (isIntegral_algebraMap.mul hn)
  obtain ⟨s, hs⟩ := integer_of_squarefree_mul_sq_integral hD z.im him
  have hsi : IsIntegral ℤ (algebraMap (QuadraticAlgebra ℤ a b)
      (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) ⟨0, s⟩) :=
    (IsIntegral.of_finite ℤ (⟨0, s⟩ : QuadraticAlgebra ℤ a b)).algebraMap
  have hre : IsIntegral ℤ (algebraMap ℚ (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) z.re) := by
    convert hz.sub hsi using 1
    ext <;> simp [hs]
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    ((isIntegral_algebraMap_iff (A := ℚ) (B := QuadraticAlgebra ℚ (a : ℚ) (b : ℚ))).mp hre)
  exact ⟨r, s, hr.symm, hs.symm⟩

/-- Maximality of the actual quadratic order, expressed as an integral-closure predicate. -/
theorem isIntegralClosure_of_squarefree_discr {a b : ℤ}
    (hD : Squarefree (QuadraticAlgebra.discr a b)) :
    IsIntegralClosure (QuadraticAlgebra ℤ a b) ℤ
      (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) where
  algebraMap_injective := FaithfulSMul.algebraMap_injective _ _
  isIntegral_iff {z} := by
    constructor
    · intro hz
      obtain ⟨r, s, hr, hs⟩ := integral_coordinates hD z hz
      refine ⟨⟨r, s⟩, ?_⟩
      apply QuadraticAlgebra.ext
      · simpa using hr.symm
      · simpa using hs.symm
    · rintro ⟨w, rfl⟩
      exact (IsIntegral.of_finite ℤ w).algebraMap

/-- The coordinate trace agrees with the algebra trace. -/
theorem algebra_trace_eq {R : Type*} [CommRing R] (a b : R)
    (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = QuadraticAlgebra.trace z := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  simp [Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    QuadraticAlgebra.basis_repr_apply, QuadraticAlgebra.trace_def]
  ring

/-- The order discriminant is the discriminant of its actual integral basis. -/
theorem basis_discr (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = QuadraticAlgebra.discr a b := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, algebra_trace_eq,
    QuadraticAlgebra.trace_def, QuadraticAlgebra.discr_def]
  ring

/-- Negative quadratic orders of discriminant at most minus seven have only the two units.
This deliberately excludes the extra-unit orders of discriminants minus three and minus four. -/
theorem units_eq_one_or_neg_one {a : ℤ} (ha : a ≤ -2)
    (z : QuadraticAlgebra ℤ a 1) (hz : IsUnit z) : z = 1 ∨ z = -1 := by
  have hnorm := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hz
  have henergy : 4 * QuadraticAlgebra.norm z =
      (2 * z.re + z.im) ^ 2 + (-1 - 4 * a) * z.im ^ 2 := by
    simp [QuadraticAlgebra.norm_def]
    ring
  have hnn : 0 ≤ (-1 - 4 * a) * z.im ^ 2 := mul_nonneg (by omega) (sq_nonneg _)
  have hn : QuadraticAlgebra.norm z = 1 := by
    rcases Int.isUnit_iff.mp hnorm with h | h
    · exact h
    · nlinarith [sq_nonneg (2 * z.re + z.im)]
  have him : z.im = 0 := by
    by_contra hi
    have hi1 : 1 ≤ z.im ^ 2 := by
      have := sq_pos_of_ne_zero hi
      omega
    have hcoeff : 7 ≤ -1 - 4 * a := by omega
    nlinarith [sq_nonneg (2 * z.re + z.im), mul_nonneg (by omega : 0 ≤ -1 - 4 * a - 7)
      (by omega : 0 ≤ z.im ^ 2 - 1)]
  have hre : z.re ^ 2 = 1 := by simpa [QuadraticAlgebra.norm_def, him, sq] using hn
  rcases sq_eq_one_iff.mp hre with h | h
  · left
    ext <;> simp [h, him]
  · right
    ext <;> simp [h, him]

section NumberField

variable {a b : ℤ}
variable [Fact (¬ IsSquare (QuadraticAlgebra.discr (a : ℚ) (b : ℚ)))]

instance quadratic_numberField : NumberField (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) :=
  NumberField.of_module_finite ℚ _

/-- The concrete order is isomorphic to the maximal ring of integers, with its actual
integral-closure meaning. No class number is defined by coordinates or a character sum. -/
noncomputable def ringOfIntegersEquiv (hD : Squarefree (QuadraticAlgebra.discr a b)) :
    QuadraticAlgebra ℤ a b ≃ₐ[ℤ] 𝓞 (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) := by
  letI := isIntegralClosure_of_squarefree_discr hD
  exact IsIntegralClosure.equiv ℤ (QuadraticAlgebra ℤ a b)
    (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) _

/-- The genuine number-field discriminant of a squarefree-discriminant quadratic order. -/
theorem numberField_discr (hD : Squarefree (QuadraticAlgebra.discr a b)) :
    NumberField.discr (QuadraticAlgebra ℚ (a : ℚ) (b : ℚ)) =
      QuadraticAlgebra.discr a b := by
  let e := ringOfIntegersEquiv hD
  let B := (QuadraticAlgebra.basis a b).map e.toLinearEquiv
  rw [← NumberField.discr_eq_discr _ B]
  change Algebra.discr ℤ (e ∘ QuadraticAlgebra.basis a b) = _
  rw [← Algebra.discr_eq_discr_of_algEquiv, basis_discr]

end NumberField

namespace PrimeImaginary

/-- The integral generator satisfies omega squared minus omega plus (p+1)/4 equals zero. -/
def orderA (p : ℕ) : ℤ := (-(p : ℤ) - 1) / 4

abbrev Field (p : ℕ) := QuadraticAlgebra ℚ (orderA p : ℚ) ((1 : ℤ) : ℚ)

variable (p : ℕ) [Fact p.Prime] [Fact (p % 4 = 3)]

theorem order_discr : QuadraticAlgebra.discr (orderA p) 1 = -(p : ℤ) := by
  have hp4 : (p : ℤ) % 4 = 3 := by exact_mod_cast (Fact.out : p % 4 = 3)
  simp only [QuadraticAlgebra.discr_def, one_pow, orderA]
  omega

instance nonsquare_discr :
    Fact (¬ IsSquare (QuadraticAlgebra.discr (orderA p : ℚ) (1 : ℚ))) := by
  constructor
  rw [show (1 : ℚ) = ((1 : ℤ) : ℚ) by norm_num, QuadraticAlgebra.discr_intCast, order_discr]
  intro h
  have hp : (0 : ℚ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have := h.nonneg
  push_cast at this
  linarith

instance nonsquare_discr_intCast :
    Fact (¬ IsSquare (QuadraticAlgebra.discr (orderA p : ℚ) ((1 : ℤ) : ℚ))) := by
  simpa only [Int.cast_one] using nonsquare_discr p

instance prime_numberField : NumberField (Field p) :=
  NumberField.of_module_finite ℚ _

private theorem squarefree_discr : Squarefree (QuadraticAlgebra.discr (orderA p) 1) := by
  rw [order_discr]
  exact (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))).squarefree

/-- Identification with the standard algebra generated by a square root of minus p. -/
noncomputable def sqrtFieldEquiv : Field p ≃ₐ[ℚ] QuadraticAlgebra ℚ (-(p : ℚ)) 0 := by
  have hD : QuadraticAlgebra.discr (orderA p : ℚ) (1 : ℚ) = -(p : ℚ) := by
    have h := order_discr p
    simp only [QuadraticAlgebra.discr_def, one_pow] at h ⊢
    exact_mod_cast h
  refine (QuadraticAlgebra.algEquivDiscrZero (orderA p : ℚ) ((1 : ℤ) : ℚ)).trans ?_
  have hD' : QuadraticAlgebra.discr (orderA p : ℚ) ((1 : ℤ) : ℚ) = -(p : ℚ) := by
    simpa only [Int.cast_one] using hD
  rw [hD']
  exact AlgEquiv.refl

/-- The maximal-order discriminant, with the actual NumberField definition. -/
theorem field_discr : NumberField.discr (Field p) = -(p : ℤ) := by
  exact (numberField_discr (a := orderA p) (b := 1) (squarefree_discr p)).trans (order_discr p)

/-- The actual maximal order, rather than the potentially nonmaximal square-root order. -/
noncomputable def maximalOrderEquiv :
    QuadraticAlgebra ℤ (orderA p) 1 ≃ₐ[ℤ] 𝓞 (Field p) := by
  exact ringOfIntegersEquiv (a := orderA p) (b := 1) (squarefree_discr p)

/-- The extra-unit exception is excluded by p greater than three. -/
theorem integral_unit_eq_one_or_neg_one (hp : 3 < p) (u : (𝓞 (Field p))ˣ) :
    (u : 𝓞 (Field p)) = 1 ∨ (u : 𝓞 (Field p)) = -1 := by
  let e := maximalOrderEquiv p
  have ha : orderA p ≤ -2 := by
    have hpd : QuadraticAlgebra.discr (orderA p) 1 = -(p : ℤ) := order_discr p
    simp only [QuadraticAlgebra.discr_def, one_pow] at hpd
    omega
  have hu : IsUnit (e.symm (u : 𝓞 (Field p))) := u.isUnit.map e.symm.toRingHom
  rcases units_eq_one_or_neg_one ha _ hu with h | h
  · left
    apply e.symm.injective
    simpa using h
  · right
    apply e.symm.injective
    simpa using h

end PrimeImaginary

end D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal
