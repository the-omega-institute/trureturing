/- GID: D5/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/CubicJacobiNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic residue characters normalize Jacobi sums to primary generators. -/

import D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter
import D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # Cubic Jacobi normalization

Classical Jacobi identities for the Euler residue character over the Eisenstein
order. The proof derives the norm, the chosen ideal direction, the primary
congruence, and the equality with a primary generator. It reuses the established
local cubic selector from CubicIdealCharacter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization

open D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open D5.S3.Factorization.QuadraticIdeals.CubicIdealCharacter

abbrev E := EisensteinOrder

private instance eisensteinDomain : IsDomain E :=
  QuadraticAlgebra.Int.isDomain_iff.mpr
    (not_isSquare_of_neg (by norm_num [QuadraticAlgebra.discr]))

private theorem omega_cube : (QuadraticAlgebra.omega : E) ^ 3 = 1 := by
  have hquad : (QuadraticAlgebra.omega : E) ^ 2 + QuadraticAlgebra.omega + 1 = 0 := by
    rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
    simp
  linear_combination (QuadraticAlgebra.omega - 1) * hquad


/-- Label the Euler power in the quotient, extending the value at zero by zero. -/
def residueCubicValue (P : Ideal E) (x : E ⧸ P) : E := by
  classical
  let q := Ideal.Quotient.mk P
  let m := (Nat.card (E ⧸ P) - 1) / 3
  exact if x = 0 then 0 else
    if x ^ m = 1 then 1 else
      if x ^ m = q QuadraticAlgebra.omega then QuadraticAlgebra.omega
        else QuadraticAlgebra.omega ^ 2

@[simp] theorem residueCubicValue_zero (P : Ideal E) :
    residueCubicValue P 0 = 0 := by
  classical
  simp [residueCubicValue]

/-- On a nonzero residue class this agrees with the established Euler selector. -/
theorem residueCubicValue_mk (P : Ideal E) (a : E) (ha : a ∉ P) :
    residueCubicValue P (Ideal.Quotient.mk P a) = localCubicSymbol P a := by
  classical
  have hqa : Ideal.Quotient.mk P a ≠ 0 := by
    intro h
    exact ha (Ideal.Quotient.eq_zero_iff_mem.mp h)
  simp [residueCubicValue, localCubicSymbol, hqa]

variable (P : Ideal E) [P.IsMaximal] [Finite (E ⧸ P)]
private theorem localSelector_spec
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (a : E) (ha : a ∉ P) :
    (localCubicSymbol P a = 1 ∨
      localCubicSymbol P a = QuadraticAlgebra.omega ∨
      localCubicSymbol P a = QuadraticAlgebra.omega ^ 2) ∧
    Ideal.Quotient.mk P (localCubicSymbol P a) =
      (Ideal.Quotient.mk P a) ^ ((Nat.card (E ⧸ P) - 1) / 3) ∧
    (∀ z : E,
      (z = 1 ∨ z = QuadraticAlgebra.omega ∨ z = QuadraticAlgebra.omega ^ 2) →
      Ideal.Quotient.mk P z =
        (Ideal.Quotient.mk P a) ^ ((Nat.card (E ⧸ P) - 1) / 3) →
      z = localCubicSymbol P a) := by
  have H := cubic_ideal_character_and_factored_multiplicativity
    ({()} : Finset Unit) (fun _ : Unit => P)
    (by intro i hi; infer_instance)
    (by intro i hi; infer_instance)
    (by intro i hi; exact hcard)
    (by intro i hi; exact hthree)
  exact H.1 () (by simp) a ha

private theorem localSelector_mul
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (a b : E) (ha : a ∉ P) (hb : b ∉ P) :
    localCubicSymbol P (a * b) = localCubicSymbol P a * localCubicSymbol P b := by
  have H := cubic_ideal_character_and_factored_multiplicativity
    ({()} : Finset Unit) (fun _ : Unit => P)
    (by intro i hi; infer_instance)
    (by intro i hi; infer_instance)
    (by intro i hi; exact hcard)
    (by intro i hi; exact hthree)
  exact H.2.1 () (by simp) a b ha hb

theorem residueCubicValue_mem_roots
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (x : E ⧸ P) (hx : x ≠ 0) :
    residueCubicValue P x = 1 ∨
      residueCubicValue P x = QuadraticAlgebra.omega ∨
      residueCubicValue P x = QuadraticAlgebra.omega ^ 2 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∉ P := by
    intro ha
    exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  rw [residueCubicValue_mk P a ha]
  exact (localSelector_spec P hcard hthree a ha).1

@[simp] theorem residueCubicValue_one : residueCubicValue P 1 = 1 := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  simp [residueCubicValue]

theorem residueCubicValue_mul
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (x y : E ⧸ P) :
    residueCubicValue P (x * y) = residueCubicValue P x * residueCubicValue P y := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∉ P := by
    intro ha
    exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  have hb : b ∉ P := by
    intro hb
    exact hy (Ideal.Quotient.eq_zero_iff_mem.mpr hb)
  have hab : a * b ∉ P := by
    intro hab
    rcases (show P.IsPrime from inferInstance).mem_or_mem hab with ha' | hb'
    · exact ha ha'
    · exact hb hb'
  calc
    residueCubicValue P (Ideal.Quotient.mk P a * Ideal.Quotient.mk P b) =
        residueCubicValue P (Ideal.Quotient.mk P (a * b)) := by rw [map_mul]
    _ = localCubicSymbol P (a * b) := residueCubicValue_mk P (a * b) hab
    _ = localCubicSymbol P a * localCubicSymbol P b :=
      localSelector_mul P hcard hthree a b ha hb
    _ = residueCubicValue P (Ideal.Quotient.mk P a) *
        residueCubicValue P (Ideal.Quotient.mk P b) := by
      rw [residueCubicValue_mk P a ha, residueCubicValue_mk P b hb]

/-- The genuine zero-extended multiplicative character on the residue field. -/
def cubicResidueMulChar
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) : MulChar (E ⧸ P) E := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  refine {
    toFun := residueCubicValue P
    map_one' := residueCubicValue_one P
    map_mul' := residueCubicValue_mul P hcard hthree
    map_nonunit' := ?_ }
  intro x hx
  have hx0 : x = 0 := by
    by_contra hx0
    exact hx (isUnit_iff_ne_zero.mpr hx0)
  rw [hx0, residueCubicValue_zero]

theorem cubicResidueMulChar_mk
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (a : E) (ha : a ∉ P) :
    cubicResidueMulChar P hcard hthree (Ideal.Quotient.mk P a) =
      localCubicSymbol P a := by
  change residueCubicValue P (Ideal.Quotient.mk P a) = localCubicSymbol P a
  exact residueCubicValue_mk P a ha

/-- The defining Euler criterion holds at every residue class, including zero. -/
theorem cubicResidueMulChar_reduction
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (x : E ⧸ P) :
    Ideal.Quotient.mk P (cubicResidueMulChar P hcard hthree x) =
      x ^ ((Nat.card (E ⧸ P) - 1) / 3) := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  have hq : 1 < Nat.card (E ⧸ P) := Finite.one_lt_card
  have hm : (Nat.card (E ⧸ P) - 1) / 3 ≠ 0 := by omega
  by_cases hx : x = 0
  · subst x
    change Ideal.Quotient.mk P (residueCubicValue P 0) = _
    rw [residueCubicValue_zero, map_zero, zero_pow hm]
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∉ P := by
    intro ha
    exact hx (Ideal.Quotient.eq_zero_iff_mem.mpr ha)
  rw [cubicResidueMulChar_mk P hcard hthree a ha]
  exact (localSelector_spec P hcard hthree a ha).2.1

/-- Its pointwise values on units are cube roots of unity. -/
theorem cubicResidueMulChar_cube
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    cubicResidueMulChar P hcard hthree ^ 3 = 1 := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  have hw : (QuadraticAlgebra.omega : E) ^ 3 = 1 := by
    have hquad : (QuadraticAlgebra.omega : E) ^ 2 + QuadraticAlgebra.omega + 1 = 0 := by
      rw [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add]
      simp
    linear_combination (QuadraticAlgebra.omega - 1) * hquad
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  change residueCubicValue P (u : E ⧸ P) ^ 3 = 1
  rcases residueCubicValue_mem_roots P hcard hthree (u : E ⧸ P) u.ne_zero with
    h | h | h
  · rw [h, one_pow]
  · rw [h, hw]
  · rw [h]
    calc
      ((QuadraticAlgebra.omega : E) ^ 2) ^ 3 = (QuadraticAlgebra.omega ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hw, one_pow]

/-- The Euler character is nontrivial: otherwise every unit would have m-th power one. -/
theorem cubicResidueMulChar_ne_one
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    cubicResidueMulChar P hcard hthree ≠ 1 := by
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  let m := (Nat.card (E ⧸ P) - 1) / 3
  have hq : 1 < Nat.card (E ⧸ P) := Finite.one_lt_card
  have hm : 0 < m := by dsimp [m]; omega
  have hlt : m < Nat.card (E ⧸ P) - 1 := by dsimp [m]; omega
  intro hχ
  have hall : ∀ u : (E ⧸ P)ˣ, u ^ m = 1 := by
    intro u
    apply Units.ext
    change (u : E ⧸ P) ^ m = 1
    have H := cubicResidueMulChar_reduction P hcard hthree (u : E ⧸ P)
    rw [hχ, MulChar.one_apply_coe, map_one] at H
    exact H.symm
  have hdvd : Nat.card (E ⧸ P) - 1 ∣ m := by
    simpa only [Fintype.card_eq_nat_card] using
      (FiniteField.forall_pow_eq_one_iff (E ⧸ P) m).mp hall
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hm hdvd)

/-- Its exact order is three, so the nontrivial cubic Fermat formulas apply. -/
theorem cubicResidueMulChar_orderOf
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    orderOf (cubicResidueMulChar P hcard hthree) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (cubicResidueMulChar_cube P hcard hthree)
    (cubicResidueMulChar_ne_one P hcard hthree)


/-- An elementary finite-field vanishing statement used after reducing the Jacobi sum. -/
theorem sum_cubic_euler_kernel (F : Type*) [Field F] [Fintype F]
    (hq : Fintype.card F % 3 = 1) :
    ∑ x : F, x ^ ((Fintype.card F - 1) / 3) *
      (1 - x) ^ ((Fintype.card F - 1) / 3) = 0 := by
  classical
  let m := (Fintype.card F - 1) / 3
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hm : 0 < m := by dsimp [m]; omega
  have hm3 : m * 3 = Fintype.card F - 1 := by dsimp [m]; omega
  change ∑ x : F, x ^ m * (1 - x) ^ m = 0
  calc
    _ = ∑ x : F, ∑ i ∈ Finset.range (m + 1),
        (m.choose i : F) * (-1 : F) ^ i * x ^ (m + i) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show (1 : F) - x = -x + 1 by ring, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [neg_pow, one_pow, mul_one, pow_add]
      ring
    _ = ∑ i ∈ Finset.range (m + 1),
        (m.choose i : F) * (-1 : F) ^ i * (∑ x : F, x ^ (m + i)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      rw [FiniteField.sum_pow_lt_card_sub_one F (m + i) (by omega), mul_zero]

/-- The Jacobi sum is divisible by the chosen prime, with its direction fixed by Euler reduction. -/
theorem cubicJacobiSum_mem
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    letI : Fintype (E ⧸ P) := Fintype.ofFinite _
    jacobiSum (cubicResidueMulChar P hcard hthree)
      (cubicResidueMulChar P hcard hthree) ∈ P := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simp only [jacobiSum, map_sum, map_mul,
    cubicResidueMulChar_reduction P hcard hthree]
  simpa only [Fintype.card_eq_nat_card] using
    sum_cubic_euler_kernel (E ⧸ P) (by simpa only [Fintype.card_eq_nat_card] using hcard)



/-- Conjugation on the cubic roots is inversion. -/
theorem cubicResidueMulChar_star
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    (cubicResidueMulChar P hcard hthree).ringHomComp (starRingEnd E) =
      (cubicResidueMulChar P hcard hthree)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  apply MulChar.ext
  intro u
  rw [MulChar.mul_apply, MulChar.one_apply_coe, MulChar.ringHomComp_apply]
  change star (residueCubicValue P (u : E ⧸ P)) *
    residueCubicValue P (u : E ⧸ P) = 1
  rcases residueCubicValue_mem_roots P hcard hthree (u : E ⧸ P) u.ne_zero with
    h | h | h
  · rw [h, star_one, one_mul]
  · rw [h]
    apply QuadraticAlgebra.ext <;>
      norm_num [QuadraticAlgebra.omega, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  · rw [h]
    apply QuadraticAlgebra.ext <;>
      norm_num [pow_two, QuadraticAlgebra.omega, QuadraticAlgebra.re_star,
        QuadraticAlgebra.im_star]

/-- The algebraic norm is exactly the residue-field cardinality. -/
theorem cubicJacobiSum_norm
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    letI : Fintype (E ⧸ P) := Fintype.ofFinite _
    QuadraticAlgebra.norm (jacobiSum (cubicResidueMulChar P hcard hthree)
      (cubicResidueMulChar P hcard hthree)) = (Nat.card (E ⧸ P) : ℤ) := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  let χ := cubicResidueMulChar P hcard hthree
  let f := algebraMap E (FractionRing E)
  have hf : Function.Injective f := IsFractionRing.injective E (FractionRing E)
  have hχ : χ ≠ 1 := cubicResidueMulChar_ne_one P hcard hthree
  have hχχ : χ * χ ≠ 1 := by
    intro h
    have hc : χ ^ 3 = 1 := cubicResidueMulChar_cube P hcard hthree
    rw [show χ ^ 3 = (χ * χ) * χ by
      simp only [pow_succ, pow_zero, one_mul], h, one_mul] at hc
    exact hχ hc
  have H := jacobiSum_mul_jacobiSum_inv
    (F := E ⧸ P) (F' := FractionRing E)
    (χ := χ.ringHomComp f) (φ := χ.ringHomComp f)
    (by rw [ringChar.eq_zero]; exact (CharP.ringChar_ne_zero_of_finite (E ⧸ P)).symm)
    ((MulChar.ringHomComp_ne_one_iff hf).mpr hχ)
    ((MulChar.ringHomComp_ne_one_iff hf).mpr hχ)
    (by rw [← MulChar.ringHomComp_mul]; exact
      (MulChar.ringHomComp_ne_one_iff hf).mpr hχχ)
  have hsχ : χ.ringHomComp (starRingEnd E) = χ⁻¹ :=
    cubicResidueMulChar_star P hcard hthree
  have hs : star (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
    simpa only [starRingEnd_apply, hsχ] using
      (jacobiSum_ringHomComp χ χ (starRingEnd E)).symm
  have Hj : jacobiSum χ χ * star (jacobiSum χ χ) = (Fintype.card (E ⧸ P) : E) := by
    apply hf
    simpa only [map_mul, hs, ← jacobiSum_ringHomComp,
      ← MulChar.ringHomComp_inv, map_natCast] using H
  have Hnorm : (algebraMap ℤ E) (QuadraticAlgebra.norm (jacobiSum χ χ)) =
      (Nat.card (E ⧸ P) : E) := by
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star, Hj, Fintype.card_eq_nat_card]
  have Hre := congrArg QuadraticAlgebra.re Hnorm
  simpa using Hre



/-- The sign of the normalized Jacobi sum is fixed modulo three. -/
theorem cubicJacobiSum_primary
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    letI : Fintype (E ⧸ P) := Fintype.ofFinite _
    (3 : E) ∣ -jacobiSum (cubicResidueMulChar P hcard hthree)
      (cubicResidueMulChar P hcard hthree) - 1 := by
  classical
  letI : Field (E ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwne : (QuadraticAlgebra.omega : E) ≠ 1 := by
    intro h
    have hi := congrArg QuadraticAlgebra.im h
    norm_num [QuadraticAlgebra.omega, QuadraticAlgebra.im_one] at hi
  have hprim : IsPrimitiveRoot (QuadraticAlgebra.omega : E) 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime omega_cube hwne)
  obtain ⟨z, hz, H⟩ := exists_jacobiSum_eq_neg_one_add (by decide : 2 < 3)
    (cubicResidueMulChar_cube P hcard hthree)
    (cubicResidueMulChar_cube P hcard hthree)
    (show 3 ∣ Fintype.card (E ⧸ P) - 1 by
      rw [Fintype.card_eq_nat_card]; omega) hprim
  have hw2 : ((QuadraticAlgebra.omega : E) - 1) ^ 2 =
      -3 * QuadraticAlgebra.omega := by
    apply QuadraticAlgebra.ext <;>
      norm_num [pow_two, QuadraticAlgebra.omega, QuadraticAlgebra.re_one,
        QuadraticAlgebra.im_one, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  refine ⟨z * QuadraticAlgebra.omega, ?_⟩
  rw [H, hw2]
  ring

/-- Equal finite indices and the proved inclusion identify the chosen ideal. -/
theorem cubicJacobiSum_span
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P) :
    letI : Fintype (E ⧸ P) := Fintype.ofFinite _
    Ideal.span {-(jacobiSum (cubicResidueMulChar P hcard hthree)
      (cubicResidueMulChar P hcard hthree))} = P := by
  classical
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  let J := -(jacobiSum (cubicResidueMulChar P hcard hthree)
    (cubicResidueMulChar P hcard hthree))
  have hmem : J ∈ P := P.neg_mem (cubicJacobiSum_mem P hcard hthree)
  have hle : Ideal.span {J} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hnorm : QuadraticAlgebra.norm J = (Nat.card (E ⧸ P) : ℤ) := by
    dsimp [J]
    simpa using cubicJacobiSum_norm P hcard hthree
  -- Reuse the established integral cyclotomic bridge to supply Dedekind/PID
  -- structure required by the existing absolute-ideal-norm API.
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : NeZero (3 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  letI : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) :=
    IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  let φ := Classical.choice
    D5.S3.Factorization.QuadraticIdeals.EisensteinCyclotomicBridge.eisenstein_cyclotomic_equiv_exists
  letI : IsPrincipalIdealRing E :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  have hn : Ideal.absNorm (Ideal.span {J}) = Nat.card (E ⧸ P) := by
    rw [Ideal.absNorm_span_singleton]
    have halg : Algebra.norm ℤ J = QuadraticAlgebra.norm J := by
      rw [Algebra.norm_apply]
      exact QuadraticAlgebra.det_toLinearMap_eq_norm J
    rw [halg, hnorm, Int.natAbs_natCast]
  have hidx : (Ideal.span {J}).toAddSubgroup.index = P.toAddSubgroup.index := hn
  letI : (Ideal.span {J}).toAddSubgroup.FiniteIndex :=
    ⟨by rw [← Ideal.absNorm_eq_index, hn]; exact Nat.card_pos.ne'⟩
  apply le_antisymm hle
  by_contra hnot
  have hlt : (Ideal.span {J}).toAddSubgroup < P.toAddSubgroup :=
    lt_of_le_not_ge hle hnot
  have H := AddSubgroup.index_strictAnti hlt
  exact (ne_of_lt H) hidx.symm


/- Reused coordinate proof from the local `hUnitPrimary` in
   `GoldenCubicPrimaryProduct.golden_cubic_primary_product`: a unit congruent
   to one modulo three is one. Kept private here solely for its live consumer. -/
private theorem unit_eq_one_of_primary (u : EisensteinOrder) (hu : IsUnit u)
    (hprimary : (3 : EisensteinOrder) ∣ u - 1) : u = 1 := by
  have hcoords : (3 : ℤ) ∣ u.re - 1 ∧ (3 : ℤ) ∣ u.im := by
    have h := (QuadraticAlgebra.algebraMap_dvd_iff
      (r := (3 : ℤ)) (z := u - 1)).mp hprimary
    simpa only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, sub_zero] using h
  have hnormunit : IsUnit (QuadraticAlgebra.norm u) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
  have hnormnonneg : 0 ≤ QuadraticAlgebra.norm u := by
    simp only [QuadraticAlgebra.norm_def]
    nlinarith [sq_nonneg (2 * u.re - u.im), sq_nonneg u.im]
  have hnorm : QuadraticAlgebra.norm u = 1 := by
    have habs := Int.isUnit_iff_abs_eq.mp hnormunit
    simpa [abs_of_nonneg hnormnonneg] using habs
  have hbSqFour : 3 * u.im ^ 2 ≤ 4 := by
    simp only [QuadraticAlgebra.norm_def] at hnorm
    nlinarith [sq_nonneg (2 * u.re - u.im)]
  have hbSq : u.im ^ 2 ≤ 1 := by omega
  have hbBounds : -1 ≤ u.im ∧ u.im ≤ 1 := by
    constructor <;> nlinarith
  obtain ⟨k, hk⟩ := hcoords.2
  have hb : u.im = 0 := by omega
  have haSq : u.re ^ 2 = 1 := by
    simpa only [QuadraticAlgebra.norm_def, hb, mul_zero, zero_mul,
      sub_zero, add_zero, pow_two] using hnorm
  have haBounds : -1 ≤ u.re ∧ u.re ≤ 1 := by
    constructor <;> nlinarith
  obtain ⟨m, hm⟩ := hcoords.1
  have ha : u.re = 1 := by omega
  apply QuadraticAlgebra.ext
  · simpa only [QuadraticAlgebra.re_one] using ha
  · simpa only [QuadraticAlgebra.im_one] using hb

/-- The primary generator is exactly the negative Jacobi sum. Neither the
norm nor the choice between conjugate ideals is assumed. -/
theorem cubicJacobiSum_eq_primary_generator
    (hcard : Nat.card (E ⧸ P) % 3 = 1) (hthree : (3 : E) ∉ P)
    (π : E) (hπ : Ideal.span {π} = P) (hπprimary : (3 : E) ∣ π - 1) :
    letI : Fintype (E ⧸ P) := Fintype.ofFinite _;
    -(jacobiSum (cubicResidueMulChar P hcard hthree)
      (cubicResidueMulChar P hcard hthree)) = π := by
  classical
  letI : Fintype (E ⧸ P) := Fintype.ofFinite _
  let j := -(jacobiSum (cubicResidueMulChar P hcard hthree)
    (cubicResidueMulChar P hcard hthree))
  have hjspan : Ideal.span {j} = P := cubicJacobiSum_span P hcard hthree
  have hjprimary : (3 : E) ∣ j - 1 := cubicJacobiSum_primary P hcard hthree
  have ha : Associated π j :=
    Ideal.span_singleton_eq_span_singleton.mp (hπ.trans hjspan.symm)
  obtain ⟨u, hu⟩ := ha
  let q := Ideal.Quotient.mk (Ideal.span {(3 : E)})
  have q_primary (z : E) (hz : (3 : E) ∣ z - 1) : q z = 1 := by
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hz)
    change q (z - 1) = 0 at hzero
    rw [map_sub, map_one, sub_eq_zero] at hzero
    exact hzero
  have hqu : q (u : E) = 1 := by
    have h := congrArg q hu
    simpa only [map_mul, q_primary π hπprimary, q_primary j hjprimary, one_mul] using h
  have huprimary : (3 : E) ∣ (u : E) - 1 := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q ((u : E) - 1) = 0
    rw [map_sub, hqu, map_one, sub_self]
  have hu1 : (u : E) = 1 := unit_eq_one_of_primary u u.isUnit huprimary
  have hπj : π = j := by simpa only [hu1, mul_one] using hu
  exact hπj.symm


end D5.S3.Factorization.QuadraticIdeals.CubicJacobiNormalization
