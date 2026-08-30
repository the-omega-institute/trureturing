/- GID: D5/S3/Arith/Lattices/GoldenIntegerRing
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/GoldenIntegerRing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The coordinate golden ring is the integer ring of the golden number field. -/

import D5.S0.Carrier.Euclidean
import D5.S3.Arith.GoldenPrimeSplitting
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.Int.Lemmas
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.KrullDimension.Basic

namespace D5.S3.Arith.Lattices.GoldenIntegerRing

open D5.S0.Carrier
open Module
open scoped NumberField QuadraticAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

private instance goldenPolynomialNoRationalRoot :
    Fact (forall r : Rat, r ^ 2 ≠ (1 : Rat) + 1 * r) := by
  refine ⟨fun r hr => ?_⟩
  have hsq : (5 : Rat) = (2 * r - 1) ^ 2 := by
    nlinarith
  have hfive : IsSquare (5 : Rat) := ⟨2 * r - 1, by nlinarith⟩
  have hfiveNat : IsSquare (5 : Nat) := Rat.isSquare_natCast_iff.mp hfive
  have hprime : Nat.Prime 5 := by decide
  exact hprime.not_isSquare hfiveNat

/-- The golden number field, presented by `omega^2 = omega + 1`. -/
abbrev GoldenNumberField := QuadraticAlgebra Rat 1 1

noncomputable instance goldenNumberField : NumberField GoldenNumberField where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

/-- The ordered rational basis `(1, omega)` of the golden number field. -/
noncomputable def goldenFieldBasis : Basis (Fin 2) Rat GoldenNumberField :=
  QuadraticAlgebra.basis 1 1

@[simp] private theorem goldenFieldBasis_zero :
    goldenFieldBasis 0 = (1 : GoldenNumberField) := by
  apply goldenFieldBasis.repr.injective
  ext i
  fin_cases i <;>
    simp [goldenFieldBasis, QuadraticAlgebra.basis_repr_apply]

@[simp] private theorem goldenFieldBasis_one :
    goldenFieldBasis 1 = (QuadraticAlgebra.omega : GoldenNumberField) := by
  apply goldenFieldBasis.repr.injective
  ext i
  fin_cases i <;>
    simp [goldenFieldBasis, QuadraticAlgebra.basis_repr_apply]

private theorem golden_field_trace (z : GoldenNumberField) :
    Algebra.trace Rat GoldenNumberField z = 2 * z.re + z.im := by
  rw [Algebra.trace_eq_matrix_trace goldenFieldBasis, Matrix.trace_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, goldenFieldBasis_zero,
    goldenFieldBasis_one, mul_one]
  simp [goldenFieldBasis, QuadraticAlgebra.basis_repr_apply]
  ring_nf

private theorem golden_field_basis_discr :
    Algebra.discr Rat goldenFieldBasis = 5 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  norm_num [Algebra.traceMatrix_apply, Algebra.traceForm_apply, golden_field_trace]

private theorem golden_omega_isIntegral :
    IsIntegral Int (QuadraticAlgebra.omega : GoldenNumberField) := by
  let p : Polynomial Int :=
    (Polynomial.X ^ 2 - Polynomial.C 1) - Polynomial.X
  have hp : p.Monic := by
    apply (Polynomial.monic_X_pow_sub_C (1 : Int) (by norm_num : 2 ≠ 0)).sub_of_left
    rw [Polynomial.degree_X, Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 2)]
    norm_num
  refine ⟨p, hp, ?_⟩
  simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_one, Polynomial.eval₂_X, map_one]
  rw [pow_two]
  rw [QuadraticAlgebra.omega_mul_omega_eq_add]
  norm_num

private theorem golden_field_basis_isIntegral (i : Fin 2) :
    IsIntegral Int (goldenFieldBasis i) := by
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · simpa using (isIntegral_one : IsIntegral Int (1 : GoldenNumberField))
  · simpa using golden_omega_isIntegral

private noncomputable def goldenFieldBasisOnIntegralIndex :
    Basis (Module.Free.ChooseBasisIndex Int (𝓞 GoldenNumberField)) Rat
      GoldenNumberField :=
  goldenFieldBasis.reindex
    (goldenFieldBasis.indexEquiv (NumberField.integralBasis GoldenNumberField))

private theorem golden_change_entry_isIntegral
    (i j : Module.Free.ChooseBasisIndex Int (𝓞 GoldenNumberField)) :
    IsIntegral Int
      ((NumberField.integralBasis GoldenNumberField).toMatrix
        goldenFieldBasisOnIntegralIndex i j) := by
  rw [Basis.toMatrix_apply]
  have hx : IsIntegral Int (goldenFieldBasisOnIntegralIndex j) := by
    simpa [goldenFieldBasisOnIntegralIndex, Basis.reindex_apply] using
      golden_field_basis_isIntegral
        ((goldenFieldBasis.indexEquiv
          (NumberField.integralBasis GoldenNumberField)).symm j)
  let x : 𝓞 GoldenNumberField := ⟨goldenFieldBasisOnIntegralIndex j, hx⟩
  change IsIntegral Int
    ((NumberField.integralBasis GoldenNumberField).repr
      (algebraMap (𝓞 GoldenNumberField) GoldenNumberField x) i)
  rw [NumberField.integralBasis_repr_apply]
  exact isIntegral_algebraMap

theorem golden_numberField_discr : NumberField.discr GoldenNumberField = 5 := by
  let P := (NumberField.integralBasis GoldenNumberField).toMatrix
    goldenFieldBasisOnIntegralIndex
  have hP : forall i j, IsIntegral Int (P i j) := golden_change_entry_isIntegral
  have hdet : IsIntegral Int P.det := IsIntegral.det hP
  obtain ⟨d, hd⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  have hchange :
      Algebra.discr Rat goldenFieldBasisOnIntegralIndex =
        P.det ^ 2 * Algebra.discr Rat (NumberField.integralBasis GoldenNumberField) := by
    rw [← Algebra.discr_of_matrix_vecMul
      (NumberField.integralBasis GoldenNumberField) P]
    congr 1
    exact ((NumberField.integralBasis GoldenNumberField).toMatrix_map_vecMul
      goldenFieldBasisOnIntegralIndex).symm
  have hreindex :
      Algebra.discr Rat goldenFieldBasisOnIntegralIndex =
        Algebra.discr Rat goldenFieldBasis := by
    simpa [goldenFieldBasisOnIntegralIndex, Basis.coe_reindex] using
      Algebra.discr_reindex goldenFieldBasis
        (goldenFieldBasis.indexEquiv (NumberField.integralBasis GoldenNumberField))
  have hrat :
      (5 : Rat) = (d : Rat) ^ 2 * (NumberField.discr GoldenNumberField : Rat) := by
    rw [← golden_field_basis_discr, ← hreindex, hchange, ← hd,
      NumberField.coe_discr]
    norm_num
  have hint : (5 : Int) = d ^ 2 * NumberField.discr GoldenNumberField := by
    exact_mod_cast hrat
  have hdvd : d ^ 2 ∣ (5 : Int) := ⟨NumberField.discr GoldenNumberField, hint⟩
  have habs := Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num : (5 : Int) ≠ 0)
  have hfourth : (d ^ 2) * (d ^ 2) ≤ (5 : Int) * 5 :=
    Int.natAbs_le_iff_mul_self_le.mp habs
  have hsq : d ^ 2 ≤ (5 : Int) := by
    nlinarith [sq_nonneg d]
  have hdle : d ≤ 2 := by
    by_contra h
    have : 3 ≤ d := by omega
    nlinarith
  have hdge : -2 ≤ d := by
    by_contra h
    have : d ≤ -3 := by omega
    nlinarith
  interval_cases d <;> omega

/-- The coordinate embedding sends `phi` to the quadratic generator `omega`. -/
def goldenIntegerEmbedding : GoldenInt →+* GoldenNumberField where
  toFun x := ⟨(x.a : Rat), (x.b : Rat)⟩
  map_zero' := by ext <;> norm_num
  map_one' := by ext <;> norm_num
  map_add' x y := by ext <;> norm_num
  map_mul' x y := by ext <;> norm_num <;> push_cast <;> ring

private theorem goldenIntegerEmbedding_injective :
    Function.Injective goldenIntegerEmbedding := by
  intro x y hxy
  apply GoldenInt.ext
  · have ha := congrArg QuadraticAlgebra.re hxy
    change (x.a : Rat) = (y.a : Rat) at ha
    exact_mod_cast ha
  · have hb := congrArg QuadraticAlgebra.im hxy
    change (x.b : Rat) = (y.b : Rat) at hb
    exact_mod_cast hb

noncomputable instance goldenIntAlgebra : Algebra GoldenInt GoldenNumberField :=
  goldenIntegerEmbedding.toAlgebra

private instance goldenIntScalarTower :
    IsScalarTower Int GoldenInt GoldenNumberField :=
  IsScalarTower.of_algebraMap_eq fun z => by ext <;> norm_num

private theorem golden_phi_isIntegral : IsIntegral Int phi := by
  let p : Polynomial Int := (Polynomial.X ^ 2 - Polynomial.C 1) - Polynomial.X
  have hp : p.Monic := by
    apply (Polynomial.monic_X_pow_sub_C (1 : Int) (by norm_num : 2 ≠ 0)).sub_of_left
    rw [Polynomial.degree_X, Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 2)]
    norm_num
  refine ⟨p, hp, ?_⟩
  simp [p, phi_sq]

private instance goldenInt_isIntegral : Algebra.IsIntegral Int GoldenInt :=
  ⟨fun x => by
    have hx : x = (x.a : GoldenInt) + (x.b : GoldenInt) * phi := by
      apply GoldenInt.ext <;> simp [phi]
    rw [hx]
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul golden_phi_isIntegral)⟩

noncomputable instance goldenNumberFieldIsFractionRing :
    IsFractionRing GoldenInt GoldenNumberField where
  map_units := by
    rintro ⟨x, hx⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hx
    exact isUnit_iff_ne_zero.mpr (goldenIntegerEmbedding_injective.ne hx)
  surj := by
    intro z
    let d : Nat := z.re.den * z.im.den
    let n : GoldenInt :=
      ⟨z.re.num * z.im.den, z.im.num * z.re.den⟩
    refine ⟨⟨n, ⟨(d : GoldenInt), ?_⟩⟩, ?_⟩
    · rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hd
      have ha := congrArg GoldenInt.a hd
      simp [d] at ha
    · change z * goldenIntegerEmbedding (d : GoldenInt) = goldenIntegerEmbedding n
      apply QuadraticAlgebra.ext
      · change z.re * ((d : GoldenInt).a : Rat) +
          1 * z.im * ((d : GoldenInt).b : Rat) = (n.a : Rat)
        simp only [a_natCast, b_natCast, mul_zero, add_zero]
        simp only [d, n, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
        norm_num
        rw [← mul_assoc, Rat.mul_den_eq_num]
      · change z.re * ((d : GoldenInt).b : Rat) +
          z.im * ((d : GoldenInt).a : Rat) +
          1 * z.im * ((d : GoldenInt).b : Rat) = (n.b : Rat)
        simp only [a_natCast, b_natCast, mul_zero, add_zero, zero_add]
        simp only [d, n, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
        norm_num
        rw [mul_comm (z.re.den : Rat) (z.im.den : Rat),
          ← mul_assoc, Rat.mul_den_eq_num]
  exists_of_eq := by
    intro x y hxy
    refine ⟨1, ?_⟩
    simpa using goldenIntegerEmbedding_injective hxy

/-- The single Lean carrier for the source object `O_K = Z[phi]`. -/
abbrev GoldenIntegerRing := 𝓞 GoldenNumberField

/-- The coordinate golden ring is the actual ring of integers of the golden field. -/
noncomputable def goldenIntegerRingAlgEquiv : GoldenInt ≃ₐ[Int] GoldenIntegerRing :=
  IsIntegralClosure.equiv (A := GoldenInt) Int GoldenNumberField GoldenIntegerRing

noncomputable def goldenIntegerRingEquiv : GoldenInt ≃+* GoldenIntegerRing :=
  goldenIntegerRingAlgEquiv.toRingEquiv

/-- The golden generator in the actual ring of integers. -/
noncomputable def goldenPhiInteger : GoldenIntegerRing :=
  goldenIntegerRingAlgEquiv.toRingEquiv phi

private def sqrtFiveCoordinateOrder : Subring GoldenInt where
  carrier := {x | ∃ k : Int, x.b = 2 * k}
  zero_mem' := ⟨0, by simp⟩
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨kx, hkx⟩ ⟨ky, hky⟩
    refine ⟨kx + ky, ?_⟩
    simp only [b_add, hkx, hky]
    ring
  neg_mem' := by
    rintro x ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    simp only [b_neg, hk]
    ring
  mul_mem' := by
    rintro x y ⟨kx, hkx⟩ ⟨ky, hky⟩
    refine ⟨x.a * ky + kx * y.a + 2 * kx * ky, ?_⟩
    simp only [b_mul, hkx, hky]
    ring

/-- The nonmaximal order `Z[sqrt 5]` inside the actual ring of integers. -/
noncomputable def sqrtFiveOrder : Subring GoldenIntegerRing :=
  sqrtFiveCoordinateOrder.map goldenIntegerRingAlgEquiv.toRingEquiv

/-- The rational prime ideal `(2)`. -/
def goldenTwoBaseIdeal : Ideal Int := Ideal.span {(2 : Int)}

private instance goldenTwoBaseIdeal_isMaximal : goldenTwoBaseIdeal.IsMaximal := by
  change (Ideal.span {(2 : Int)}).IsMaximal
  exact Int.ideal_span_isMaximal_of_prime 2

private def goldenTwoCoordinateIdeal : Ideal GoldenInt := Ideal.span {(2 : GoldenInt)}

private instance goldenTwoCoordinateIdeal_isMaximal :
    goldenTwoCoordinateIdeal.IsMaximal := by
  exact D5.S3.Arith.GoldenPrimeSplitting.golden_prime_two.isMaximal_span_singleton

private instance goldenTwoCoordinateIdeal_liesOver :
    goldenTwoCoordinateIdeal.LiesOver goldenTwoBaseIdeal where
  over := by
    ext z
    simp only [goldenTwoBaseIdeal, goldenTwoCoordinateIdeal, Ideal.mem_span_singleton,
      Ideal.mem_comap]
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨(k : GoldenInt), ?_⟩
      simp
    · rintro ⟨x, hx⟩
      have ha := congrArg GoldenInt.a hx
      refine ⟨x.a, ?_⟩
      change z = 2 * x.a + 0 * x.b at ha
      simpa using ha

/-- The unique concrete ideal `(2)` used to define the 2-adic finite place. -/
noncomputable def goldenTwoPrimeIdeal : Ideal GoldenIntegerRing :=
  goldenTwoCoordinateIdeal.map goldenIntegerRingAlgEquiv.toRingEquiv

private theorem goldenTwoPrimeIdeal_isMaximal : goldenTwoPrimeIdeal.IsMaximal :=
  by
    unfold goldenTwoPrimeIdeal
    infer_instance

private instance goldenTwoPrimeIdeal_liesOver :
    goldenTwoPrimeIdeal.LiesOver goldenTwoBaseIdeal :=
  by
    unfold goldenTwoPrimeIdeal
    exact Ideal.LiesOver.of_eq_map_equiv goldenTwoBaseIdeal
      goldenIntegerRingAlgEquiv rfl

private theorem goldenTwoPrimeIdeal_ne_bot : goldenTwoPrimeIdeal ≠ ⊥ := by
  letI : goldenTwoPrimeIdeal.IsMaximal := goldenTwoPrimeIdeal_isMaximal
  exact Ideal.IsMaximal.ne_bot_of_isIntegral_int goldenTwoPrimeIdeal

/-- The finite place of the golden field cut out by the parity prime `(2)`. -/
noncomputable def goldenTwoFinitePlace :
    IsDedekindDomain.HeightOneSpectrum GoldenIntegerRing where
  asIdeal := goldenTwoPrimeIdeal
  isPrime := goldenTwoPrimeIdeal_isMaximal.isPrime
  ne_bot := goldenTwoPrimeIdeal_ne_bot

/-- The conductor of `Z[sqrt 5]` in `O_K`. -/
noncomputable def sqrtFiveOrderConductor : Ideal GoldenIntegerRing where
  carrier := {x | forall y : GoldenIntegerRing, x * y ∈ sqrtFiveOrder}
  zero_mem' := by simp [sqrtFiveOrder]
  add_mem' := by
    intro x y hx hy z
    rw [add_mul]
    exact sqrtFiveOrder.add_mem (hx z) (hy z)
  smul_mem' := by
    intro r x hx y
    simpa only [smul_eq_mul, mul_assoc, mul_left_comm] using hx (r * y)

/-- The parity conductor is exactly the ideal defining the finite place above `2`. -/
theorem sqrtFiveOrderConductor_eq_goldenTwoPrimeIdeal :
    sqrtFiveOrderConductor = goldenTwoPrimeIdeal := by
  ext x
  let c : GoldenInt := goldenIntegerRingAlgEquiv.toRingEquiv.symm x
  constructor
  · intro hx
    have hOne := hx (1 : GoldenIntegerRing)
    have hPhi := hx goldenPhiInteger
    rw [sqrtFiveOrder, Subring.mem_map_equiv] at hOne hPhi
    have hOne' : c ∈ sqrtFiveCoordinateOrder := by
      simpa only [c, map_one, mul_one] using hOne
    have hPhi' : c * phi ∈ sqrtFiveCoordinateOrder := by
      simpa [c, goldenPhiInteger] using hPhi
    change ∃ k : Int, c.b = 2 * k at hOne'
    change ∃ k : Int, (c * phi).b = 2 * k at hPhi'
    rcases hOne' with ⟨kb, hkb⟩
    rcases hPhi' with ⟨ks, hks⟩
    have ha : ∃ ka : Int, c.a = 2 * ka := by
      refine ⟨ks - kb, ?_⟩
      simp only [b_mul, phi_a, phi_b] at hks
      omega
    rcases ha with ⟨ka, hka⟩
    have hcMem : c ∈ goldenTwoCoordinateIdeal := by
      rw [goldenTwoCoordinateIdeal, Ideal.mem_span_singleton]
      refine ⟨⟨ka, kb⟩, ?_⟩
      change c = (2 : GoldenInt) * ⟨ka, kb⟩
      rw [show (2 : GoldenInt) = ⟨2, 0⟩ by rfl]
      apply GoldenInt.ext
      · change c.a = 2 * ka + 0 * kb
        omega
      · change c.b = 2 * kb + 0 * ka + 0 * kb
        omega
    have hmap := Ideal.mem_map_of_mem
      (goldenIntegerRingAlgEquiv.toRingEquiv : GoldenInt →+* GoldenIntegerRing) hcMem
    have hc_image : goldenIntegerRingAlgEquiv.toRingEquiv c = x := by
      exact goldenIntegerRingAlgEquiv.toRingEquiv.apply_symm_apply x
    rw [← hc_image, goldenTwoPrimeIdeal]
    exact hmap
  · intro hx y
    rw [goldenTwoPrimeIdeal,
      ← Ideal.symm_apply_mem_of_equiv_iff
        (f := goldenIntegerRingAlgEquiv.toRingEquiv),
      goldenTwoCoordinateIdeal, Ideal.mem_span_singleton] at hx
    rcases hx with ⟨q, hq⟩
    rw [sqrtFiveOrder, Subring.mem_map_equiv]
    refine ⟨q.b * (goldenIntegerRingAlgEquiv.toRingEquiv.symm y).a +
      q.a * (goldenIntegerRingAlgEquiv.toRingEquiv.symm y).b +
      q.b * (goldenIntegerRingAlgEquiv.toRingEquiv.symm y).b, ?_⟩
    change (goldenIntegerRingAlgEquiv.toRingEquiv.symm (x * y)).b = _
    rw [map_mul]
    have hc : c = (2 : GoldenInt) * q := hq
    change (c * goldenIntegerRingAlgEquiv.toRingEquiv.symm y).b = _
    rw [show (2 : GoldenInt) = ⟨2, 0⟩ by rfl] at hc
    rw [hc]
    simp only [b_mul, a_mul]
    ring

end D5.S3.Arith.Lattices.GoldenIntegerRing
