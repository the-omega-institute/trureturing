/- GID: D5/S3/Arith/CyclotomicFields/MercaQuadraticSubfield
   generality: G
   mirror-B: D5/B/S3/Arith/CyclotomicFields/MercaQuadraticSubfield
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quadratic Gauss root identifies the actual Merca real subfield. -/

import D5.S3.Arith.CyclotomicFields.MercaQuarticField
import D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal
import Mathlib.NumberTheory.GaussSum
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
The actual quadratic Gauss sum in the prime cyclotomic field is fixed by the
normalized quartic kernel and generates its maximal real subfield. This realizes
the Q(sqrt(r)) identification in the historical Ma--Zhang theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Cyclotomic

namespace D5.S3.Arith.CyclotomicFields.MercaQuadraticSubfield

open NumberField IsCyclotomicExtension
open D5.S3.ArithUnits.MercaQuarticCharacter
open MercaQuarticField

variable (r : ℕ) [Fact r.Prime]

private def quadratic : MulChar (ZMod r) (Ambient r) :=
  (quadraticChar (ZMod r)).ringHomComp (Int.castRingHom (Ambient r))

private def additive : AddChar (ZMod r) (Ambient r) :=
  AddChar.zmodChar r (IsCyclotomicExtension.zeta_spec r ℚ (Ambient r)).pow_eq_one

/-- The actual quadratic Gauss sum in the prime cyclotomic number field. -/
def gaussRoot : Ambient r := gaussSum (quadratic r) (additive r)

private lemma gaussRoot_sq (hr : r % 8 = 5) : gaussRoot r ^ 2 = (r : Ambient r) := by
  have hchar : ringChar (ZMod r) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hne : quadratic r ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := Ambient r))).mpr
      (quadraticChar_ne_one hchar)
  have h := gaussSum_sq hne
    ((quadraticChar_isQuadratic (ZMod r)).comp (Int.castRingHom (Ambient r)))
    (AddChar.zmodChar_primitive_of_primitive_root r
      (IsCyclotomicExtension.zeta_spec r ℚ (Ambient r)))
  have hminus : quadraticChar (ZMod r) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card, ZMod.χ₄_nat_one_mod_four (by omega)]
  simpa only [quadratic, MulChar.ringHomComp_apply, hminus, map_one,
    one_mul, ZMod.card, gaussRoot, additive] using h

private lemma quadratic_on_kernel (hr : r % 8 = 5) (u : (ZMod r)ˣ)
    (hu : u ∈ kernel r hr) : quadratic r (u : ZMod r) = 1 := by
  have hp := congrArg (fun v : kernel r hr => ((v : (ZMod r)ˣ) : ZMod r))
    (pow_card_eq_one' (x := (⟨u, hu⟩ : kernel r hr)))
  change (u : ZMod r) ^ Nat.card (kernel r hr) = 1 at hp
  rw [(kernel_structure r hr).2.2.2.2.2.1] at hp
  have hχ := congrArg (quadraticChar (ZMod r)) hp
  rw [map_pow, map_one] at hχ
  rcases quadraticChar_dichotomy (Units.ne_zero u) with h | h
  · simp only [quadratic, MulChar.ringHomComp_apply, h, map_one]
  · have hm : Odd ((r - 1) / 4) := Nat.odd_iff.mpr (by omega)
    rw [h, hm.neg_one_pow] at hχ
    norm_num at hχ

private lemma gaussRoot_fixed (hr : r % 8 = 5)
    (σ : Gal(Ambient r/ℚ)) (hσ : σ ∈ galoisKernel r hr) :
    σ (gaussRoot r) = gaussRoot r := by
  let u := Rat.galEquivZMod r (Ambient r) σ
  have hu : u ∈ kernel r hr := hσ
  have hψ (a : ZMod r) : σ (additive r a) = additive r ((u : ZMod r) * a) := by
    simp only [additive, AddChar.zmodChar_apply, map_pow]
    rw [Rat.galEquivZMod_apply_of_pow_eq r (Ambient r) σ
      (IsCyclotomicExtension.zeta_spec r ℚ (Ambient r)).pow_eq_one]
    rw [← pow_mul, ZMod.val_mul]
    exact pow_eq_pow_mod _
      (IsCyclotomicExtension.zeta_spec r ℚ (Ambient r)).pow_eq_one
  have hmap : σ (gaussRoot r) =
      gaussSum (quadratic r) ((additive r).mulShift (u : ZMod r)) := by
    simp only [gaussRoot, gaussSum, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [hψ]
    simp only [quadratic, MulChar.ringHomComp_apply, AddChar.mulShift_apply]
    congr 1
    exact map_intCast σ _
  have h := gaussSum_mulShift (quadratic r) (additive r) u
  rw [quadratic_on_kernel r hr u hu, one_mul] at h
  exact hmap.trans h

/-- The same Gauss root as an element of the actual quartic fixed field. -/
def quarticGaussRoot (hr : r % 8 = 5) : MercaQuarticField.Field r hr :=
  ⟨gaussRoot r,
    (IntermediateField.mem_fixedField_iff (galoisKernel r hr) _).mpr (gaussRoot_fixed r hr)⟩

private lemma quarticGaussRoot_sq (hr : r % 8 = 5) :
    quarticGaussRoot r hr ^ 2 = (r : MercaQuarticField.Field r hr) := by
  apply Subtype.ext
  exact gaussRoot_sq r hr

private lemma gaussRoot_real (hr : r % 8 = 5) :
    quarticGaussRoot r hr ∈ maximalRealSubfield (MercaQuarticField.Field r hr) := by
  intro φ
  have hs : φ (quarticGaussRoot r hr) ^ 2 = (r : ℂ) := by
    rw [← map_pow, quarticGaussRoot_sq, map_natCast]
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_re, Complex.natCast_re] at hre
  simp only [pow_two, Complex.mul_im, Complex.natCast_im] at him
  have hne : (φ (quarticGaussRoot r hr)).re ≠ 0 := by
    intro h
    have hp : (0 : ℝ) < r := by exact_mod_cast (Fact.out : r.Prime).pos
    rw [h] at hre
    nlinarith [sq_nonneg (φ (quarticGaussRoot r hr)).im]
  have hi : (φ (quarticGaussRoot r hr)).im = 0 := by
    have hmul : (φ (quarticGaussRoot r hr)).re *
        (φ (quarticGaussRoot r hr)).im = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hne
  apply Complex.ext <;> simp [hi]

/-- The actual square-root algebra Q(sqrt(r)); its generator squares to r. -/
abbrev RealQuadratic := QuadraticAlgebra ℚ (r : ℚ) 0

private lemma rat_prime_nonsquare : ¬ IsSquare (r : ℚ) := by
  intro h
  obtain ⟨a, ha⟩ := Rat.isSquare_natCast_iff.mp h
  have hd : a ∣ r := ⟨a, ha⟩
  rcases (Nat.dvd_prime (Fact.out : r.Prime)).mp hd with h | h
  · rw [h] at ha
    have := (Fact.out : r.Prime).two_le
    nlinarith
  · rw [h] at ha
    have := (Fact.out : r.Prime).two_le
    nlinarith

instance real_nonsquare : Fact (¬ IsSquare (QuadraticAlgebra.discr (r : ℚ) 0)) := by
  constructor
  rintro ⟨z, hz⟩
  apply rat_prime_nonsquare r
  refine ⟨z / 2, ?_⟩
  dsimp [QuadraticAlgebra.discr] at hz
  nlinarith

instance real_numberField : NumberField (RealQuadratic r) :=
  NumberField.of_module_finite ℚ _

/-- The Gauss-root embedding of the actual square-root field into the actual maximal real field. -/
def realHom (hr : r % 8 = 5) :
    RealQuadratic r →ₐ[ℚ] maximalRealSubfield (MercaQuarticField.Field r hr) :=
  QuadraticAlgebra.lift ⟨⟨quarticGaussRoot r hr, gaussRoot_real r hr⟩, by
    apply Subtype.ext
    simpa [pow_two] using quarticGaussRoot_sq r hr⟩

/-- The maximal real field is isomorphic to the actual field Q(sqrt(r)), not a supplied scalar. -/
def realEquiv (hr : r % 8 = 5) :
    RealQuadratic r ≃ₐ[ℚ] maximalRealSubfield (MercaQuarticField.Field r hr) := by
  apply AlgEquiv.ofBijective (realHom r hr)
  refine ⟨(realHom r hr).injective, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (realHom r hr).toLinearMap) ?_).mp
    (realHom r hr).injective
  rw [QuadraticAlgebra.finrank_eq_two, (field_structure r hr).2.2.2]

private def orderA : ℤ := ((r - 1) / 4 : ℕ)

private lemma order_discr (hr : r % 8 = 5) :
    QuadraticAlgebra.discr (orderA r) 1 = (r : ℤ) := by
  dsimp [orderA, QuadraticAlgebra.discr]
  omega

private lemma order_rat_discr (hr : r % 8 = 5) :
    QuadraticAlgebra.discr (orderA r : ℚ) (1 : ℚ) = (r : ℚ) := by
  have h := order_discr r hr
  simp only [QuadraticAlgebra.discr, one_pow] at h ⊢
  exact_mod_cast h

private def orderModelEquiv (hr : r % 8 = 5) :
    QuadraticAlgebra ℚ (orderA r : ℚ) (1 : ℚ) ≃ₐ[ℚ] RealQuadratic r := by
  refine (QuadraticAlgebra.algEquivDiscrZero (orderA r : ℚ) (1 : ℚ)).trans ?_
  rw [order_rat_discr r hr]
  exact AlgEquiv.refl

/-- The half-integral order Z[(1+sqrt(r))/2] is the actual maximal integer ring. -/
def realMaximalOrderEquiv (hr : r % 8 = 5) :
    QuadraticAlgebra ℤ (((r - 1) / 4 : ℕ) : ℤ) 1 ≃ₐ[ℤ] 𝓞 (RealQuadratic r) := by
  letI : Fact (¬ IsSquare (QuadraticAlgebra.discr (orderA r : ℚ) (1 : ℚ))) :=
    ⟨by rw [order_rat_discr r hr]; exact rat_prime_nonsquare r⟩
  have hsf : Squarefree (QuadraticAlgebra.discr (orderA r) 1) := by
    rw [order_discr r hr]
    exact (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : r.Prime))).squarefree
  exact (D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.ringOfIntegersEquiv hsf).trans
    ((orderModelEquiv r hr).restrictScalars ℤ).mapIntegralClosure

/-- The actual real quadratic field and the maximal real subfield have discriminant r. -/
theorem real_discriminant (hr : r % 8 = 5) :
    NumberField.discr (RealQuadratic r) = (r : ℤ) ∧
    NumberField.discr (maximalRealSubfield (MercaQuarticField.Field r hr)) = (r : ℤ) := by
  letI : Fact (¬ IsSquare (QuadraticAlgebra.discr (orderA r : ℚ) (1 : ℚ))) :=
    ⟨by rw [order_rat_discr r hr]; exact rat_prime_nonsquare r⟩
  letI : NumberField (QuadraticAlgebra ℚ (orderA r : ℚ) (1 : ℚ)) :=
    NumberField.of_module_finite ℚ _
  have hsf : Squarefree (QuadraticAlgebra.discr (orderA r) 1) := by
    rw [order_discr r hr]
    exact (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : r.Prime))).squarefree
  have hD : NumberField.discr (RealQuadratic r) = (r : ℤ) := by
    rw [← NumberField.discr_eq_discr_of_algEquiv _ (orderModelEquiv r hr)]
    exact (D5.S3.Arith.QuadraticFields.QuadraticOrderMaximal.numberField_discr hsf).trans
      (order_discr r hr)
  exact ⟨hD, (NumberField.discr_eq_discr_of_algEquiv _ (realEquiv r hr)).symm.trans hD⟩

end D5.S3.Arith.CyclotomicFields.MercaQuadraticSubfield
