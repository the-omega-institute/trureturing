/-
Uncompiled source candidate. Literal Quotient.out representatives, without
beta(0)=0. This proves the scalar identity only, not a four-input field
pentagon or arbitrary-weak-input representability. All signs are computed
from the original half-diagonal lattice cocycle, not a model associator.
-/
import D5.S3.VertexAlgebra.Sectors.LatticeChargedTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeChargedQuotientScalar
open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeDiscriminantTheta LatticeActualGeneratorLocality
open LatticeChargedTransport
open scoped BigOperators Matrix
noncomputable section

open private class_representative class_gram class_add gramMap_injective
  integral_dot_gram from D5.S3.VertexAlgebra.Characters.LatticeDiscriminantTheta

/-- Second coordinate of the ACTUAL coset equivalence inverse, without search. -/
def carry (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) : Charge D :=
  ((cosetEquiv D hD).symm (representative D c + representative D d)).2

private theorem inverse_class (D : LatticeData) (hD : (gramReal D).PosDef)
    (x : Charge D) : ((cosetEquiv D hD).symm x).1 = classOf D x := by
  have h := congrArg (classOf D) ((cosetEquiv D hD).apply_symm_apply x)
  change classOf D (representative D _ + gramMap D _) = classOf D x at h
  simpa only [class_add, class_representative, class_gram, add_zero] using h

/-- Literal constructive representative equation. -/
theorem carry_equation (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) :
    representative D c + representative D d = representative D (c+d) +
      gramMap D (carry D hD c d) := by
  have h := (cosetEquiv D hD).apply_symm_apply
    (representative D c + representative D d)
  change representative D ((cosetEquiv D hD).symm _).1 +
    gramMap D (carry D hD c d) = _ at h
  rw [inverse_class, class_add, class_representative, class_representative] at h
  exact h.symm

/-- Original positive Gram injectivity supplies uniqueness, including rank zero. -/
theorem carry_unique (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) (n : Charge D)
    (hn : representative D c + representative D d =
      representative D (c+d) + gramMap D n) : n = carry D hD c d := by
  apply gramMap_injective D hD
  exact add_left_cancel (hn.symm.trans (carry_equation D hD c d))

/-- The carry cocycle is proved in the original integral charge group. -/
theorem carry_cocycle (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e : Discriminant D) :
    carry D hD c d + carry D hD (c+d) e =
      carry D hD d e + carry D hD c (d+e) := by
  apply gramMap_injective D hD
  rw [map_add, map_add]
  have h1 := carry_equation D hD c d
  have h2 := carry_equation D hD (c+d) e
  have h3 := carry_equation D hD d e
  have h4 := carry_equation D hD c (d+e)
  rw [add_assoc c d e] at h2
  linear_combination (norm := module) -h1 - h2 + h3 + h4

/-- No new section: the literal zero representative has its own Gram carry. -/
def zeroCarry (D : LatticeData) (hD : (gramReal D).PosDef) : Charge D :=
  carry D hD 0 0

theorem representative_zero (D : LatticeData) (hD : (gramReal D).PosDef) :
    representative D 0 = gramMap D (zeroCarry D hD) := by
  have h := carry_equation D hD 0 0
  rw [zero_add] at h
  exact add_left_cancel h

@[simp] theorem carry_zero_left (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) : carry D hD 0 c = zeroCarry D hD := by
  symm
  apply carry_unique D hD
  rw [zero_add, representative_zero D hD]
  abel

@[simp] theorem carry_zero_right (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) : carry D hD c 0 = zeroCarry D hD := by
  symm
  apply carry_unique D hD
  rw [add_zero, representative_zero D hD]

/-- Literal iterate-to-product scalar, with the source order epsilon(q,s). -/
def associator (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e : Discriminant D) : ℂ :=
  chi D (representative D c) (carry D hD d e) *
    epsilon D (carry D hD d e) (carry D hD c (d+e)) /
      epsilon D (carry D hD c d) (carry D hD (c+d) e)

theorem associator_nonzero (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e : Discriminant D) : associator D hD c d e ≠ 0 :=
  div_ne_zero (mul_ne_zero (chi_nonzero D _ _) (epsilon_nonzero D _ _))
    (epsilon_nonzero D _ _)

/-- Integral exponent of precisely the displayed native scalar. -/
private def associatorExponent (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e : Discriminant D) : ℤ :=
  representative D c ⬝ᵥ carry D hD d e +
    lowerCocycleExponent D (carry D hD d e) (carry D hD c (d+e)) -
      lowerCocycleExponent D (carry D hD c d) (carry D hD (c+d) e)

private theorem sign_neg (k : ℤ) : paritySign (-k) = paritySign k := by
  have h : Even (-k) ↔ Even k := by
    constructor <;> intro hk <;> simpa using hk.neg
  simp only [paritySign, h]

private theorem sign_inv (k : ℤ) : (paritySign k)⁻¹ = paritySign k := by
  unfold paritySign
  split_ifs <;> norm_num

private theorem sign_sub (j k : ℤ) :
    paritySign (j-k) = paritySign j * paritySign k := by
  rw [sub_eq_add_neg, paritySign_add, sign_neg]

private theorem sign_twice (k : ℤ) : paritySign (2*k) = 1 := by
  have h : Even (2*k) := ⟨k, by ring⟩
  simp only [paritySign, h, if_true]

private theorem exponent_add_left (D : LatticeData) (a b c : Charge D) :
    lowerCocycleExponent D (a+b) c =
      lowerCocycleExponent D a c + lowerCocycleExponent D b c := by
  simp [lowerCocycleExponent, add_mul, mul_add, Finset.sum_add_distrib] <;> ring

private theorem exponent_add_right (D : LatticeData) (a b c : Charge D) :
    lowerCocycleExponent D a (b+c) =
      lowerCocycleExponent D a b + lowerCocycleExponent D a c := by
  simp [lowerCocycleExponent, mul_add, Finset.sum_add_distrib] <;> ring

private theorem exponent_sub_left (D : LatticeData) (a b c : Charge D) :
    lowerCocycleExponent D (a-b) c =
      lowerCocycleExponent D a c - lowerCocycleExponent D b c := by
  simp [lowerCocycleExponent, sub_mul, mul_sub, Finset.sum_sub_distrib] <;> ring

private theorem exponent_sub_right (D : LatticeData) (a b c : Charge D) :
    lowerCocycleExponent D a (b-c) =
      lowerCocycleExponent D a b - lowerCocycleExponent D a c := by
  simp [lowerCocycleExponent, mul_sub, Finset.sum_sub_distrib] <;> ring

private theorem dot_sub_left (D : LatticeData) (a b c : Charge D) :
    (a-b) ⬝ᵥ c = a ⬝ᵥ c - b ⬝ᵥ c := by
  simp [dotProduct, sub_mul, Finset.sum_sub_distrib]

private theorem dot_sub_right (D : LatticeData) (a b c : Charge D) :
    a ⬝ᵥ (b-c) = a ⬝ᵥ b - a ⬝ᵥ c := by
  simp [dotProduct, mul_sub, Finset.sum_sub_distrib]

/-- The cross character and cocycle commutator use the SAME original Gram. -/
private theorem gram_dot_exponent (D : LatticeData) (p r : Charge D) :
    gramMap D p ⬝ᵥ r = lowerCocycleExponent D r p + lowerCocycleExponent D p r := by
  rw [dotProduct_comm, integral_dot_gram,
    LatticeTwistedGroundRealization.SignQuotient.integral_cocycle_symmetrization]

private theorem associator_eq_sign (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e : Discriminant D) :
    associator D hD c d e = paritySign (associatorExponent D hD c d e) := by
  unfold associator associatorExponent chi epsilon
  rw [sign_sub, paritySign_add, div_eq_mul_inv, sign_inv]

/-- A coefficient-free integer computation: the pentagon defect is 2*kappa(r,p).
The non-symmetric epsilon order is visible in this exact defect. -/
private theorem pentagon_exponent (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e f : Discriminant D) :
    associatorExponent D hD c d e + associatorExponent D hD c (d+e) f +
      associatorExponent D hD d e f =
    associatorExponent D hD (c+d) e f + associatorExponent D hD c d (e+f) +
      2 * lowerCocycleExponent D (carry D hD e f) (carry D hD c d) := by
  have ht : carry D hD c (d+e) =
      carry D hD c d + carry D hD (c+d) e - carry D hD d e := by
    have h := carry_cocycle D hD c d e
    linear_combination (norm := module) -h
  have hu : carry D hD (d+e) f =
      carry D hD e f + carry D hD d (e+f) - carry D hD d e := by
    have h := carry_cocycle D hD d e f
    linear_combination (norm := module) h
  have hw : carry D hD ((c+d)+e) f =
      carry D hD e f + carry D hD (c+d) (e+f) - carry D hD (c+d) e := by
    have h := carry_cocycle D hD (c+d) e f
    linear_combination (norm := module) h
  have hy : carry D hD c (d+(e+f)) =
      carry D hD c d + carry D hD (c+d) (e+f) - carry D hD d (e+f) := by
    have h := carry_cocycle D hD c d (e+f)
    linear_combination (norm := module) -h
  have hb : representative D (c+d) = representative D c + representative D d -
      gramMap D (carry D hD c d) := by
    have h := carry_equation D hD c d
    linear_combination (norm := module) -h
  unfold associatorExponent
  simp only [← add_assoc c d e, add_assoc d e f, ht, hu, hw, hy, hb,
    exponent_add_left, exponent_add_right, exponent_sub_left, exponent_sub_right,
    add_dotProduct, dot_sub_left,
    dotProduct_add, dot_sub_right, gram_dot_exponent]
  ring

/-- Full scalar pentagon for the literal section and the native half-diagonal
cocycle. This statement does not assert any four-field common witness. -/
theorem scalar_pentagon (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e f : Discriminant D) :
    associator D hD c d e * associator D hD c (d+e) f * associator D hD d e f =
      associator D hD (c+d) e f * associator D hD c d (e+f) := by
  simp only [associator_eq_sign, ← paritySign_add]
  rw [pentagon_exponent, paritySign_add, sign_twice, mul_one]

/-- The literal unit character; no change to the prescribed pair field. -/
def unitCharacter (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) : ℂ := chi D (representative D c) (zeroCarry D hD)

theorem unitCharacter_nonzero (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) : unitCharacter D hD c ≠ 0 := chi_nonzero D _ _

@[simp] theorem unitCharacter_zero (D : LatticeData) (hD : (gramReal D).PosDef) :
    unitCharacter D hD 0 = 1 := by
  unfold unitCharacter chi
  rw [representative_zero D hD, gram_dot_exponent]
  rw [show lowerCocycleExponent D (zeroCarry D hD) (zeroCarry D hD) +
      lowerCocycleExponent D (zeroCarry D hD) (zeroCarry D hD) =
        2 * lowerCocycleExponent D (zeroCarry D hD) (zeroCarry D hD) by ring,
    sign_twice]

@[simp] theorem associator_zero_left (D : LatticeData) (hD : (gramReal D).PosDef)
    (d e : Discriminant D) : associator D hD 0 d e = 1 := by
  rw [associator_eq_sign]
  simp only [associatorExponent, zero_add, carry_zero_left, representative_zero D hD,
    gram_dot_exponent]
  rw [show (lowerCocycleExponent D (carry D hD d e) (zeroCarry D hD) +
      lowerCocycleExponent D (zeroCarry D hD) (carry D hD d e)) +
      lowerCocycleExponent D (carry D hD d e) (zeroCarry D hD) -
      lowerCocycleExponent D (zeroCarry D hD) (carry D hD d e) =
        2 * lowerCocycleExponent D (carry D hD d e) (zeroCarry D hD) by ring,
    sign_twice]

@[simp] theorem associator_zero_middle (D : LatticeData) (hD : (gramReal D).PosDef)
    (c e : Discriminant D) : associator D hD c 0 e = unitCharacter D hD c := by
  unfold associator unitCharacter
  simp only [zero_add, add_zero, carry_zero_left, carry_zero_right]
  exact (div_eq_iff (epsilon_nonzero D _ _)).mpr rfl

@[simp] theorem associator_zero_right (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) :
    associator D hD c d 0 = unitCharacter D hD d / unitCharacter D hD (c+d) := by
  rw [associator_eq_sign]
  have hb : representative D (c+d) = representative D c + representative D d -
      gramMap D (carry D hD c d) := by
    have h := carry_equation D hD c d
    linear_combination (norm := module) -h
  have he : associatorExponent D hD c d 0 =
      (representative D d ⬝ᵥ zeroCarry D hD -
        representative D (c+d) ⬝ᵥ zeroCarry D hD) +
      2 * (representative D c ⬝ᵥ zeroCarry D hD -
        lowerCocycleExponent D (carry D hD c d) (zeroCarry D hD)) := by
    simp only [associatorExponent, carry_zero_right, add_zero, hb,
      dot_sub_left, add_dotProduct, gram_dot_exponent]
    ring
  rw [he, paritySign_add, sign_twice, mul_one, sign_sub]
  simp only [unitCharacter, chi, div_eq_mul_inv, sign_inv]

private theorem unitCharacter_square (D : LatticeData) (hD : (gramReal D).PosDef)
    (c : Discriminant D) : unitCharacter D hD c * unitCharacter D hD c = 1 :=
  paritySign_square _

/-- OPTIONAL rescaled convention, kept separate from literal associator/J.
It corresponds to J^u(c,d)=unitCharacter(c)^(-1) smul J(c,d). -/
def unitAssociator (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d e : Discriminant D) : ℂ :=
  associator D hD c d e * unitCharacter D hD (c+d) / unitCharacter D hD d

/-- Only the explicitly rescaled convention has all three literal unit values one. -/
theorem unitAssociator_units (D : LatticeData) (hD : (gramReal D).PosDef)
    (c d : Discriminant D) :
    unitAssociator D hD 0 c d = 1 ∧ unitAssociator D hD c 0 d = 1 ∧
      unitAssociator D hD c d 0 = 1 := by
  simp [unitAssociator, unitCharacter_nonzero, unitCharacter_square]

end
end D5.S3.VertexAlgebra.LatticeChargedQuotientScalar
