/- GID: D5/S1/DifferentialAlgebra/FractionFieldDerivation
   generality: G
   mirror-B: D5/B/S1/DifferentialAlgebra/FractionFieldDerivation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.Derivation.Basic, mathlib/module/Mathlib.Algebra.TrivSqZeroExt.Basic, mathlib/module/Mathlib.RingTheory.Localization.FractionRing]
   utility: none
   digest: A derivation on an integral domain extends to its fraction field. -/

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
The extension is the second coordinate of the homomorphism to dual numbers
obtained from the localization universal property. Its first coordinate is
the identity. Every helper enters the construction or its agreement theorem.

proof_shape: extend_algebraMap: bind-only; consumer: extend_commutes
proof_shape: extend_commutes: bind-only; consumers:
ExponentialDifferentialField.kAmbientDifferential,
ExponentialDifferentialField.hAmbientDifferential
escape_witness: the localization lift of the graph into dual numbers is a
ring homomorphism whose second coordinate satisfies the Leibniz rule.
-/

set_option autoImplicit false

namespace D5.S1.DifferentialAlgebra.FractionFieldDerivation

variable {R : Type*} [CommRing R] [IsDomain R]
variable (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]

private def graph (D : Derivation ℤ R R) : R →+* TrivSqZeroExt F F where
  toFun r := (algebraMap R F r, algebraMap R F (D r))
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact map_add (algebraMap R F) a b
    · change algebraMap R F (D (a + b)) =
        algebraMap R F (D a) + algebraMap R F (D b)
      simp only [map_add]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap R F) a b
    · change algebraMap R F (D (a * b)) =
        algebraMap R F a * algebraMap R F (D b) +
          algebraMap R F (D a) * algebraMap R F b
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_comm]

private theorem graph_units (D : Derivation ℤ R R) (r : nonZeroDivisors R) :
    IsUnit (graph F D r) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit (algebraMap R F (r : R))
  exact IsLocalization.map_units F r

private noncomputable def graphLift (D : Derivation ℤ R R) : F →+* TrivSqZeroExt F F :=
  IsLocalization.lift (graph_units F D)

private theorem graphLift_algebraMap (D : Derivation ℤ R R) (r : R) :
    graphLift F D (algebraMap R F r) = graph F D r :=
  IsLocalization.lift_eq (graph_units F D) r

private theorem graphLift_fst (D : Derivation ℤ R R) (x : F) :
    (graphLift F D x).fst = x := by
  have h : (TrivSqZeroExt.fstHom ℤ F F).toRingHom.comp (graphLift F D) =
      RingHom.id F := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    exact congrArg TrivSqZeroExt.fst (graphLift_algebraMap F D r)
  exact congrArg (fun f : F →+* F => f x) h

/-- Extend an integer-linear derivation from an integral domain to any of
its fraction fields. -/
noncomputable def extend (D : Derivation ℤ R R) : Derivation ℤ F F where
  toLinearMap :=
    ((TrivSqZeroExt.sndHom F F).toAddMonoidHom.comp
      (graphLift F D).toAddMonoidHom).toIntLinearMap
  map_one_eq_zero' := by
    change (graphLift F D 1).snd = 0
    simp
  leibniz' x y := by
    change (graphLift F D (x * y)).snd =
      x * (graphLift F D y).snd + y * (graphLift F D x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, graphLift_fst, graphLift_fst]
    simp only [op_smul_eq_smul, smul_eq_mul]

/-- The extended derivation agrees with the original derivation on every
element of the integral domain. -/
theorem extend_algebraMap (D : Derivation ℤ R R) (r : R) :
    extend F D (algebraMap R F r) = algebraMap R F (D r) := by
  change (graphLift F D (algebraMap R F r)).snd = algebraMap R F (D r)
  rw [graphLift_algebraMap]
  rfl

/-- A derivation in a further field extension commutes with the extended
derivation as soon as it agrees on the original integral domain. -/
theorem extend_commutes (L : Type*) [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] (D : Derivation ℤ R R) (d : Derivation ℤ L L)
    (h : ∀ r : R, d (algebraMap R L r) = algebraMap R L (D r)) (x : F) :
    d (algebraMap F L x) = algebraMap F L (extend F D x) := by
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  have hb : algebraMap R F (b : R) ≠ 0 := (IsLocalization.map_units F b).ne_zero
  have hbL : algebraMap R L (b : R) ≠ 0 := by
    intro hzero
    apply hb
    apply (algebraMap F L).injective
    simpa only [map_zero, IsScalarTower.algebraMap_apply R F L] using hzero
  have hxL := congrArg (algebraMap F L) hx
  simp only [map_mul, ← IsScalarTower.algebraMap_apply R F L] at hxL
  have hd := congrArg d hxL
  rw [Derivation.leibniz, h, h] at hd
  have he := congrArg (extend F D) hx
  rw [Derivation.leibniz, extend_algebraMap, extend_algebraMap] at he
  have heL := congrArg (algebraMap F L) he
  simp only [smul_eq_mul, map_add, map_mul,
    ← IsScalarTower.algebraMap_apply R F L] at heL
  apply mul_left_cancel₀ hbL
  apply add_left_cancel (a := algebraMap F L x * algebraMap R L (D (b : R)))
  exact hd.trans heL.symm

#print axioms extend_algebraMap
#print axioms extend_commutes

end D5.S1.DifferentialAlgebra.FractionFieldDerivation
