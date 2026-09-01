/- GID: D5/S3/Arith/Lattices/RamifiedFiveMatrixReduction
   generality: I
   mirror-B: D5/B/S3/Arith/Lattices/RamifiedFiveMatrixReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An integral square root of five becomes square-zero modulo the ramified prime. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import D5.S3.Arith.Lattices.ExactDualLatticeFormula

/- Library-search audit trail (2026-09-01):
   * Repository receipt, atom-neighbor, keyword, and statement-shape searches found no existing
     formalization of the reduction of `J ^ 2 = 5 • 1` modulo five.
   * Pinned Mathlib exact hits `Matrix.map_mul`, `Matrix.det_pow`, `Matrix.det_smul`,
     `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`,
     `Matrix.isNilpotent_trace_of_isNilpotent`, `RingHom.map_det`, and
     `Matrix.isUnit_iff_isUnit_det`; these are applied below.
   * Third-party GitHub searches through the credential broker did not run: the configured
     services returned `HTTP 400 Bad Request: API key is failed` and
     `HTTP 404 Not Found: Service not found`, respectively.
-/

namespace D5.S3.Arith.Lattices.RamifiedFiveMatrixReduction

open Polynomial

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Reduction modulo the ramified prime sends an integral square root of five to a
square-zero matrix.  The multiplicativity step uses the ring homomorphism explicitly. -/
theorem square_zero_mod_five {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℤ) (hJ : J ^ 2 = (5 : ℤ) • (1 : Matrix n n ℤ)) :
    (J.map (Int.castRingHom (ZMod 5))) ^ 2 = 0 := by
  rw [pow_two]
  rw [← Matrix.map_mul]
  have hmul : J * J = (5 : ℤ) • (1 : Matrix n n ℤ) := by
    simpa only [pow_two] using hJ
  rw [hmul]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.ofNat_apply]
    exact ZMod.natCast_self 5
  · simp [Matrix.ofNat_apply, hij]

/-- The full arithmetic contrast at five: the reduction is nilpotent with zero spectral
invariants, while the integral matrix is not nilpotent and becomes a unit over `ℚ`. -/
structure ReductionData {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℤ) : Prop where
  square_zero : (J.map (Int.castRingHom (ZMod 5))) ^ 2 = 0
  isNilpotent_mod_five : IsNilpotent (J.map (Int.castRingHom (ZMod 5)))
  charpoly_mod_five :
    (J.map (Int.castRingHom (ZMod 5))).charpoly = X ^ Fintype.card n
  trace_mod_five : Matrix.trace (J.map (Int.castRingHom (ZMod 5))) = 0
  det_mod_five : (J.map (Int.castRingHom (ZMod 5))).det = 0
  det_square : J.det ^ 2 = (5 : ℤ) ^ Fintype.card n
  not_isNilpotent_integer : ¬ IsNilpotent J
  isUnit_rational : IsUnit (J.map (Int.castRingHom ℚ))

/-- **Ramified-five matrix reduction.** If an integral matrix squares to five times the
identity, then it is nonnilpotent over `ℤ` and invertible over `ℚ`, but its reduction modulo
five is square-zero, hence nilpotent with characteristic polynomial `X ^ n`, trace zero,
and determinant zero. -/
theorem ramified_five_matrix_reduction {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (J : Matrix n n ℤ) (hJ : J ^ 2 = (5 : ℤ) • (1 : Matrix n n ℤ)) :
    ReductionData J := by
  let Jbar : Matrix n n (ZMod 5) := J.map (Int.castRingHom (ZMod 5))
  have hsquare : Jbar ^ 2 = 0 := square_zero_mod_five J hJ
  have hnilpotent : IsNilpotent Jbar := ⟨2, hsquare⟩
  have hcharpoly_nilpotent :
      IsNilpotent (Jbar.charpoly - X ^ Fintype.card n) :=
    Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnilpotent
  have hcharpoly_sub : Jbar.charpoly - X ^ Fintype.card n = 0 :=
    isNilpotent_iff_eq_zero.mp hcharpoly_nilpotent
  have hcharpoly : Jbar.charpoly = X ^ Fintype.card n := sub_eq_zero.mp hcharpoly_sub
  have htrace_nilpotent : IsNilpotent (Matrix.trace Jbar) :=
    Matrix.isNilpotent_trace_of_isNilpotent hnilpotent
  have htrace : Matrix.trace Jbar = 0 := isNilpotent_iff_eq_zero.mp htrace_nilpotent
  have hdet_square_mod_five : Jbar.det ^ 2 = 0 := by
    calc
      Jbar.det ^ 2 = (Jbar ^ 2).det := (Matrix.det_pow Jbar 2).symm
      _ = 0 := by
        rw [hsquare]
        exact Matrix.det_zero (R := ZMod 5) (n := n) (inferInstance : Nonempty n)
  have hdet_mod_five : Jbar.det = 0 := eq_zero_of_pow_eq_zero hdet_square_mod_five
  have hdet_relation : J.det ^ 2 = (5 : ℤ) ^ Fintype.card n := by
    calc
      J.det ^ 2 = (J ^ 2).det := (Matrix.det_pow J 2).symm
      _ = ((5 : ℤ) • (1 : Matrix n n ℤ)).det := congrArg Matrix.det hJ
      _ = (5 : ℤ) ^ Fintype.card n := by rw [Matrix.det_smul]; simp
  have hdet_square_ne : J.det ^ 2 ≠ 0 := by
    rw [hdet_relation]
    exact pow_ne_zero _ (by norm_num)
  have hdet_ne : J.det ≠ 0 := by
    intro hzero
    exact hdet_square_ne (by simp [hzero])
  have hnot_nilpotent : ¬ IsNilpotent J := by
    rintro ⟨k, hk⟩
    have hdet_pow : J.det ^ k = 0 := by
      calc
        J.det ^ k = (J ^ k).det := (Matrix.det_pow J k).symm
        _ = 0 := by
          rw [hk]
          exact Matrix.det_zero (R := ℤ) (n := n) (inferInstance : Nonempty n)
    exact hdet_ne (eq_zero_of_pow_eq_zero hdet_pow)
  have hunit_rational : IsUnit (J.map (Int.castRingHom ℚ)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet_cast :
        (J.map (Int.castRingHom ℚ)).det = (Int.castRingHom ℚ) J.det := by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) J).symm
    rw [hdet_cast]
    exact isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hdet_ne)
  exact
    { square_zero := hsquare
      isNilpotent_mod_five := hnilpotent
      charpoly_mod_five := hcharpoly
      trace_mod_five := htrace
      det_mod_five := hdet_mod_five
      det_square := hdet_relation
      not_isNilpotent_integer := hnot_nilpotent
      isUnit_rational := hunit_rational }

/-- The adjointness relation `Jᵀ G = G J` survives reduction modulo five. -/
theorem gram_compatibility_mod_five {n : Type*} [Fintype n]
    (J G : Matrix n n ℤ) (hJG : J.transpose * G = G * J) :
    (J.map (Int.castRingHom (ZMod 5))).transpose *
        G.map (Int.castRingHom (ZMod 5)) =
      G.map (Int.castRingHom (ZMod 5)) *
        J.map (Int.castRingHom (ZMod 5)) := by
  have hmapped := congrArg (fun M => M.map (Int.castRingHom (ZMod 5))) hJG
  simpa only [Matrix.map_mul, Matrix.transpose_map] using hmapped

/-- The integral Hodge matrix on `Lambda^2 A4` satisfies the ramified-five reduction
package. -/
theorem integral_hodge_matrix_reduction :
    ReductionData ExactDualLatticeFormula.integralHodgeMatrix := by
  apply ramified_five_matrix_reduction
  decide

/-- A nonempty two-dimensional integral witness for the ramified-five contrast. -/
def witnessMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![0, 5; 1, 0]

/-- The two-dimensional witness squares to five times the identity. -/
theorem witness_square :
    witnessMatrix ^ 2 = (5 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  decide

/-- The reduction of the witness is the displayed nonzero square-zero matrix. -/
theorem witness_reduction :
    witnessMatrix.map (Int.castRingHom (ZMod 5)) =
      !![0, 0; 1, 0] := by
  decide

/-- The witness exhibits zero determinant after reduction but determinant `-5`,
nonnilpotence, and rational invertibility before reduction. -/
theorem witness_contrast :
    (witnessMatrix.map (Int.castRingHom (ZMod 5))) ^ 2 = 0 ∧
      (witnessMatrix.map (Int.castRingHom (ZMod 5))).det = 0 ∧
      witnessMatrix.det = -5 ∧
      ¬ IsNilpotent witnessMatrix ∧
      IsUnit (witnessMatrix.map (Int.castRingHom ℚ)) := by
  have hdata := ramified_five_matrix_reduction witnessMatrix witness_square
  exact ⟨hdata.square_zero, hdata.det_mod_five, by decide,
    hdata.not_isNilpotent_integer, hdata.isUnit_rational⟩

#print axioms ramified_five_matrix_reduction
#print axioms integral_hodge_matrix_reduction
#print axioms witness_contrast

end D5.S3.Arith.Lattices.RamifiedFiveMatrixReduction
