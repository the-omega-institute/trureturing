/- GID: D5/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/GolayLeech/ExplicitLeechLattice
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An explicit positive even unimodular rootless rank-twenty-four lattice supplies moonshine ground data. -/
import D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechSpan
import D5.S3.VertexAlgebra.GolayLeech.ExplicitGolayDuality
import D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice

open scoped BigOperators Matrix
open ExplicitGolayCode ExplicitLeechCongruence ExplicitLeechBasis ExplicitLeechSpan
open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization

abbrev data : LatticeData where
  rank := 24
  G := gramMatrix
  symmetric := finite_gram_certificate.2.1
  even_diagonal := finite_gram_certificate.2.2

theorem charge_pairing_scaled (left right : Charge data) :
    8 * bilinear data left right =
      ∑ axis, (basisMatrix *ᵥ left) axis * (basisMatrix *ᵥ right) axis := by
  have original_pairing : bilinear data left right = left ⬝ᵥ (gramMatrix *ᵥ right) := by
    simp [bilinear, data, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [original_pairing]
  change _ = (basisMatrix *ᵥ left) ⬝ᵥ (basisMatrix *ᵥ right)
  have contraction : left ⬝ᵥ (basisMatrixᵀ *ᵥ (basisMatrix *ᵥ right)) =
      (basisMatrix *ᵥ left) ⬝ᵥ (basisMatrix *ᵥ right) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [← contraction, Matrix.mulVec_mulVec,
    finite_gram_certificate.1]
  rw [Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]

theorem charge_square_scaled (charge : Charge data) :
    8 * bilinear data charge charge = squareSum (basisMatrix *ᵥ charge) := by
  rw [charge_pairing_scaled]
  simp [squareSum, pow_two]

theorem charge_even (charge : Charge data) : Even (bilinear data charge charge) := by
  have member : member (basisMatrix *ᵥ charge) := range_le_lattice ⟨charge, rfl⟩
  obtain ⟨quotient, equation⟩ := member_even_squareSum _ member
  have scaled := charge_square_scaled charge
  refine ⟨quotient, ?_⟩
  omega

theorem charge_minimum (charge : Charge data) (nonzero : charge ≠ 0) :
    4 ≤ bilinear data charge charge := by
  have member : member (basisMatrix *ᵥ charge) := range_le_lattice ⟨charge, rfl⟩
  have vector_nonzero : basisMatrix *ᵥ charge ≠ 0 := by
    intro zero
    apply nonzero
    apply basis_injective
    simpa using zero
  have lower := member_minimum_squareSum _ member vector_nonzero
  have scaled := charge_square_scaled charge
  omega

def realBasis : Matrix (Fin 24) (Fin 24) ℝ := basisMatrix.map (Int.castRingHom ℝ)
def realGram : Matrix (Fin 24) (Fin 24) ℝ := gramMatrix.map (Int.castRingHom ℝ)

theorem real_basis_determinant : realBasis.det = (2 : ℝ) ^ 36 := by
  change ((Int.castRingHom ℝ).mapMatrix basisMatrix).det = _
  rw [← RingHom.map_det, basis_determinant]
  norm_num

theorem real_gram_certificate : realBasisᵀ * realBasis = (8 : ℝ) • realGram := by
  ext left right
  have entry := congrFun (congrFun finite_gram_certificate.1 left) right
  have cast_entry := congrArg (fun value : ℤ => (value : ℝ)) entry
  simpa [realBasis, realGram, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, Finset.mul_sum] using cast_entry

theorem real_positive : realGram.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext left right
    simp only [Matrix.conjTranspose_apply, realGram, Matrix.map_apply, star_trivial]
    rw [finite_gram_certificate.2.1]
  · intro vector nonzero
    have injective : Function.Injective (Matrix.mulVec realBasis) :=
      Matrix.mulVec_injective_of_det_ne_zero (by rw [real_basis_determinant]; positivity)
    have vector_nonzero : realBasis *ᵥ vector ≠ 0 := by
      intro zero
      apply nonzero
      apply injective
      simpa using zero
    have coordinate_nonzero : ∃ axis, (realBasis *ᵥ vector) axis ≠ 0 := by
      by_contra failure
      apply vector_nonzero
      ext axis
      simpa using not_exists.mp failure axis
    obtain ⟨axis, coordinate⟩ := coordinate_nonzero
    have positive_sum : 0 < ∑ axis, (realBasis *ᵥ vector) axis ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨axis, Finset.mem_univ _, sq_pos_of_ne_zero coordinate⟩
    have scaled : (∑ axis, (realBasis *ᵥ vector) axis ^ 2) =
        8 * (vector ⬝ᵥ (realGram *ᵥ vector)) := by
      calc
        (∑ axis, (realBasis *ᵥ vector) axis ^ 2) =
            (realBasis *ᵥ vector) ⬝ᵥ (realBasis *ᵥ vector) := by
          simp only [dotProduct, pow_two]
        _ = vector ⬝ᵥ (realBasisᵀ *ᵥ (realBasis *ᵥ vector)) := by
          exact (Matrix.dotProduct_transpose_mulVec
            realBasis vector (realBasis *ᵥ vector)).symm
        _ = 8 * (vector ⬝ᵥ (realGram *ᵥ vector)) := by
          rw [Matrix.mulVec_mulVec, real_gram_certificate]
          rw [Matrix.smul_mulVec, dotProduct_smul]
          simp only [smul_eq_mul]
    simp only [star_trivial]
    nlinarith

theorem minimum_attained :
    ∃ charge : Charge data, charge ≠ 0 ∧ bilinear data charge charge = 4 := by
  refine ⟨unitCharge data (1 : Fin 24), ?_, ?_⟩
  · intro zero
    have contradiction := congrFun zero (1 : Fin 24)
    norm_num [unitCharge] at contradiction
  · norm_num [bilinear, unitCharge, data, gramMatrix, Fin.sum_univ_succ]

local instance : (SignQuotient.K data).Normal := SignQuotient.K_normal data

theorem actual_leech_supplier : data.rank = 24 ∧ data.G.det = 1 ∧ realGram.PosDef ∧
    (∀ charge : Charge data, Even (bilinear data charge charge)) ∧
    (∀ charge : Charge data, charge ≠ 0 → 4 ≤ bilinear data charge charge) ∧
    (∀ vector : Coordinates,
      (∃ charge : Charge data, basisMatrix *ᵥ charge = vector) ↔ congruences vector) ∧
    (∃ charge : Charge data, charge ≠ 0 ∧ bilinear data charge charge = 4) ∧
    (∃ (number : ℕ) (representation : Representation ℂ
        (SignQuotient.Extension data ⧸ SignQuotient.K data) (Ground number)),
      number = 12 ∧ Representation.IsIrreducible representation ∧
      Module.finrank ℂ (Ground number) = 4096) := by
  refine ⟨rfl, gram_determinant, real_positive, charge_even, charge_minimum,
    basis_congruence_identity, minimum_attained, ?_⟩
  have unit_determinant : IsUnit data.G.det := by
    change IsUnit gramMatrix.det
    rw [gram_determinant]
    exact isUnit_one
  obtain ⟨number, representation, rank, irreducible, sign, dimension, rank_twenty_four,
    squares, commutation⟩ := actual_twisted_ground_representation data unit_determinant
  have number_twelve : number = 12 := by
    change 24 = number + number at rank
    omega
  refine ⟨number, representation, number_twelve, irreducible, ?_⟩
  simpa using rank_twenty_four rfl

end D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
