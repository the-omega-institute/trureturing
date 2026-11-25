/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/AffineTablePacking
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pack each affine coefficient polynomial before evaluating its spectral exponents. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTableTerms
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.SparseRadixHorner

/-! A coefficient group has consecutive degree indices and a common
spectral index. Only the groups need sorting in the integer identity. -/

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks

open RefinedBMV.DividedDifference.SparseExpansion
open AffineRadixIdentity
open DimThree.PackedCheck (packSigned)
open private termExponents coefficientTerms
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.AffineTableTerms
open private sum_map_flatMap
  from D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.GroupedAffineMasks

private theorem index_degree (sizes : Exponents) (start : ℕ) (u v : AffineRate) (d : ℕ) :
    index sizes (termExponents start u v d) = d + index sizes (termExponents start u v 0) := by
  simp only [index, termExponents, zero_add]
  omega

private theorem packed_eval_term (sizes : Exponents) (b : ℤ) (t : Term) :
    t.eval b (b ^ sizes.p) (b ^ (sizes.p * sizes.x)) (b ^ (sizes.p * sizes.x * sizes.y))
      (b ^ (sizes.p * sizes.x * sizes.y * sizes.u)) = t.coefficient * b ^ index sizes t.exponents := by
  simp only [Term.eval, Int.cast_id, index, pow_add, pow_mul]

private theorem pack_coefficientTerms (sizes : Exponents) (b : ℤ) (start : ℕ)
    (u v : AffineRate) (d : ℕ) (cs : List ℤ) :
    packedEval sizes b (coefficientTerms start u v d cs) =
      packSigned b cs * b ^ (d + index sizes (termExponents start u v 0)) := by
  induction cs generalizing d with
  | nil => simp [coefficientTerms, packedEval, evalTerms, packSigned]
  | cons a as ih =>
    change Term.eval b (b ^ sizes.p) (b ^ (sizes.p * sizes.x))
      (b ^ (sizes.p * sizes.x * sizes.y)) (b ^ (sizes.p * sizes.x * sizes.y * sizes.u))
        ⟨termExponents start u v d, a⟩ +
      packedEval sizes b (coefficientTerms start u v (d + 1) as) = _
    rw [ih, packed_eval_term]
    change a * b ^ index sizes (termExponents start u v d) +
      packSigned b as * b ^ (d + 1 + index sizes (termExponents start u v 0)) =
        (a + b * packSigned b as) * b ^ (d + index sizes (termExponents start u v 0))
    rw [index_degree sizes start u v d]
    rw [show d + 1 + index sizes (termExponents start u v 0) =
      d + index sizes (termExponents start u v 0) + 1 by omega, pow_succ]
    ring

def Certificate.groupedPackedEval (c : Certificate) (start : ℕ) (sizes : Exponents) (bits : ℕ) : ℤ :=
  let b := (2 : ℤ) ^ bits
  packedPowers bits (c.terms.map fun (v, group) =>
    (index sizes (termExponents start group.rateU v 0), packSigned b group.coefficients))

theorem Certificate.groupedPackedEval_eq (c : Certificate) (start : ℕ)
    (sizes : Exponents) (bits : ℕ) :
    c.groupedPackedEval start sizes bits = packedEval sizes ((2 : ℤ) ^ bits) (c.tableTerms start) := by
  let b := (2 : ℤ) ^ bits
  rw [Certificate.groupedPackedEval, packedPowers_eq, packedEval, evalTerms,
    Certificate.tableTerms, sum_map_flatMap]
  simp only [List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨v, group⟩ _
  symm
  simpa only [zero_add, packedEval, evalTerms] using
    pack_coefficientTerms sizes b start group.rateU v 0 group.coefficients

end RefinedBMV.ThreeBlockGram.PositiveSpectrum.GroupedAffineMasks
