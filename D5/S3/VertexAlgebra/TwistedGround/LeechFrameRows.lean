/- GID: D5/S3/VertexAlgebra/TwistedGround/LeechFrameRows
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/LeechFrameRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer Gram rows factor the literal Leech hyperbolic frame calculation. -/

import D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open GolayLeech.ExplicitLeechLattice GolayLeech.ExplicitLeechBasis
open scoped BigOperators

noncomputable section

def literalIntegralVectors : Matrix (Fin 24) (Fin 24) ℤ :=
  ![![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0],
    ![1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0]]

def literalGramRows : Matrix (Fin 24) (Fin 24) ℤ :=
  !![8, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 2, 0, 0, 0, 2, 2, 2, 0, 2, 0, 5;
    12, 8, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 3, 4, 1, 0, 0, 3, 4, 4, 1, 3, 1, 8;
    12, 6, 8, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 4, 1, 1, 0, 4, 4, 3, 1, 3, 0, 8;
    8, 6, 4, 6, 4, 4, 4, 4, 4, 4, 4, 4, 2, 4, 2, 1, 1, 2, 4, 4, 1, 3, 1, 6;
    8, 4, 4, 6, 6, 4, 4, 4, 4, 4, 4, 4, 2, 3, 2, 2, 2, 3, 3, 4, 1, 3, 1, 6;
    20, 12, 10, 12, 10, 12, 10, 10, 10, 10, 10, 10, 6, 8, 2, 2, 2, 5, 7, 8, 2, 6, 1, 14;
    20, 10, 10, 12, 10, 12, 12, 10, 10, 10, 10, 10, 6, 8, 2, 2, 3, 6, 6, 7, 2, 7, 0, 14;
    28, 14, 14, 16, 16, 16, 16, 16, 14, 14, 14, 14, 8, 10, 4, 4, 4, 10, 9, 10, 3, 10, 2, 20;
    24, 14, 12, 12, 14, 14, 14, 14, 14, 12, 12, 12, 8, 10, 4, 4, 4, 10, 8, 9, 4, 9, 4, 18;
    24, 12, 14, 12, 12, 14, 14, 14, 14, 14, 12, 12, 10, 10, 4, 4, 4, 10, 8, 8, 3, 10, 3, 18;
    28, 14, 14, 14, 16, 16, 16, 14, 16, 14, 16, 14, 10, 10, 2, 4, 4, 10, 8, 10, 4, 10, 3, 20;
    24, 14, 12, 14, 12, 14, 12, 12, 14, 12, 14, 14, 10, 10, 2, 4, 4, 8, 10, 10, 4, 9, 4, 18;
    13, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 5, 5, 2, 2, 2, 5, 5, 5, 2, 5, 2, 11;
    10, 5, 6, 5, 5, 6, 5, 5, 6, 6, 6, 6, 6, 4, 1, 2, 2, 4, 4, 4, 2, 4, 2, 8;
    18, 12, 13, 10, 10, 10, 10, 10, 10, 11, 10, 10, 10, 10, 7, 5, 4, 9, 10, 9, 6, 8, 5, 16;
    6, 4, 6, 7, 5, 5, 4, 5, 5, 5, 5, 4, 8, 8, 8, 9, 7, 7, 8, 8, 6, 8, 6, 10;
    10, 6, 6, 6, 5, 6, 6, 5, 6, 5, 5, 5, 4, 6, 2, 2, 2, 4, 4, 4, 2, 4, 1, 8;
    18, 12, 14, 12, 10, 11, 11, 10, 12, 10, 10, 11, 12, 14, 8, 8, 7, 12, 12, 10, 8, 10, 6, 18;
    6, 4, 6, 6, 6, 6, 7, 5, 6, 6, 5, 5, 10, 10, 10, 10, 11, 10, 8, 9, 9, 10, 8, 12;
    18, 12, 14, 12, 10, 10, 10, 11, 11, 10, 11, 12, 12, 12, 8, 8, 6, 12, 14, 10, 8, 10, 7, 18;
    14, 10, 8, 12, 10, 12, 8, 8, 9, 9, 9, 8, 10, 12, 8, 10, 10, 8, 10, 14, 8, 10, 7, 16;
    18, 12, 14, 14, 12, 14, 14, 12, 12, 9, 12, 12, 14, 18, 12, 14, 12, 16, 16, 14, 14, 14, 9, 22;
    26, 18, 20, 18, 18, 16, 16, 18, 16, 18, 17, 17, 20, 20, 18, 16, 14, 20, 22, 20, 16, 19, 16, 30;
    30, 18, 20, 20, 20, 18, 18, 18, 20, 18, 20, 15, 18, 20, 14, 16, 12, 18, 18, 20, 12, 20, 12, 30]

theorem literalGramRows_eq : literalGramRows = literalIntegralVectors * gramMatrix := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [literalGramRows, literalIntegralVectors, gramMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem literal_gram_entry (first second : Fin 24) :
    bilinear data (literalIntegralVectors first) (literalIntegralVectors second) =
      ∑ axis, literalGramRows first axis * literalIntegralVectors second axis := by
  rw [literalGramRows_eq]
  change (∑ axis, ∑ other,
    literalIntegralVectors first axis * gramMatrix axis other *
      literalIntegralVectors second other) = _
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_comm

end

end D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
