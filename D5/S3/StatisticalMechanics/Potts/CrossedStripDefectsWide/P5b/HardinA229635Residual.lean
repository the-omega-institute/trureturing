/- GID: D5/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/CrossedStripDefectsWide/P5b/HardinA229635Residual
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Transport of the signed residual through the width-six transfer. -/

import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer

open scoped BigOperators
open D5.S3.StatisticalMechanics.Potts.StripDefects

namespace D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual

open DefectTransfer (forward forward_eq)

def coefficients : Fin 27 → ℤ :=
  ![54, -1140, 11637, -54252, 33192, 658756, -1921212, -1566516, 12850374,
    -7108644, -35018232, 43506046, 38500440, -85687812, -200796, 75241308,
    -31685592, -25769200, 20878068, 213348, -3655770, 608916, 230904,
    -61761, -2790, 1800, -125]

variable {D : ℕ}

def scalar (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ) (k : ℕ) : ℤ :=
  dotProduct v ((M ^ k).mulVec e)

def residual (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ) (t : ℕ) : ℤ :=
  scalar M v e (30 + t) -
    ∑ j : Fin 27, coefficients j * scalar M v e (29 - j.val + t)

private theorem scalar_shift (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ)
    (k t : ℕ) :
    scalar M v e (k + t) = dotProduct (forward M v k) ((M ^ t).mulVec e) := by
  simp only [scalar, forward_eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← pow_add]

def residualVector (M : Matrix (Fin D) (Fin D) ℤ) (v : Fin D → ℤ) : Fin D → ℤ :=
  forward M v 30 - ∑ j : Fin 27, coefficients j • forward M v (29 - j.val)

theorem residual_as_power (M : Matrix (Fin D) (Fin D) ℤ) (v e : Fin D → ℤ)
    (t : ℕ) :
    residual M v e t =
      dotProduct (residualVector M v) ((M ^ t).mulVec e) := by
  simp only [residual, residualVector, scalar_shift, sub_dotProduct, sum_dotProduct,
    smul_dotProduct, smul_eq_mul]

end D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual
