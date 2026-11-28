/- GID: D5/S3/VertexAlgebra/SignedFields/SignedFieldResidueReflection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SignedFields/SignedFieldResidueReflection
   mirror-E: none(waiver:algebraic-signed-field-calculus)
   anchors: []
   utility: none
   digest: Paired reflection of all-integer residues under mode anti-transposition. -/

import D5.S3.VertexAlgebra.SignedFields.SignedFieldResidueLocality
import Mathlib.LinearAlgebra.BilinearMap

/-! Reflection of signed residues under a bilinear pairing of anti-transposed fields. -/

set_option autoImplicit false
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SignedFieldResidueReflection

open SignedFieldResidueLocality (residueField residueCoefficient residueLeft residueRight)
open StateFieldResidueReconstruction (epsilon)

universe uV uW

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Mode anti-transposition exchanges the two residue branches at each offset. -/
theorem residue_pair_anti_transpose (r q qPrime : ℤ)
    (A B : VertexOperator ℂ V) (Adual Bdual : VertexOperator ℂ W)
    (pair : W →ₗ[ℂ] V →ₗ[ℂ] ℂ)
    (hA : ∀ (k : ℤ) (w : W) (v : V),
      pair ((Adual [[k]]) w) v = pair w ((A [[r - k]]) v))
    (hB : ∀ (k : ℤ) (w : W) (v : V),
      pair ((Bdual [[k]]) w) v = pair w ((B [[q + qPrime + r - k]]) v))
    (w : W) (v : V) :
    pair (((residueField 1 r Adual Bdual).operator [[q]]) w) v =
      -epsilon r * pair w (((residueField 1 r A B).operator [[qPrime]]) v) := by
  have forward : pair (residueLeft r q Adual Bdual w) v =
      pair w (residueRight r qPrime A B v) := by
    change (pair.flip v) (residueLeft r q Adual Bdual w) =
      (pair w) (residueRight r qPrime A B v)
    unfold residueLeft residueRight
    rw [map_finsum (pair.flip v) ((residueField 1 r Adual Bdual).left_finite q w),
      map_finsum (pair w) ((residueField 1 r A B).right_finite qPrime v)]
    apply finsum_congr
    intro j
    simp only [map_smul]
    simp only [LinearMap.flip_apply]
    rw [hA, hB, show r - (r - (j : ℤ)) = (j : ℤ) by omega,
      show q + qPrime + r - (q + (j : ℤ)) = r + qPrime - (j : ℤ) by omega]
  have reverse : pair (residueRight r q Adual Bdual w) v =
      pair w (residueLeft r qPrime A B v) := by
    change (pair.flip v) (residueRight r q Adual Bdual w) =
      (pair w) (residueLeft r qPrime A B v)
    unfold residueRight residueLeft
    rw [map_finsum (pair.flip v) ((residueField 1 r Adual Bdual).right_finite q w),
      map_finsum (pair w) ((residueField 1 r A B).left_finite qPrime v)]
    apply finsum_congr
    intro j
    simp only [map_smul]
    simp only [LinearMap.flip_apply]
    rw [hB, hA,
      show q + qPrime + r - (r + q - (j : ℤ)) = qPrime + (j : ℤ) by omega]
  have signSquare : epsilon r * epsilon r = 1 := by
    rw [epsilon, ← mul_zpow]
    norm_num
  rw [(residueField 1 r Adual Bdual).coefficient, (residueField 1 r A B).coefficient]
  change (pair.flip v) (residueCoefficient 1 r q Adual Bdual w) =
    -epsilon r * pair w (residueCoefficient 1 r qPrime A B v)
  simp only [residueCoefficient, mul_one, map_sub, map_smul, smul_eq_mul]
  simp only [LinearMap.flip_apply, forward, reverse]
  calc
    _ = -epsilon r * pair w (residueLeft r qPrime A B v) +
        (epsilon r * epsilon r) * pair w (residueRight r qPrime A B v) := by
      rw [signSquare, one_mul]
      ring
    _ = _ := by ring

end D5.S3.VertexAlgebra.SignedFieldResidueReflection
