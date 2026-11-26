/- GID: D5/S3/Quantum/Measurement/Auric/CoherentSlack
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/CoherentSlack
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive majorant on the three coherent Choi coordinates of one flag. -/

import D5.S3.Quantum.Measurement.Auric.FiveLevelTilt
import D5.S3.Quantum.Measurement.Auric.RootTrace

/-! # Positive majorant on the three coherent Choi coordinates of one flag -/

namespace D5.S3.Quantum.Measurement.Auric.CoherentSlack

open _root_.Matrix
open D5.S3.Quantum.Measurement.Auric.FiveLevelTilt
open scoped ComplexOrder MatrixOrder

private def realRankOne (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (fun i => (v i : ℂ)) (fun i => (v i : ℂ))

@[simp] theorem averagedCoherentGram_apply_aux (v : Fin 3 → ℝ) (i j : Fin 3) :
    realRankOne v i j = (v i : ℂ) * (v j : ℂ) := rfl

private theorem realRankOne_psd (v : Fin 3 → ℝ) : (realRankOne v).PosSemidef := by
  let z : Fin 3 → ℂ := fun i => (v i : ℂ)
  have hz : star z = z := by
    funext i
    simp [Pi.star_apply, z]
  have h := Matrix.posSemidef_vecMulVec_self_star z
  rwa [hz] at h

/-- Diagonal-coordinate Gram block of a flag after within-sector swaps,
the flag interchange, and the deletion of phase-mismatched coherences. -/
noncomputable def averagedCoherentGram (c a h : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℝ) • realRankOne ![1, 1, c] +
    (1 / 4 : ℝ) • realRankOne ![a, 1, h] +
    (1 / 4 : ℝ) • realRankOne ![1, a, h]

/-- The target flag's single Kraus vector on its active sector and the spectator. -/
noncomputable def targetCoherentGram : Matrix (Fin 3) (Fin 3) ℂ :=
  realRankOne ![1, 1, Real.sqrt 2 / 2]

private noncomputable def coherentBasis : Matrix (Fin 2) (Fin 3) ℂ :=
  !![(Real.sqrt 2 / 2 : ℝ), (Real.sqrt 2 / 2 : ℝ), 0; 0, 0, 1]

private noncomputable def antiBasis : Fin 3 → ℝ :=
  ![Real.sqrt 2 / 2, -(Real.sqrt 2 / 2), 0]

private noncomputable def symmetricSlack (w u v d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(2*w-u : ℝ), (w-d : ℝ); (w-d : ℝ), (w/2-v : ℝ)]

private theorem coherent_decomposition (c a h w : ℝ) :
    w • targetCoherentGram - (targetCoherentGram - averagedCoherentGram c a h) =
      coherentBasisᴴ * symmetricSlack w ((1-a)*(3+a)/4)
        ((1-c^2-h^2)/2)
        (1-Real.sqrt 2 * (c/2+(1+a)*h/4)) * coherentBasis +
      ((1-a)^2/4 : ℝ) • realRankOne antiBasis := by
  set s := Real.sqrt (2 : ℝ) with hs
  have hs2 : s^2 = 2 := by rw [hs, Real.sq_sqrt (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    simp [targetCoherentGram, averagedCoherentGram, realRankOne, vecMulVec,
      coherentBasis, symmetricSlack,
      antiBasis, ← hs, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
      pow_two, Complex.conj_ofReal, map_ofNat] <;>
    nlinarith only [hs2,
      congrArg (fun x : ℝ => x * c) hs2, congrArg (fun x : ℝ => x * a) hs2,
      congrArg (fun x : ℝ => x * h) hs2, congrArg (fun x : ℝ => x * w) hs2,
      congrArg (fun x : ℝ => x * a^2) hs2, congrArg (fun x : ℝ => x * a*h) hs2]

/-- The matching two-dimensional certificate also controls the antisymmetric
coherent direction. Its slack there is the nonnegative square from the swap. -/
theorem coherent_flag_majorized (c a h r : ℝ) (hr : 0 < r) :
    let u := (1-a)*(3+a)/4
    let v := (1-c^2-h^2)/2
    let d := 1-Real.sqrt 2 * (c/2+(1+a)*h/4)
    let w := (Real.sqrt 2 * u + r * d) / (2 * Real.sqrt 2 + r)
    (2-r/Real.sqrt 2)*d + Real.sqrt 2 * r * v - u = 0 →
    u ≤ 2*d →
    (w • targetCoherentGram - (targetCoherentGram - averagedCoherentGram c a h)).PosSemidef := by
  dsimp only
  intro hmatch hpositive
  have h := (matching_certificate r _ _ _ hr hmatch hpositive).1
  rw [coherent_decomposition]
  exact (h.conjTranspose_mul_mul_same coherentBasis).add
    ((realRankOne_psd antiBasis).smul (by positivity))

end D5.S3.Quantum.Measurement.Auric.CoherentSlack
