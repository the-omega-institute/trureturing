/- GID: D5/S3/Quantum/Measurement/Auric/TiltedInstrument
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/Auric/TiltedInstrument
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual tilted rank-three and rank-two PVM on five levels. -/

import D5.S3.Quantum.Algebra.GramUnitaryExtension
import D5.S3.Quantum.Measurement.Auric.ProjectiveTree
import Mathlib.Tactic

/-! # The actual tilted rank-three and rank-two PVM on five levels -/

namespace D5.S3.Quantum.Measurement.Auric.TiltedInstrument

open Matrix
open D5.S3.Quantum.Measurement.Auric.ProjectiveTree
open D5.S3.Quantum.Algebra.GramUnitaryExtension

abbrev Registers := Matrix (Fin 5) (Fin 5) ℂ

noncomputable def firstEffect (cosine sine : ℝ) : Registers :=
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, (sine ^ 2 : ℝ), 0, (sine * cosine : ℝ);
     0, 0, 0, 0, 0;
     0, 0, (sine * cosine : ℝ), 0, (cosine ^ 2 : ℝ)]

noncomputable def firstKraus (cosine sine : ℝ) : Registers :=
  !![1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, (sine : ℝ), 0, (cosine : ℝ)]

noncomputable def secondKraus (cosine sine outCosine outSine : ℝ) : Registers :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, (outCosine * cosine : ℝ), 0, (-(outCosine * sine) : ℝ);
     0, 0, 0, 1, 0;
     0, 0, (-(outSine * cosine) : ℝ), 0, (outSine * sine : ℝ)]

noncomputable def witnessZero (r : ℝ) : Registers :=
  Matrix.diagonal ![1, 1, 0, 0, (r : ℝ)]

noncomputable def witnessOne (r : ℝ) : Registers :=
  Matrix.diagonal ![0, 0, 1, 1, (r : ℝ)]

theorem first_witness_trace (r c t : ℝ) :
    (witnessZero r * firstKraus c t).trace = ((2 + r * c : ℝ) : ℂ) := by
  simp [witnessZero, firstKraus, Matrix.trace, Matrix.diagonal_mul, Fin.sum_univ_succ]
  push_cast
  ring

theorem second_witness_trace (r c t d b : ℝ) :
    (witnessOne r * secondKraus c t d b).trace = ((1 + d * c + r * (b * t) : ℝ) : ℂ) := by
  simp [witnessOne, secondKraus, Matrix.trace, Matrix.diagonal_mul, Fin.sum_univ_succ]
  push_cast
  ring

private theorem firstEffect_hermitian (c t : ℝ) : (firstEffect c t).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstEffect, conjTranspose_apply, Complex.star_def]

private theorem firstEffect_idempotent (c t : ℝ) (hc : c ^ 2 + t ^ 2 = 1) :
    firstEffect c t * firstEffect c t = firstEffect c t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstEffect, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    norm_cast <;> first
      | linear_combination t ^ 2 * hc
      | linear_combination c ^ 2 * hc
      | linear_combination (t * c) * hc

private theorem firstKraus_gram (c t : ℝ) :
    (firstKraus c t)ᴴ * firstKraus c t = firstEffect c t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstEffect, firstKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.star_def, pow_two, mul_comm]

private theorem secondKraus_gram (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) :
    (secondKraus c t d b)ᴴ * secondKraus c t d b = 1 - firstEffect c t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstEffect, secondKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.star_def, Matrix.one_apply] <;>
    norm_cast <;> first
      | linear_combination c ^ 2 * hd + hc
      | linear_combination t ^ 2 * hd + hc
      | linear_combination -(t * c) * hd

/-- The explicit complementary effects of ranks three and two. -/
noncomputable def tiltedPVM (c t : ℝ) (hc : c ^ 2 + t ^ 2 = 1) : CompletePVM (Fin 5) 2 where
  proj j := if j = 0 then firstEffect c t else 1 - firstEffect c t
  hermitian j := by
    split_ifs
    · exact firstEffect_hermitian c t
    · exact Matrix.isHermitian_one.sub (firstEffect_hermitian c t)
  idempotent j := by
    split_ifs
    · exact firstEffect_idempotent c t hc
    · simp [Matrix.sub_mul, Matrix.mul_sub, firstEffect_idempotent c t hc]
  orthogonal i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.mul_sub, Matrix.sub_mul,
      firstEffect_idempotent c t hc]
  complete := by
    rw [Fin.sum_univ_two]
    simp

/-- The two desired Kraus matrices are implemented by one complete
Lüders measurement and an allowed conditional unitary for each outcome. -/
theorem realizes_tilted_operators (c t d b : ℝ) (hc : c ^ 2 + t ^ 2 = 1)
    (hd : d ^ 2 + b ^ 2 = 1) :
    ∃ U₀ U₁ : Matrix.unitaryGroup (Fin 5) ℂ,
      firstKraus c t = (U₀ : Registers) * (tiltedPVM c t hc).proj 0 ∧
      secondKraus c t d b = (U₁ : Registers) * (tiltedPVM c t hc).proj 1 := by
  have hE := firstEffect_hermitian c t
  have hE2 := firstEffect_idempotent c t hc
  have hF : (1 - firstEffect c t).IsHermitian := Matrix.isHermitian_one.sub hE
  have hF2 : (1 - firstEffect c t) * (1 - firstEffect c t) = 1 - firstEffect c t := by
    simp [Matrix.sub_mul, Matrix.mul_sub, hE2]
  obtain ⟨U₀, hU₀⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (firstKraus c t) (firstEffect c t) (by rw [firstKraus_gram, hE.eq, hE2])
  obtain ⟨U₁, hU₁⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (secondKraus c t d b) (1 - firstEffect c t)
    (by rw [secondKraus_gram c t d b hc hd, hF.eq, hF2])
  exact ⟨U₀, U₁, by simpa [tiltedPVM] using hU₀, by simpa [tiltedPVM] using hU₁⟩

end D5.S3.Quantum.Measurement.Auric.TiltedInstrument
