/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldGradedCharacter
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldGradedCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The fixed theta projection and shifted twisted count give every orbifold weight. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
import D5.S3.VertexAlgebra.SourceBPZ.ThetaGradeTraceSplit
import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter

/-! Graded multiplicities of the original two-sector conformal zero mode. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.OriginalOrbifoldGradedCharacter

open TwistedGround.OriginalOrbifoldConformal (L)
open TwistedGround.OriginalOrbifoldLowSpectrum (eigenspaceEquiv)
open LatticeGeneratingFieldLocality (LatticeData)
open LatticeInvolution (fixedSpace)
open LatticePositiveEnergy (grade grade_finiteDimensional actualL0_eigenspace_eq_grade
  complex_inverse_exists)
open LatticeHalfFockGradedTrace (actualTensorL0 actualGrade actual_grade_finrank_bRank bRank)
open LatticeHalfFockParityT (actualParity actualParity_on_actualGrade)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeSugawaraCurrents (gramComplex sugawaraMode)
open SourceBPZ.ThetaGradeTraceSplit (plusGrade minusGrade gradeTheta gradeSplitEquiv
  grade_theta_trace_eq_fixed_minus_anti)
open LatticeThetaCharacter (signedThetaCoefficient fullThetaRestriction positiveFullThetaTrace
  positive_full_theta_character)
open ActualLeechHyperbolic (leechData leech_spec)
open D5.S3.Combinatorics.Partitions.ColouredOddOccupation (colouredFiberSeries)
open D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity (card_colouredFiber)
open private fixedEnergy oddEnergy fixedEnergy_finite oddEnergy_finite oddEnergy_eq_bot
  from D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldLowSpectrum
open private canonicalFixedEnergy_eq_fixedGrade from
  D5.S3.VertexAlgebra.Lattice.InvolutionRootlessLowGrades

noncomputable section

/-- At weight `n ≥ 2` the entire negative-parity sector is the actual twisted
grade `2*n - 3`. The twisted eigenvalue is `24/16 + (2*n - 3)/2`, and this
grade has odd parity. -/
theorem negative_eigenspace_eq_actualGrade (D : LatticeData) (hu : IsUnit D.G.det)
    (h24 : D.rank = 24) (n : ℕ) (hn : 2 ≤ n) :
    paritySpace D hu (-1) ⊓ (actualTensorL0 D hu).eigenspace (n : ℂ) =
      actualGrade D hu (2 * n - 3) := by
  have hdegree : 2 * n - 3 + 3 = 2 * n := by omega
  have hcast : ((2 * n - 3 : ℕ) : ℂ) + 3 = 2 * (n : ℂ) := by
    exact_mod_cast hdegree
  have hshift : (D.rank : ℂ) / 16 + ((2 * n - 3 : ℕ) : ℂ) / 2 = (n : ℂ) := by
    rw [h24]
    linear_combination hcast / 2
  have henergy : (actualTensorL0 D hu).eigenspace (n : ℂ) =
      actualGrade D hu (2 * n - 3) := by
    rw [Module.End.eigenspace_def, Module.End.one_eq_id, actualGrade, hshift]
  rw [henergy, inf_eq_right]
  intro v hv
  have hodd : (2 * n - 3) % 2 = 1 := by omega
  have hp := actualParity_on_actualGrade D hu (2 * n - 3) ⟨v, hv⟩
  change actualParity D hu v = ((-1 : ℂ) ^ (2 * n - 3)) • v at hp
  rw [neg_one_pow_eq_pow_mod_two, hodd, pow_one] at hp
  simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hp

private theorem fixed_finrank_eq (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℕ) :
    (Module.finrank ℂ (fixedEnergy D (n : ℂ)) : ℂ) =
      ((Module.finrank ℂ (grade D n) : ℂ) +
        LinearMap.trace ℂ (grade D n) (gradeTheta D n)) / 2 := by
  have hfixed : fixedEnergy D (n : ℂ) = plusGrade D n := by
    have he := canonicalFixedEnergy_eq_fixedGrade D hD (n : ℤ)
    rw [Int.cast_natCast] at he
    change fixedEnergy D (n : ℂ) = fixedSpace D ⊓ grade D n at he
    exact he.trans (inf_comm _ _)
  let : FiniteDimensional ℂ (grade D n) := grade_finiteDimensional D hD n
  let : FiniteDimensional ℂ (plusGrade D n) := Submodule.finiteDimensional_of_le inf_le_left
  let : FiniteDimensional ℂ (minusGrade D n) := Submodule.finiteDimensional_of_le inf_le_left
  have hdim := (gradeSplitEquiv D n).finrank_eq.trans Module.finrank_prod
  rw [hfixed, grade_theta_trace_eq_fixed_minus_anti D n hD, hdim, Nat.cast_add]
  ring

private theorem negative_finrank_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24) (n : ℕ) :
    Module.finrank ℂ (oddEnergy D hu (n : ℂ)) =
      if 2 ≤ n then 4096 * bRank 24 (2 * n - 3) else 0 := by
  by_cases hn : 2 ≤ n
  · have he : oddEnergy D hu (n : ℂ) = actualGrade D hu (2 * n - 3) :=
      negative_eigenspace_eq_actualGrade D hu h24 n hn
    rw [ite_eq_left hn, he, actual_grade_finrank_bRank, h24]
    norm_num
  · rw [ite_eq_right hn, oddEnergy_eq_bot D hu hD h24 n (Nat.lt_of_not_ge hn), finrank_bot]

set_option maxHeartbeats 1000000 in
-- The sector equivalence and finite-dimensional instances elaborate over concrete Leech data.
/-- The weight multiplicity of the original Golay–Leech orbifold is the
theta-fixed projection of the lattice grade plus the negative twisted count. -/
theorem actual_leech_graded_character_coefficient (n : ℕ) :
    let D := leechData
    let A := L D leech_spec.2.1 leech_spec.2.2.1 0
    (Module.finrank ℂ (A.eigenspace (n : ℂ)) : ℂ) =
      ((Module.finrank ℂ (grade D n) : ℂ) +
        LinearMap.trace ℂ (grade D n) (gradeTheta D n)) / 2 +
      (if 2 ≤ n then 4096 * bRank 24 (2 * n - 3) else 0 : ℕ) := by
  dsimp only
  let hu := leech_spec.2.1
  let hD : Matrix.PosDef (leechData.G.map (Int.cast : ℤ → ℝ)) := leech_spec.2.2.1
  let := fixedEnergy_finite leechData hD (n : ℂ) (n : ℤ) (Int.cast_natCast n)
  let := oddEnergy_finite leechData hu hD leech_spec.1 n
  have hdim := (eigenspaceEquiv leechData hu hD (n : ℂ)).finrank_eq.trans Module.finrank_prod
  rw [hdim, Nat.cast_add,
    fixed_finrank_eq leechData hD n, negative_finrank_eq leechData hu hD leech_spec.1 n]

set_option maxHeartbeats 1000000 in
-- Conjugation transports the endomorphism and its trace across the submodule equality.
/-- The theta trace on the ambient energy grade is the signed neutral
oscillator coefficient. Both restrictions are conjugate through the
identification of the Sugawara eigenspace with the energy grade. -/
theorem grade_theta_trace_eq_signedThetaCoefficient (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (n : ℕ) :
    LinearMap.trace ℂ (grade D n) (gradeTheta D n) = signedThetaCoefficient D n := by
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists D hD
  let e := LinearEquiv.ofEq _ _ (actualL0_eigenspace_eq_grade D H hHG hGH (n : ℤ))
  have hconj : e.conj (fullThetaRestriction D H hHG hGH n) = gradeTheta D n := by
    ext v
    rfl
  have ht := (positive_full_theta_character D H hHG hGH hD (q := 0) (by simp)).1 (n : ℤ)
  rw [← hconj, LinearMap.trace_conj']
  change positiveFullThetaTrace D H hHG hGH hD (n : ℤ) = _
  simpa using ht

set_option maxHeartbeats 1000000 in
-- The coefficient proof rewrites the series of the concrete orbifold eigenspaces.
/-- The unshifted weight series of the original `L₀`. The odd coefficients of
the 24-coloured half-Fock series give the twisted term starting at weight two. -/
theorem actual_leech_graded_character_series :
    let D := leechData
    let A := L D leech_spec.2.1 leech_spec.2.2.1 0
    PowerSeries.mk (fun n => (Module.finrank ℂ (A.eigenspace (n : ℂ)) : ℂ)) =
      PowerSeries.C (1 / 2 : ℂ) *
        (PowerSeries.mk (fun n : ℕ => (Module.finrank ℂ (grade D n) : ℂ)) +
          PowerSeries.mk (signedThetaCoefficient D)) +
      PowerSeries.X ^ 2 * PowerSeries.mk (fun k => 4096 *
        PowerSeries.coeff (2 * k + 1) (colouredFiberSeries ℂ (Fin 24))) := by
  dsimp only
  apply PowerSeries.ext
  intro n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_mk]
  rw [actual_leech_graded_character_coefficient,
    grade_theta_trace_eq_signedThetaCoefficient leechData leech_spec.2.2.1, one_div,
    ← div_eq_inv_mul]
  simp only [colouredFiberSeries, PowerSeries.coeff_mk, card_colouredFiber, bRank]
  by_cases hn : 2 ≤ n
  · have hd : 2 * (n - 2) + 1 = 2 * n - 3 := by omega
    simp only [hn, ↓reduceIte, hd, Nat.cast_mul, Nat.cast_ofNat]
  · simp only [hn, ↓reduceIte, Nat.cast_zero]

#print axioms negative_eigenspace_eq_actualGrade
#print axioms actual_leech_graded_character_coefficient
#print axioms grade_theta_trace_eq_signedThetaCoefficient
#print axioms actual_leech_graded_character_series

end
end D5.S3.VertexAlgebra.OriginalOrbifoldGradedCharacter
