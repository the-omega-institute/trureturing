/- GID: D5/S3/VertexAlgebra/LatticeOppositeDerivative
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeOppositeDerivative
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite opposite coefficients obey the state-translation derivative law. -/

import D5.S3.VertexAlgebra.LatticeOppositeCurrentInsertion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOppositeDerivative

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeSugawaraConformal LatticeSugawaraVirasoro
open LatticeSugawaraLocalNilpotence LatticeOppositeCoefficients LatticeOppositeCurrentInsertion
open scoped BigOperators VertexOperator

noncomputable section

attribute [local irreducible] sugawaraMode Y translation

private theorem one_translation_commutator (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1) :
    sugawaraMode D H 1 * translation D - translation D * sugawaraMode D H 1 =
      (2 : ℂ) • sugawaraMode D H 0 := by
  rw [← sugawaraMode_minus_one_eq_translation D H hHG hGH,
    sugawaraMode_virasoro D H hHG hGH]
  norm_num

theorem one_pow_translation_succ (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Carrier D) (weight : ℤ) (homogeneous : state ∈ grade D weight) (power : ℕ) :
    ((sugawaraMode D H 1)^(power + 1)) (translation D state) =
      translation D (((sugawaraMode D H 1)^(power + 1)) state) +
        (((power + 1 : ℕ) : ℂ) * (2 * (weight : ℂ) - power)) •
          (((sugawaraMode D H 1)^power) state) := by
  have commute (descendant : Carrier D) :
      sugawaraMode D H 1 (translation D descendant) =
        translation D (sugawaraMode D H 1 descendant) +
          (2 : ℂ) • sugawaraMode D H 0 descendant := by
    have actual := congrArg (fun operator : Module.End ℂ (Carrier D) => operator descendant)
      (one_translation_commutator D H hHG hGH)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at actual
    exact (sub_eq_iff_eq_add.mp actual).trans (add_comm _ _)
  induction power with
  | zero =>
    have eigen := (actualL0_eigen_iff_grade D H hHG hGH weight state).mpr homogeneous
    simpa only [Nat.zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one,
      Nat.cast_zero, sub_zero, one_mul, smul_smul, eigen] using commute state
  | succ power inductionHypothesis =>
    have descendantEigen := (actualL0_eigen_iff_grade D H hHG hGH _ _).mpr
      (one_pow_grade D H hHG hGH weight state homogeneous (power + 1))
    rw [show power + 1 + 1 = (power + 1) + 1 by omega,
      pow_succ', Module.End.mul_apply, inductionHypothesis, map_add, map_smul, commute,
      descendantEigen]
    simp only [smul_smul]
    simp only [pow_succ', Module.End.mul_apply]
    push_cast
    module

set_option maxHeartbeats 2000000 in
theorem opposite_translation (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Carrier D) (weight index : ℤ) (homogeneous : state ∈ grade D weight) :
    oppositeCoeff D H (weight + 1) (translation D state) index =
      -(index : ℂ) • oppositeCoeff D H weight state (index - 1) := by
  classical
  let cutoff := max (oscillatorBound D state) (oscillatorBound D (translation D state)) + 1
  have covers : oscillatorBound D state < cutoff := by dsimp [cutoff]; omega
  have coversTranslation : oscillatorBound D (translation D state) < cutoff + 1 := by
    dsimp [cutoff]
    omega
  let first : ℕ → Module.End ℂ (Carrier D) := fun power =>
    -((2 * weight - index - power : ℤ) : ℂ) •
      (((power.factorial : ℂ)⁻¹) •
        ((Y D (((sugawaraMode D H 1)^power) state))[[2 * weight - index - power - 1]]))
  let second : ℕ → Module.End ℂ (Carrier D) := fun power =>
    (2 * (weight : ℂ) - power) •
      (((power.factorial : ℂ)⁻¹) •
        ((Y D (((sugawaraMode D H 1)^power) state))[[2 * weight - index - power - 1]]))
  have initial : oppositeTerm D H (weight + 1) (translation D state) index 0 = first 0 := by
    unfold oppositeTerm first
    simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero]
    rw [show 2 * (weight + 1) - index - 2 = 2 * weight - index by omega,
      LatticeActualStateDerivative.state_derivative_modes]
    rw [smul_comm]
  have successor (power : ℕ) :
      oppositeTerm D H (weight + 1) (translation D state) index (power + 1) =
        first (power + 1) + second power := by
    unfold oppositeTerm first second
    rw [one_pow_translation_succ D H hHG hGH state weight homogeneous power]
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
    rw [LatticeActualStateDerivative.state_derivative_modes]
    have firstIndex : 2 * (weight + 1) - index - (power + 1 : ℕ) - 2 =
        2 * weight - index - (power + 1 : ℕ) := by omega
    rw [firstIndex]
    congr 1
    · rw [smul_smul, mul_comm]
    · rw [show 2 * weight - index - (power + 1 : ℕ) =
        2 * weight - index - power - 1 by omega]
      rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
      have nonzero : ((power + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero power
      congr 1
      field_simp
  have lastZero : second cutoff = 0 := by
    simp [second, one_pow_eq_zero D H state cutoff covers]
  rw [opposite_cutoff D H (weight + 1) _ index (cutoff + 1) coversTranslation,
    sum_successor_pair _ first second initial successor,
    show (∑ power ∈ Finset.range cutoff, second power) =
      ∑ power ∈ Finset.range (cutoff + 1), second power by
        rw [Finset.sum_range_succ second cutoff, lastZero, add_zero], ← Finset.sum_add_distrib,
    opposite_cutoff D H weight state (index - 1) (cutoff + 1) (by omega)]
  have sign : paritySign (weight + 1) = -paritySign weight := by
    rw [LatticeActualGeneratorLocality.paritySign_add]
    norm_num [paritySign]
  have term (power : ℕ) : first power + second power =
      (index : ℂ) • oppositeTerm D H weight state (index - 1) power := by
    unfold first second oppositeTerm
    rw [show 2 * weight - (index - 1) - power - 2 =
      2 * weight - index - power - 1 by omega]
    push_cast
    module
  simp_rw [term]
  rw [← Finset.smul_sum, sign, smul_smul, smul_smul]
  congr 1
  ring

end
end D5.S3.VertexAlgebra.LatticeOppositeDerivative
