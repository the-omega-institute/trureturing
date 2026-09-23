/- GID: D5/S3/ConceptDynamics/ObservationTopology/TwoHarmonicRotationObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationTopology/TwoHarmonicRotationObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coprime frequency pairs cannot both avoid the half-cosine barrier at a sixth-turn rotation. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationTopology.TwoHarmonicRotationObstruction

/-- At a rotation by `pi / 6`, two coprime natural frequencies cannot both
have cosine magnitude strictly below one half. -/
theorem coprime_two_frequency_cosine_obstruction
    (m n : Nat) (coprime : Nat.Coprime m n) :
    (1 / 2 : Real) <=
      max |Real.cos ((m : Real) * (Real.pi / 6))|
        |Real.cos ((n : Real) * (Real.pi / 6))| := by
  by_contra obstructionFails
  have bothSmall :
      max |Real.cos ((m : Real) * (Real.pi / 6))|
          |Real.cos ((n : Real) * (Real.pi / 6))| < (1 / 2 : Real) :=
    lt_of_not_ge obstructionFails
  have frequencySmall (k : Nat)
      (small : |Real.cos ((k : Real) * (Real.pi / 6))| < (1 / 2 : Real)) :
      k % 6 = 3 := by
    have residueBound : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have decomposition : k = k % 6 + 6 * (k / 6) := (Nat.mod_add_div k 6).symm
    have castDecomposition :
        (k : Real) = ((k % 6 : Nat) : Real) +
          6 * ((k / 6 : Nat) : Real) := by
      exact_mod_cast decomposition
    have angleDecomposition :
        (k : Real) * (Real.pi / 6) =
          ((k % 6 : Nat) : Real) * (Real.pi / 6) +
            (k / 6 : Nat) * Real.pi := by
      rw [castDecomposition]
      ring
    rw [angleDecomposition, Real.cos_add_nat_mul_pi] at small
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at small
    interval_cases residue : k % 6
    · norm_num [residue] at small
    · simp only [Nat.cast_one, one_mul, Real.cos_pi_div_six] at small
      have sqrtNonneg : (0 : Real) <= Real.sqrt 3 := Real.sqrt_nonneg _
      rw [abs_of_nonneg (div_nonneg sqrtNonneg (by norm_num))] at small
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 3),
        Real.sqrt_nonneg 3]
    · norm_num [residue, show (2 : Real) * (Real.pi / 6) = Real.pi / 3 by ring]
        at small
    · omega
    · norm_num [residue,
        show (4 : Real) * (Real.pi / 6) = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub] at small
    · simp only [Nat.cast_ofNat,
        show (5 : Real) * (Real.pi / 6) = Real.pi - Real.pi / 6 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_six, abs_neg] at small
      have sqrtNonneg : (0 : Real) <= Real.sqrt 3 := Real.sqrt_nonneg _
      rw [abs_of_nonneg (div_nonneg sqrtNonneg (by norm_num))] at small
      nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) <= 3),
        Real.sqrt_nonneg 3]
  have mSmall : |Real.cos ((m : Real) * (Real.pi / 6))| < (1 / 2 : Real) :=
    lt_of_le_of_lt (le_max_left _ _) bothSmall
  have nSmall : |Real.cos ((n : Real) * (Real.pi / 6))| < (1 / 2 : Real) :=
    lt_of_le_of_lt (le_max_right _ _) bothSmall
  have mResidue : m % 6 = 3 := frequencySmall m mSmall
  have nResidue : n % 6 = 3 := frequencySmall n nSmall
  have threeDvdM : 3 ∣ m := by
    use 1 + 2 * (m / 6)
    omega
  have threeDvdN : 3 ∣ n := by
    use 1 + 2 * (n / 6)
    omega
  have impossible : Nat.Coprime 3 3 := coprime.of_dvd threeDvdM threeDvdN
  norm_num at impossible

#print axioms coprime_two_frequency_cosine_obstruction
end D5.S3.ConceptDynamics.ObservationTopology.TwoHarmonicRotationObstruction
