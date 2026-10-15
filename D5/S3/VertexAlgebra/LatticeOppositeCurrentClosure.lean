/- GID: D5/S3/VertexAlgebra/LatticeOppositeCurrentClosure
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeOppositeCurrentClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every actual negative-current opposite insertion reverses the two finite compositions. -/

import D5.S3.VertexAlgebra.LatticeOppositeDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure

open LatticeGeneratingFieldLocality LatticeAllStateField LatticePositiveEnergy
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents LatticeSugawaraConformal
open LatticeSugawaraVirasoro LatticeSugawaraLocalNilpotence LatticeOppositeCoefficients
open LatticeOppositeCurrentInsertion LatticeOppositeDerivative
open scoped BigOperators VertexOperator

noncomputable section

attribute [local irreducible] sugawaraMode neutralMode Y translation oppositeCoeff

def oppositeLinear (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (weight index : ℤ) :
    Carrier D →ₗ[ℂ] Module.End ℂ (Carrier D) where
  toFun state := oppositeCoeff D H weight state index
  map_add' first second := by
    rw [opposite_finsum, opposite_finsum, opposite_finsum]
    have termAdd (power : ℕ) :
        oppositeTerm D H weight (first + second) index power =
          oppositeTerm D H weight first index power + oppositeTerm D H weight second index power := by
      simp only [oppositeTerm, map_add, Pi.add_apply, smul_add]
    simp_rw [termAdd]
    rw [finsum_add_distrib (opposite_terms_finite D H weight first index)
      (opposite_terms_finite D H weight second index), smul_add]
  map_smul' scalar state := by
    rw [opposite_finsum, opposite_finsum]
    have termSmul (power : ℕ) :
        oppositeTerm D H weight (scalar • state) index power =
          scalar • oppositeTerm D H weight state index power := by
      simp only [oppositeTerm, map_smul, Pi.smul_apply, smul_smul]
      rw [mul_comm]
    simp_rw [termSmul]
    rw [← smul_finsum, smul_comm]
    rfl

private theorem translation_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (state : Carrier D) (weight : ℤ) (homogeneous : state ∈ grade D weight) :
    translation D state ∈ grade D (weight + 1) := by
  apply (actualL0_eigen_iff_grade D H hHG hGH _ _).mp
  have eigen := (actualL0_eigen_iff_grade D H hHG hGH weight state).mpr homogeneous
  have commutator := congrArg (fun operator : Module.End ℂ (Carrier D) => operator state)
    (sugawaraMode_virasoro D H hHG hGH 0 (-1))
  rw [sugawaraMode_minus_one_eq_translation D H hHG hGH] at commutator
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, eigen, map_smul] at commutator
  norm_num at commutator
  rw [sugawaraMode_minus_one_eq_translation D H hHG hGH] at commutator
  rw [sub_eq_iff_eq_add] at commutator
  rw [commutator]
  push_cast
  module

theorem current_insertion_grade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (degree : ℕ) (state : Carrier D) (weight : ℤ)
    (homogeneous : state ∈ grade D weight) :
    neutralMode D current (-(degree : ℤ) - 1) state ∈ grade D (weight + degree + 1) := by
  apply (actualL0_eigen_iff_grade D H hHG hGH _ _).mp
  have eigen := (actualL0_eigen_iff_grade D H hHG hGH weight state).mpr homogeneous
  have commutator := congrArg (fun operator : Module.End ℂ (Carrier D) => operator state)
    (sugawaraMode_current_commutator D H hHG hGH current 0 (-(degree : ℤ) - 1))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    eigen, map_smul, zero_add] at commutator
  rw [sub_eq_iff_eq_add] at commutator
  rw [commutator]
  push_cast
  module

private theorem choose_first_step (degree offset : ℕ) :
    ((offset + 1 : ℕ) : ℂ) * ((degree + (offset + 1)).choose degree : ℂ) =
      ((degree + 1 : ℕ) : ℂ) * (((degree + 1) + offset).choose (degree + 1) : ℂ) := by
  have binomialIdentity := Nat.choose_succ_right_eq (degree + offset + 1) degree
  have difference : degree + offset + 1 - degree = offset + 1 := by omega
  rw [difference] at binomialIdentity
  exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using binomialIdentity.symm)

private theorem choose_second_step (degree offset : ℕ) :
    ((offset + degree + 1 : ℕ) : ℂ) * ((degree + offset).choose degree : ℂ) =
      ((degree + 1 : ℕ) : ℂ) * (((degree + 1) + offset).choose (degree + 1) : ℂ) := by
  exact_mod_cast (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]
    using Nat.add_one_mul_choose_eq (degree + offset) degree)

private theorem first_recursion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (degree : ℕ) (state tested : Carrier D)
    (weight index : ℤ) (homogeneous : state ∈ grade D weight) :
    (index : ℂ) • (∑ᶠ offset : ℕ, reversedFirstTerm D H current degree weight state (index - 1) tested offset) +
        (∑ᶠ offset : ℕ, reversedFirstTerm D H current degree (weight + 1) (translation D state) index tested offset) =
      -((degree + 1 : ℕ) : ℂ) • ∑ᶠ offset : ℕ,
        reversedFirstTerm D H current (degree + 1) weight state index tested offset := by
  classical
  let combined : ℕ → Carrier D := fun offset => (index : ℂ) •
    reversedFirstTerm D H current degree weight state (index - 1) tested offset +
    reversedFirstTerm D H current degree (weight + 1) (translation D state) index tested offset
  have finiteCombined : Function.HasFiniteSupport combined :=
    ((reversed_first_finite D H current degree weight state (index - 1) tested).fun_comp
      (smul_zero (index : ℂ))).add
      (reversed_first_finite D H current degree (weight + 1) (translation D state) index tested)
  have point (offset : ℕ) : combined offset =
      -(offset : ℂ) • (((degree + offset).choose degree : ℂ) •
        oppositeCoeff D H weight state (index + offset - 1)
          (neutralMode D current (offset + degree + 1) tested)) := by
    unfold combined reversedFirstTerm
    rw [opposite_translation D H hHG hGH state weight (index + offset) homogeneous,
      LinearMap.smul_apply]
    rw [show (index - 1) + offset = index + offset - 1 by omega]
    push_cast
    module
  have atZero : combined 0 = 0 := by rw [point]; simp
  have successor (offset : ℕ) : combined (offset + 1) =
      -((degree + 1 : ℕ) : ℂ) •
        reversedFirstTerm D H current (degree + 1) weight state index tested offset := by
    rw [point]
    unfold reversedFirstTerm
    rw [show index + (offset + 1 : ℕ) - 1 = index + offset by omega,
      show (offset + 1 : ℕ) + (degree : ℤ) + 1 = offset + (degree + 1 : ℕ) + 1 by omega]
    simp only [smul_smul, neg_mul]
    rw [choose_first_step]
  rw [smul_finsum, ← finsum_add_distrib
    ((reversed_first_finite D H current degree weight state (index - 1) tested).fun_comp (smul_zero _))
    (reversed_first_finite D H current degree (weight + 1) (translation D state) index tested)]
  change (∑ᶠ offset : ℕ, combined offset) = _
  rw [finsum_zero_succ combined finiteCombined, atZero, zero_add, smul_finsum]
  exact finsum_congr successor

private theorem second_recursion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (degree : ℕ) (state tested : Carrier D)
    (weight index : ℤ) (homogeneous : state ∈ grade D weight) :
    -(index : ℂ) • (∑ᶠ offset : ℕ, reversedSecondTerm D H current degree weight state (index - 1) tested offset) -
        (∑ᶠ offset : ℕ, reversedSecondTerm D H current degree (weight + 1) (translation D state) index tested offset) =
      -((degree + 1 : ℕ) : ℂ) • ∑ᶠ offset : ℕ,
        reversedSecondTerm D H current (degree + 1) weight state index tested offset := by
  classical
  rw [smul_finsum, ← finsum_sub_distrib
    ((reversed_second_finite D H current degree weight state (index - 1) tested).fun_comp (smul_zero _))
    (reversed_second_finite D H current degree (weight + 1) (translation D state) index tested), smul_finsum]
  apply finsum_congr
  intro offset
  unfold reversedSecondTerm
  rw [opposite_translation D H hHG hGH state weight (index - offset - degree - 1) homogeneous,
    LinearMap.smul_apply, map_smul]
  rw [show (index - 1) - offset - degree - 1 = index - offset - (degree + 1 : ℕ) - 1 by omega,
    show index - offset - degree - 1 - 1 = index - offset - (degree + 1 : ℕ) - 1 by omega]
  have weightCoefficient :
      -(index : ℂ) * ((degree + offset).choose degree : ℂ) -
          ((degree + offset).choose degree : ℂ) * (-((index - offset - degree - 1 : ℤ) : ℂ)) =
        -((degree + 1 : ℕ) : ℂ) * (((degree + 1) + offset).choose (degree + 1) : ℂ) := by
    have choose := choose_second_step degree offset
    push_cast at *
    linear_combination -choose
  rw [smul_smul, smul_smul, smul_smul, ← sub_smul, weightCoefficient]

set_option maxHeartbeats 4000000 in
theorem opposite_current_insertion (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (current : Fin D.rank) (degree : ℕ) (state tested : Carrier D)
    (weight index : ℤ) (homogeneous : state ∈ grade D weight) :
    oppositeCoeff D H (weight + degree + 1)
      (neutralMode D current (-(degree : ℤ) - 1) state) index tested =
      -(∑ᶠ offset : ℕ, reversedFirstTerm D H current degree weight state index tested offset) +
        (-1 : ℂ)^(degree + 1) •
          ∑ᶠ offset : ℕ, reversedSecondTerm D H current degree weight state index tested offset := by
  induction degree generalizing weight state index with
  | zero => simpa [sub_eq_add_neg] using opposite_current_one_insertion D H hHG hGH current state tested weight index
  | succ degree inductionHypothesis =>
    have stateGrade := current_insertion_grade D H hHG hGH current degree state weight homogeneous
    have translationGrade := translation_grade D H hHG hGH state weight homogeneous
    have stateRecursion := congrArg (fun operator : Module.End ℂ (Carrier D) => operator state)
      (neutral_translation_covariance D current (-(degree : ℤ) - 1))
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at stateRecursion
    have recursion := congrArg (fun vector : Carrier D =>
      oppositeLinear D H (weight + degree + 1 + 1) index vector tested) stateRecursion
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, oppositeLinear] at recursion
    change oppositeCoeff D H (weight + degree + 1 + 1)
        (translation D (neutralMode D current (-(degree : ℤ) - 1) state)) index tested -
      oppositeCoeff D H (weight + degree + 1 + 1)
        (neutralMode D current (-(degree : ℤ) - 1) (translation D state)) index tested =
      -((-(degree : ℤ) - 1 : ℤ) : ℂ) • oppositeCoeff D H (weight + degree + 1 + 1)
        (neutralMode D current (-(degree : ℤ) - 1 - 1) state) index tested at recursion
    rw [opposite_translation D H hHG hGH _ (weight + degree + 1) index stateGrade,
      LinearMap.smul_apply] at recursion
    rw [inductionHypothesis state weight (index - 1) homogeneous] at recursion
    rw [show weight + degree + 1 + 1 = (weight + 1) + degree + 1 by omega,
      inductionHypothesis (translation D state) (weight + 1) index translationGrade] at recursion
    have first := first_recursion D H hHG hGH current degree state tested weight index homogeneous
    have second := second_recursion D H hHG hGH current degree state tested weight index homogeneous
    have nonzero : ((degree + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero degree
    have coefficient : -((-(degree : ℤ) - 1 : ℤ) : ℂ) = ((degree + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [show -(degree : ℤ) - 1 - 1 = -(degree + 1 : ℕ) - 1 by omega,
      coefficient, show (weight + 1) + degree + 1 = weight + (degree + 1 : ℕ) + 1 by omega] at recursion
    apply (smul_right_injective (M := Carrier D) nonzero)
    change ((degree + 1 : ℕ) : ℂ) • _ = ((degree + 1 : ℕ) : ℂ) • _
    rw [← recursion]
    calc
      _ = ((index : ℂ) • (∑ᶠ offset : ℕ,
            reversedFirstTerm D H current degree weight state (index - 1) tested offset) +
          ∑ᶠ offset : ℕ,
            reversedFirstTerm D H current degree (weight + 1) (translation D state) index tested offset) +
        (-1 : ℂ)^(degree + 1) •
          (-(index : ℂ) • (∑ᶠ offset : ℕ,
            reversedSecondTerm D H current degree weight state (index - 1) tested offset) -
            ∑ᶠ offset : ℕ,
              reversedSecondTerm D H current degree (weight + 1) (translation D state) index tested offset) := by module
      _ = _ := by
        rw [first, second, pow_succ]
        module

end
end D5.S3.VertexAlgebra.LatticeOppositeCurrentClosure
