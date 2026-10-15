/- GID: D5/S3/VertexAlgebra/LatticeHalfFockTargetThetaCorrectionWeight
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockTargetThetaCorrectionWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consumed exact original suppliers with checked private visibility bridges. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.labelledRemainders_size
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `labelledRemainders_size) := @$(Lean.mkIdent supplier)))

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeSugawaraConformal 0).append
    `D5.S3.VertexAlgebra.LatticeSugawaraConformal.oscillatorEuler_monomial
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `oscillatorEuler_monomial) := @$(Lean.mkIdent supplier)))

run_cmd
  let supplier := (Lean.Name.num `_private.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection 0).append
    `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.wordWeight_occurrences
  Lean.Elab.Command.elabCommand
    (← `(noncomputable abbrev $(Lean.mkIdent `wordWeight_occurrences) := @$(Lean.mkIdent supplier)))


open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeSugawaraConformal LatticeFiniteNegativeGeneration MvPolynomial
open LatticeSugawaraVirasoro
open scoped BigOperators

noncomputable section

def correctionWeight (D : LatticeData) : Option (Index D) → ℕ :=
  fun coordinate => coordinate.elim 1 (sourceWeight D)

private theorem singleton_weighted (D : LatticeData) (charge : Charge D) (index : Index D) :
    IsWeightedHomogeneous (correctionWeight D) (singletonPolynomial D charge index)
      (sourceWeight D index) := by
  unfold singletonPolynomial
  have power := (isWeightedHomogeneous_X ℂ (correctionWeight D) none).pow
    (sourceWeight D index)
  simpa only [correctionWeight, Option.elim_none, smul_eq_mul, mul_one]
    using power.C_mul _

private theorem pair_weighted (D : LatticeData) (first second : Index D) :
    IsWeightedHomogeneous (correctionWeight D) (pairPolynomial D first second)
      (sourceWeight D first + sourceWeight D second) := by
  unfold pairPolynomial
  have power := (isWeightedHomogeneous_X ℂ (correctionWeight D) none).pow
    (sourceWeight D first + sourceWeight D second)
  simpa only [correctionWeight, Option.elim_none, smul_eq_mul, mul_one]
    using power.C_mul _

private theorem list_weighted (D : LatticeData) (polynomials : List (CorrectionPolynomial D))
    (weight : ℕ) (homogeneous : ∀ polynomial ∈ polynomials,
      IsWeightedHomogeneous (correctionWeight D) polynomial weight) :
    IsWeightedHomogeneous (correctionWeight D) polynomials.sum weight := by
  induction polynomials with
  | nil => exact isWeightedHomogeneous_zero ℂ _ _
  | cons first tail inductionProof =>
    exact (homogeneous first (by simp)).add
      (inductionProof (fun polynomial member => homogeneous polynomial (by simp [member])))

set_option maxHeartbeats 2000000 in
theorem correctionWord_weighted (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) :
    IsWeightedHomogeneous (correctionWeight D) (correctionWord D charge word)
      (wordWeight D word) := by
  have allWords : ∀ count : ℕ, ∀ word : List (Index D), word.length = count →
      IsWeightedHomogeneous (correctionWeight D) (correctionWord D charge word)
        (wordWeight D word) := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count inductionProof =>
      intro word size
      cases word with
      | nil => exact isWeightedHomogeneous_one ℂ _
      | cons index tail =>
        rw [correctionWord_matching]
        apply IsWeightedHomogeneous.add
        · have tailWeighted := inductionProof tail.length (by
            simp only [List.length_cons] at size
            omega) tail rfl
          exact ((isWeightedHomogeneous_X ℂ (correctionWeight D) (some index)).add
            (singleton_weighted D charge index)).mul tailWeighted
        · apply list_weighted
          intro polynomial member
          obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
          obtain ⟨lengthLaw, weightLaw⟩ := labelledRemainders_size D tail entry entryMember
          have remaining := inductionProof entry.2.length (by
            simp only [List.length_cons] at size
            omega) entry.2 rfl
          have weighted := (pair_weighted D index entry.1).mul remaining
          have equality : sourceWeight D index + sourceWeight D entry.1 +
              wordWeight D entry.2 = wordWeight D (index :: tail) := by
            simp only [wordWeight, List.map_cons, List.sum_cons] at *
            omega
          rw [equality] at weighted
          exact weighted
  exact allWords word.length word rfl

private theorem option_weight (D : LatticeData) (exponent : Index D →₀ ℕ) (shift : ℕ) :
    Finsupp.weight (correctionWeight D) (exponent.optionElim shift) =
      shift + Finsupp.weight (sourceWeight D) exponent := by
  rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul,
    Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
  simp only [correctionWeight, Option.elim_none, Option.elim_some, smul_eq_mul, mul_one]
  rfl

theorem correctionWord_coefficient_weight (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) (shift : ℕ) (exponent : Index D →₀ ℕ)
    (nonzero : coeff exponent ((optionEquivLeft ℂ (Index D)
      (correctionWord D charge word)).coeff shift) ≠ 0) :
    shift + Finsupp.weight (sourceWeight D) exponent = wordWeight D word := by
  rw [optionEquivLeft_coeff_coeff] at nonzero
  have weighted := correctionWord_weighted D charge word nonzero
  rwa [option_weight] at weighted

private theorem euler_shift (D : LatticeData) (polynomial : Oscillator D) (weight shift : ℕ)
    (homogeneous : ∀ exponent, coeff exponent polynomial ≠ 0 →
      shift + Finsupp.weight (sourceWeight D) exponent = weight) :
    oscillatorEuler D polynomial + (shift : ℂ) • polynomial = (weight : ℂ) • polynomial := by
  classical
  conv_lhs => rw [polynomial.as_sum]
  conv_rhs => rw [polynomial.as_sum]
  rw [map_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro exponent member
  rw [oscillatorEuler_monomial, ← add_smul]
  have equality := homogeneous exponent (mem_support_iff.mp member)
  have scalar : (Finsupp.weight (sourceWeight D) exponent : ℂ) + (shift : ℂ) =
      (weight : ℂ) := by exact_mod_cast (by omega :
        Finsupp.weight (sourceWeight D) exponent + shift = weight)
  exact congrArg (fun value : ℂ => value • monomial exponent (coeff exponent polynomial)) scalar

theorem Corr_Euler (D : LatticeData) (charge : Charge D) (polynomial : Oscillator D)
    (shift : ℕ) :
    oscillatorEuler D (Corr D charge polynomial shift) +
        (shift : ℂ) • Corr D charge polynomial shift =
      Corr D charge (oscillatorEuler D polynomial) shift := by
  induction polynomial using MvPolynomial.induction_on' with
  | monomial exponent scalar =>
    have corrected : oscillatorEuler D (Corr D charge (monomial exponent 1) shift) +
        (shift : ℂ) • Corr D charge (monomial exponent 1) shift =
        (Finsupp.weight (sourceWeight D) exponent : ℂ) •
          Corr D charge (monomial exponent 1) shift := by
      rw [Corr_monomial_enumeration D charge exponent _ (List.Perm.refl _)]
      apply euler_shift
      intro remaining nonzero
      rw [← wordWeight_occurrences D exponent]
      exact correctionWord_coefficient_weight D charge _ shift remaining nonzero
    have source : monomial exponent scalar = scalar • (monomial exponent 1 : Oscillator D) := by
      simp [smul_monomial]
    rw [oscillatorEuler_monomial, map_smul, Finsupp.smul_apply, source,
      map_smul, Finsupp.smul_apply, Derivation.map_smul]
    rw [smul_comm (shift : ℂ), ← smul_add, corrected]
    exact smul_comm _ _ _
  | add first second inductionFirst inductionSecond =>
    simp only [map_add, Finsupp.add_apply, smul_add]
    rw [← inductionFirst, ← inductionSecond]
    abel

#print axioms correctionWord_weighted
#print axioms correctionWord_coefficient_weight
#print axioms Corr_Euler

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectionGrading
