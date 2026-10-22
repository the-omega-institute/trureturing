import D5.S3.VertexAlgebra.TemporaryBcGhostSuperStateField
import D5.S3.VertexAlgebra.TemporaryBcGhostConformalGradingConformalFiniteComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostActualConformalState

open BcGhostFockSupport BcGhostStressCurrent BcGhostSuperGenerators
open BcGhostSuperStateField FieldNormalProduct SuperFieldProducts
open BcGhostConformalFiniteComparison
open scoped VertexOperator

noncomputable section

def omegaState : Carrier :=
  Finsupp.single {1, 2} 1 - (2 : ℂ) • Finsupp.single {0, 3} 1

theorem basisWord_pair (first second : ℕ) (ordered : first < second) :
    basisWord {first, second} = [first, second] := by
  classical
  have nonempty : ({first, second} : Finset ℕ) ≠ ∅ := by simp
  have minimum : ({first, second} : Finset ℕ).min'
      (Finset.nonempty_iff_ne_empty.mpr nonempty) = first := by
    apply le_antisymm
    · exact Finset.min'_le _ first (by simp)
    · have member := Finset.min'_mem ({first, second} : Finset ℕ)
        (Finset.nonempty_iff_ne_empty.mpr nonempty)
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with equality | equality <;> omega
  have erased : ({first, second} : Finset ℕ).erase first = {second} := by
    ext site
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [basisWord, dif_neg nonempty, minimum]
  dsimp only
  rw [erased, basisWord_singleton]

theorem omega_field_expansion :
    Y omegaState =
      normal (-1) (currentField .c) (dividedDerivative 1 (currentField .b)) -
        (2 : ℂ) • normal (-1) (currentField .b)
          (dividedDerivative 1 (currentField .c)) := by
  rw [omegaState, map_sub, map_smul, Y_single, Y_single]
  simp only [one_smul]
  rw [basisWord_pair 1 2 (by decide), basisWord_pair 0 3 (by decide)]
  simp only [wordField, List.length_cons, List.length_nil, pow_zero, pow_one]
  rw [normal_right_identity, normal_right_identity]
  norm_num [siteField, kindAt, derivative_zero]

theorem derivative_b_modes (mode : ℤ) :
    (dividedDerivative 1 (currentField .b))[[mode]] =
      -(mode : ℂ) • b (mode - 2) := by
  rw [derivative_modes, currentField_modes]
  change integerBinomial (-mode - 1 + 1) 1 • b (mode - 1 - 1) = _
  have scalar : integerBinomial (-mode - 1 + 1) 1 = -(mode : ℂ) := by
    simp [integerBinomial] <;> push_cast <;> ring
  rw [scalar]
  change -(mode : ℂ) • b (mode - 1 - 1) = -(mode : ℂ) • b (mode - 2)
  rw [show mode - 1 - 1 = mode - 2 by omega]

theorem derivative_c_modes (mode : ℤ) :
    (dividedDerivative 1 (currentField .c))[[mode]] =
      -(mode : ℂ) • c (mode + 1) := by
  rw [derivative_modes, currentField_modes]
  change integerBinomial (-mode - 1 + 1) 1 • c (mode - 1 + 2) = _
  have scalar : integerBinomial (-mode - 1 + 1) 1 = -(mode : ℂ) := by
    simp [integerBinomial] <;> push_cast <;> ring
  rw [scalar]
  change -(mode : ℂ) • c (mode - 1 + 2) = -(mode : ℂ) • c (mode + 1)
  rw [show mode - 1 + 2 = mode + 1 by omega]

theorem derivative_b_boundary :
    (dividedDerivative 1 (currentField .b))[[0]] = 0 := by
  rw [derivative_b_modes]
  simp

theorem derivative_b_same_half_CAR (first second : ℤ)
    (sameHalf : (first < 0 ∧ second < 0) ∨ (0 ≤ first ∧ 0 ≤ second)) :
    (dividedDerivative 1 (currentField .b))[[first]] * (currentField .c)[[second]] +
        (currentField .c)[[second]] * (dividedDerivative 1 (currentField .b))[[first]] = 0 := by
  rw [derivative_b_modes, currentField_modes]
  change (-(first : ℂ) • b (first - 2)) * c (second + 2) +
    c (second + 2) * (-(first : ℂ) • b (first - 2)) = 0
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, ← smul_add, b_c]
  by_cases resonance : first + second = 0
  · have firstZero : first = 0 := by
      rcases sameHalf with negative | nonnegative <;> omega
    simp only [firstZero, Int.cast_zero, neg_zero, zero_smul]
  · simp only [show first - 2 + (second + 2) = first + second by omega,
      if_neg resonance, smul_zero]

theorem c_derivative_b_creator (physicalB physicalC : ℤ) (creatorC : physicalC ≤ 1) :
    c physicalC * (dividedDerivative 1 (currentField .b))[[physicalB + 2]] =
      ((physicalB + 2 : ℤ) : ℂ) • normalPair physicalB physicalC := by
  by_cases creatorB : physicalB ≤ -2
  · by_cases boundary : physicalB = -2
    · subst physicalB
      simp [derivative_b_boundary]
    · have law := derivative_b_same_half_CAR (physicalB + 2) (physicalC - 2)
        (Or.inl ⟨by omega, by omega⟩)
      have physicalLaw :
          (dividedDerivative 1 (currentField .b))[[physicalB + 2]] * c physicalC +
            c physicalC * (dividedDerivative 1 (currentField .b))[[physicalB + 2]] = 0 := by
        simpa only [currentField_modes, currentMode,
          show physicalC - 2 + 2 = physicalC by omega] using law
      have swap : c physicalC * (dividedDerivative 1 (currentField .b))[[physicalB + 2]] =
          -((dividedDerivative 1 (currentField .b))[[physicalB + 2]] * c physicalC) :=
        add_eq_zero_iff_eq_neg.mp (by simpa only [add_comm] using physicalLaw)
      rw [swap, derivative_b_modes,
        show physicalB + 2 - 2 = physicalB by omega,
        Algebra.smul_mul_assoc, normalPair, if_pos creatorB, ← Module.End.mul_eq_comp]
      change -(-((physicalB + 2 : ℤ) : ℂ) • (b physicalB * c physicalC)) = _
      simp only [neg_smul, neg_neg]
  · rw [derivative_b_modes, show physicalB + 2 - 2 = physicalB by omega,
      normalPair, if_neg creatorB, ← Module.End.mul_eq_comp]
    change c physicalC * (-((physicalB + 2 : ℤ) : ℂ) • b physicalB) =
      ((physicalB + 2 : ℤ) : ℂ) • (-(c physicalC * b physicalB))
    simp only [Algebra.mul_smul_comm, neg_smul, smul_neg, mul_neg]

theorem derivative_b_c_annihilator (physicalB physicalC : ℤ)
    (annihilatorC : 2 ≤ physicalC) :
    (dividedDerivative 1 (currentField .b))[[physicalB + 2]] * c physicalC =
      -((physicalB + 2 : ℤ) : ℂ) • normalPair physicalB physicalC := by
  by_cases creatorB : physicalB ≤ -2
  · rw [derivative_b_modes, show physicalB + 2 - 2 = physicalB by omega,
      normalPair, if_pos creatorB, ← Module.End.mul_eq_comp]
    change (-((physicalB + 2 : ℤ) : ℂ) • b physicalB) * c physicalC =
      -((physicalB + 2 : ℤ) : ℂ) • (b physicalB * c physicalC)
    exact Algebra.smul_mul_assoc _ _ _
  · have law := derivative_b_same_half_CAR (physicalB + 2) (physicalC - 2)
      (Or.inr ⟨by omega, by omega⟩)
    have physicalLaw :
        (dividedDerivative 1 (currentField .b))[[physicalB + 2]] * c physicalC +
          c physicalC * (dividedDerivative 1 (currentField .b))[[physicalB + 2]] = 0 := by
      simpa only [currentField_modes, currentMode,
        show physicalC - 2 + 2 = physicalC by omega] using law
    have swap := add_eq_zero_iff_eq_neg.mp physicalLaw
    rw [swap, derivative_b_modes, show physicalB + 2 - 2 = physicalB by omega,
      normalPair, if_neg creatorB, ← Module.End.mul_eq_comp]
    change -(c physicalC * (-((physicalB + 2 : ℤ) : ℂ) • b physicalB)) =
      -((physicalB + 2 : ℤ) : ℂ) • (-(c physicalC * b physicalB))
    simp only [Algebra.mul_smul_comm, neg_smul, smul_neg, neg_neg, mul_neg]

theorem derivative_b_c_creator (physicalB physicalC : ℤ) (creatorB : physicalB ≤ -2) :
    (dividedDerivative 1 (currentField .b))[[physicalB + 2]] * c physicalC =
      -((physicalB + 2 : ℤ) : ℂ) • normalPair physicalB physicalC := by
  rw [derivative_b_modes, show physicalB + 2 - 2 = physicalB by omega,
    normalPair, if_pos creatorB, ← Module.End.mul_eq_comp]
  change (-((physicalB + 2 : ℤ) : ℂ) • b physicalB) * c physicalC =
    -((physicalB + 2 : ℤ) : ℂ) • (b physicalB * c physicalC)
  exact Algebra.smul_mul_assoc _ _ _

theorem c_derivative_b_positive_half (physicalB physicalC : ℤ) (boundaryB : -2 ≤ physicalB) :
    (-1 : ℂ) • (c physicalC * (dividedDerivative 1 (currentField .b))[[physicalB + 2]]) =
      -((physicalB + 2 : ℤ) : ℂ) • normalPair physicalB physicalC := by
  by_cases boundary : physicalB = -2
  · subst physicalB
    simp [derivative_b_boundary]
  · have annihilatorB : ¬ physicalB ≤ -2 := by omega
    rw [derivative_b_modes, show physicalB + 2 - 2 = physicalB by omega,
      normalPair, if_neg annihilatorB, ← Module.End.mul_eq_comp]
    change (-1 : ℂ) • (c physicalC * (-((physicalB + 2 : ℤ) : ℂ) • b physicalB)) =
      -((physicalB + 2 : ℤ) : ℂ) • (-(c physicalC * b physicalB))
    simp only [Algebra.mul_smul_comm, neg_one_smul, neg_smul, smul_neg, neg_neg,
      mul_neg, one_smul]

theorem b_derivative_c_creator (physicalB physicalC : ℤ) (creatorB : physicalB ≤ -2) :
    b physicalB * (dividedDerivative 1 (currentField .c))[[physicalC - 1]] =
      ((1 - physicalC : ℤ) : ℂ) • normalPair physicalB physicalC := by
  rw [derivative_c_modes, show physicalC - 1 + 1 = physicalC by omega,
    normalPair, if_pos creatorB, ← Module.End.mul_eq_comp]
  change b physicalB * (-((physicalC - 1 : ℤ) : ℂ) • c physicalC) =
    ((1 - physicalC : ℤ) : ℂ) • (b physicalB * c physicalC)
  rw [Algebra.mul_smul_comm]
  congr 1
  push_cast
  ring

theorem derivative_c_b_annihilator (physicalB physicalC : ℤ)
    (annihilatorB : ¬ physicalB ≤ -2) :
    (-1 : ℂ) • ((dividedDerivative 1 (currentField .c))[[physicalC - 1]] * b physicalB) =
      ((1 - physicalC : ℤ) : ℂ) • normalPair physicalB physicalC := by
  rw [derivative_c_modes, show physicalC - 1 + 1 = physicalC by omega,
    normalPair, if_neg annihilatorB, ← Module.End.mul_eq_comp]
  change (-1 : ℂ) • ((-((physicalC - 1 : ℤ) : ℂ) • c physicalC) * b physicalB) =
    ((1 - physicalC : ℤ) : ℂ) • (-(c physicalC * b physicalB))
  rw [Algebra.smul_mul_assoc]
  rw [smul_smul, smul_neg, ← neg_smul]
  congr 1
  push_cast
  ring

theorem normal_odd_modes (left right : VertexOperator ℂ Carrier) (mode : ℤ) (vector : Carrier) :
    ((normal (-1) left right)[[mode]]) vector =
      (∑ᶠ offset : ℕ, (left[[-(offset : ℤ) - 1]]) ((right[[mode + offset]]) vector)) +
        (∑ᶠ offset : ℕ, (-1 : ℂ) •
          (right[[mode - offset - 1]]) ((left[[offset]]) vector)) := by
  have indices (offset : ℕ) : mode - (offset : ℤ) - 1 = mode - 1 - offset := by omega
  have finite : Function.HasFiniteSupport (fun offset : ℕ =>
      (right[[mode - offset - 1]]) ((left[[offset]]) vector)) := by
    simpa only [zero_add, ← indices] using forward_finite right left (mode - 1) 0 vector
  rw [normal_modes, ← smul_finsum' (-1 : ℂ) finite]

def comparisonRadius (mode : ℤ) (vector : Carrier) : ℤ :=
  cutoff mode vector + (mode.natAbs : ℤ) + 4

def cbWeight (mode index : ℤ) : ℂ := ((mode + index + 2 : ℤ) : ℂ)

def dbWeight (mode index : ℤ) : ℂ := -((mode + index + 2 : ℤ) : ℂ)

def dcWeight (index : ℤ) : ℂ := ((index + 1 : ℤ) : ℂ)

theorem comparisonRadius_encloses_cutoff (mode : ℤ) (vector : Carrier) :
    -comparisonRadius mode vector ≤ -cutoff mode vector ∧
      cutoff mode vector ≤ comparisonRadius mode vector := by
  have nonnegative := Int.natCast_nonneg mode.natAbs
  dsimp only [comparisonRadius]
  omega

theorem comparisonRadius_contains (mode : ℤ) (vector : Carrier) (split : ℤ)
    (lower : -(mode.natAbs : ℤ) - 4 ≤ split)
    (upper : split ≤ (mode.natAbs : ℤ) + 4) :
    -comparisonRadius mode vector ≤ split ∧ split ≤ comparisonRadius mode vector := by
  have occupiedNonnegative : (0 : ℤ) ≤ (((occupied vector).sup id : ℕ) : ℤ) :=
    Int.natCast_nonneg _
  have absoluteNonnegative := Int.natCast_nonneg mode.natAbs
  dsimp only [comparisonRadius, cutoff]
  omega

theorem weighted_pair_support (coefficient : ℤ → ℂ) (mode : ℤ) (vector : Carrier) :
    Function.support (fun index : ℤ => coefficient index •
      normalPair (mode + index) (-index) vector) ⊆
        Set.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector) := by
  intro index member
  have pairMember : index ∈ Function.support
      (fun index : ℤ => normalPair (mode + index) (-index) vector) := by
    intro zeroPair
    exact member (by simp only [zeroPair, smul_zero])
  have pairBound := normal_pair_support_interval mode vector pairMember
  have enclosure := comparisonRadius_encloses_cutoff mode vector
  simp only [Set.mem_Icc] at pairBound ⊢
  omega

theorem normal_C_dB_interval (mode : ℤ) (vector : Carrier) :
    ((normal (-1) (currentField .c) (dividedDerivative 1 (currentField .b)))[[mode + 1]]) vector =
      ∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
        cbWeight mode index • normalPair (mode + index) (-index) vector := by
  have firstTerm (offset : ℕ) :
      ((currentField .c)[[-(offset : ℤ) - 1]])
          (((dividedDerivative 1 (currentField .b))[[mode + 1 + offset]]) vector) =
        cbWeight mode (-2 + 1 + offset) •
          normalPair (mode + (-2 + 1 + offset)) (-(-2 + 1 + offset)) vector := by
    have law := c_derivative_b_creator (mode + offset - 1) (1 - offset) (by omega)
    simpa only [currentField_modes, currentMode, Module.End.mul_apply, LinearMap.smul_apply,
      cbWeight, show -(offset : ℤ) - 1 + 2 = 1 - offset by omega,
      show mode + (-2 + 1 + (offset : ℤ)) = mode + offset - 1 by omega,
      show -(-2 + 1 + (offset : ℤ)) = 1 - offset by omega,
      show mode + (offset : ℤ) - 1 + 2 = mode + 1 + offset by omega]
      using congrArg (fun operator : Module.End ℂ Carrier => operator vector) law
  have secondTerm (offset : ℕ) :
      (-1 : ℂ) • ((dividedDerivative 1 (currentField .b))[[mode + 1 - offset - 1]])
          (((currentField .c)[[offset]]) vector) =
        cbWeight mode (-2 - offset) •
          normalPair (mode + (-2 - offset)) (-(-2 - offset)) vector := by
    have law := derivative_b_c_annihilator (mode - offset - 2) (offset + 2) (by omega)
    simpa only [currentField_modes, currentMode, Module.End.mul_apply, LinearMap.smul_apply,
      cbWeight, neg_one_smul, neg_smul, neg_neg, one_smul, LinearMap.neg_apply,
      show mode + (-2 - (offset : ℤ)) = mode - offset - 2 by omega,
      show -(-2 - (offset : ℤ)) = offset + 2 by omega,
      show mode + 1 - (offset : ℤ) - 1 = mode - offset by omega,
      show mode - (offset : ℤ) - 2 + 2 = mode - offset by omega]
      using congrArg (fun operator : Module.End ℂ Carrier => (-1 : ℂ) • operator vector) law
  rw [normal_odd_modes]
  simp_rw [firstTerm, secondTerm]
  rw [add_comm]
  have absoluteNonnegative := Int.natCast_nonneg mode.natAbs
  have splitBounds := comparisonRadius_contains mode vector (-2) (by omega) (by omega)
  exact split_common_interval
    (fun index : ℤ => cbWeight mode index • normalPair (mode + index) (-index) vector)
    (-comparisonRadius mode vector) (comparisonRadius mode vector) (-2)
    splitBounds.1 splitBounds.2 (weighted_pair_support (cbWeight mode) mode vector)

theorem normal_dB_C_interval (mode : ℤ) (vector : Carrier) :
    ((normal (-1) (dividedDerivative 1 (currentField .b)) (currentField .c))[[mode + 1]]) vector =
      ∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
        dbWeight mode index • normalPair (mode + index) (-index) vector := by
  have firstTerm (offset : ℕ) :
      ((dividedDerivative 1 (currentField .b))[[-(offset : ℤ) - 1]])
          (((currentField .c)[[mode + 1 + offset]]) vector) =
        dbWeight mode (-mode - 3 - offset) •
          normalPair (mode + (-mode - 3 - offset)) (-(-mode - 3 - offset)) vector := by
    have law := derivative_b_c_creator (-(offset : ℤ) - 3) (mode + offset + 3) (by omega)
    simpa only [currentField_modes, currentMode, Module.End.mul_apply, LinearMap.smul_apply,
      dbWeight, show mode + (-mode - 3 - (offset : ℤ)) = -(offset : ℤ) - 3 by omega,
      show -(-mode - 3 - (offset : ℤ)) = mode + offset + 3 by omega,
      show -(offset : ℤ) - 3 + 2 = -(offset : ℤ) - 1 by omega,
      show mode + 1 + (offset : ℤ) + 2 = mode + offset + 3 by omega]
      using congrArg (fun operator : Module.End ℂ Carrier => operator vector) law
  have secondTerm (offset : ℕ) :
      (-1 : ℂ) • ((currentField .c)[[mode + 1 - offset - 1]])
          (((dividedDerivative 1 (currentField .b))[[offset]]) vector) =
        dbWeight mode (-mode - 3 + 1 + offset) •
          normalPair (mode + (-mode - 3 + 1 + offset)) (-(-mode - 3 + 1 + offset)) vector := by
    have law := c_derivative_b_positive_half ((offset : ℤ) - 2) (mode - offset + 2) (by omega)
    simpa only [currentField_modes, currentMode, Module.End.mul_apply, LinearMap.smul_apply,
      dbWeight, show mode + (-mode - 3 + 1 + (offset : ℤ)) = offset - 2 by omega,
      show -(-mode - 3 + 1 + (offset : ℤ)) = mode - offset + 2 by omega,
      show (offset : ℤ) - 2 + 2 = offset by omega,
      show mode + 1 - (offset : ℤ) - 1 + 2 = mode - offset + 2 by omega]
      using congrArg (fun operator : Module.End ℂ Carrier => operator vector) law
  rw [normal_odd_modes]
  simp_rw [firstTerm, secondTerm]
  have absoluteUpper : mode ≤ (mode.natAbs : ℤ) := Int.le_natAbs
  have absoluteLower : -(mode.natAbs : ℤ) ≤ mode := by
    have negativeUpper : -mode ≤ (mode.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -mode))
    omega
  have splitBounds := comparisonRadius_contains mode vector (-mode - 3) (by omega) (by omega)
  exact split_common_interval
    (fun index : ℤ => dbWeight mode index • normalPair (mode + index) (-index) vector)
    (-comparisonRadius mode vector) (comparisonRadius mode vector) (-mode - 3)
    splitBounds.1 splitBounds.2 (weighted_pair_support (dbWeight mode) mode vector)

theorem normal_B_dC_interval (mode : ℤ) (vector : Carrier) :
    ((normal (-1) (currentField .b) (dividedDerivative 1 (currentField .c)))[[mode + 1]]) vector =
      ∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
        dcWeight index • normalPair (mode + index) (-index) vector := by
  have firstTerm (offset : ℕ) :
      ((currentField .b)[[-(offset : ℤ) - 1]])
          (((dividedDerivative 1 (currentField .c))[[mode + 1 + offset]]) vector) =
        dcWeight (-mode - 2 - offset) •
          normalPair (mode + (-mode - 2 - offset)) (-(-mode - 2 - offset)) vector := by
    have law := b_derivative_c_creator (-(offset : ℤ) - 2) (mode + offset + 2) (by omega)
    simpa only [currentField_modes, currentMode, Module.End.mul_apply, LinearMap.smul_apply,
      dcWeight, show -(offset : ℤ) - 1 - 1 = -(offset : ℤ) - 2 by omega,
      show mode + (-mode - 2 - (offset : ℤ)) = -(offset : ℤ) - 2 by omega,
      show -(-mode - 2 - (offset : ℤ)) = mode + offset + 2 by omega,
      show mode + (offset : ℤ) + 2 - 1 = mode + 1 + offset by omega,
      show (-mode - 2 - (offset : ℤ)) + 1 = 1 - (mode + offset + 2) by omega]
      using congrArg (fun operator : Module.End ℂ Carrier => operator vector) law
  have secondTerm (offset : ℕ) :
      (-1 : ℂ) • ((dividedDerivative 1 (currentField .c))[[mode + 1 - offset - 1]])
          (((currentField .b)[[offset]]) vector) =
        dcWeight (-mode - 2 + 1 + offset) •
          normalPair (mode + (-mode - 2 + 1 + offset)) (-(-mode - 2 + 1 + offset)) vector := by
    have law := derivative_c_b_annihilator ((offset : ℤ) - 1) (mode - offset + 1) (by omega)
    simpa only [currentField_modes, currentMode, Module.End.mul_apply, LinearMap.smul_apply,
      dcWeight, show mode + (-mode - 2 + 1 + (offset : ℤ)) = offset - 1 by omega,
      show -(-mode - 2 + 1 + (offset : ℤ)) = mode - offset + 1 by omega,
      show mode + 1 - (offset : ℤ) - 1 = mode - offset by omega,
      show mode - (offset : ℤ) + 1 - 1 = mode - offset by omega,
      show (-mode - 2 + 1 + (offset : ℤ)) + 1 = 1 - (mode - offset + 1) by omega]
      using congrArg (fun operator : Module.End ℂ Carrier => operator vector) law
  rw [normal_odd_modes]
  simp_rw [firstTerm, secondTerm]
  have absoluteUpper : mode ≤ (mode.natAbs : ℤ) := Int.le_natAbs
  have absoluteLower : -(mode.natAbs : ℤ) ≤ mode := by
    have negativeUpper : -mode ≤ (mode.natAbs : ℤ) := by
      simpa using (Int.le_natAbs (a := -mode))
    omega
  have splitBounds := comparisonRadius_contains mode vector (-mode - 2) (by omega) (by omega)
  exact split_common_interval
    (fun index : ℤ => dcWeight index • normalPair (mode + index) (-index) vector)
    (-comparisonRadius mode vector) (comparisonRadius mode vector) (-mode - 2)
    splitBounds.1 splitBounds.2 (weighted_pair_support dcWeight mode vector)

theorem normal_C_dB_swap :
    normal (-1) (currentField .c) (dividedDerivative 1 (currentField .b)) =
      -normal (-1) (dividedDerivative 1 (currentField .b)) (currentField .c) := by
  apply HVertexOperator.coeff_inj
  funext power
  apply LinearMap.ext
  intro vector
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  let mode : ℤ := -power - 2
  have modeIdentity : -power - 1 = mode + 1 := by dsimp only [mode]; omega
  rw [modeIdentity]
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply]
  rw [normal_C_dB_interval, normal_dB_C_interval, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro index member
  simp only [cbWeight, dbWeight, neg_smul, neg_neg]

theorem conformal_modes (mode : ℤ) :
    (Y omegaState)[[mode + 1]] = L (K := ℂ) mode := by
  rw [omega_field_expansion, normal_C_dB_swap]
  apply LinearMap.ext
  intro vector
  simp only [map_sub, map_neg, map_smul, Pi.sub_apply, Pi.neg_apply,
    Pi.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.smul_apply]
  rw [normal_dB_C_interval, normal_B_dC_interval]
  have enclosure := comparisonRadius_encloses_cutoff mode vector
  rw [L_interval_sum mode vector (-comparisonRadius mode vector) (comparisonRadius mode vector)
    enclosure.1 enclosure.2]
  calc
    -(∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
        dbWeight mode index • normalPair (mode + index) (-index) vector) -
        (2 : ℂ) • (∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
          dcWeight index • normalPair (mode + index) (-index) vector) =
      ∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
        (-(dbWeight mode index • normalPair (mode + index) (-index) vector) -
          (2 : ℂ) • (dcWeight index • normalPair (mode + index) (-index) vector)) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.smul_sum]
    _ = ∑ index ∈ Finset.Icc (-comparisonRadius mode vector) (comparisonRadius mode vector),
        (mode - index : ℂ) • normalPair (mode + index) (-index) vector := by
      apply Finset.sum_congr rfl
      intro index member
      rw [← neg_smul, smul_smul, ← sub_smul]
      congr 1
      dsimp only [dbWeight, dcWeight]
      push_cast
      ring

end
end D5.S3.VertexAlgebra.BcGhostActualConformalState
