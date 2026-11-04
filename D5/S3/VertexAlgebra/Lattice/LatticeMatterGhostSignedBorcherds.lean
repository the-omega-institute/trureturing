/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostSignedBorcherds
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostSignedBorcherds
   mirror-E: none(waiver:original-tensor-borcherds-support)
   anchors: []
   utility: none
   digest: Pointwise action supports and the tensor Borcherds Pascal recurrence. -/

/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
The completed tensor support/Pascal source supplies these arguments.
Coefficient conventions follow BcGhostStateFieldIterate and BcGhostBorcherds,
with the original coupled carrier and field retained throughout.
All theorem helpers are consumed by the unrestricted Borcherds proof or
its support/Pascal derivation; none is separate mathematical audit content.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
import D5.S3.VertexAlgebra.BinomialKernelDelta
import D5.S3.VertexAlgebra.StateFieldResidueReconstruction

/-! Finite action supports and Pascal propagation for the original tensor modes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator
open D5.S3.VertexAlgebra.StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.VertexAlgebra.LatticeMatterGhostStateField

namespace D5.S3.VertexAlgebra.LatticeMatterGhostSignedBorcherds

open LatticeGeneratingFieldLocality (LatticeData)

noncomputable section

abbrev State (D : LatticeData) := LatticeMatterGhostCoupling.State D
abbrev mu_D (D : LatticeData) (a : State D) (n : ℤ) (b : State D) : State D :=
  ((LatticeMatterGhostStateField.Y D a)[[n]]) b

/-- The three actual coupled coefficient families. -/
def jacobiLeftTerm (D : LatticeData) (p q r : ℤ)
    (a b c : State D) (i : ℕ) : State D :=
  integerBinomial p i • mu_D D (mu_D D a (r + i) b) (p + q - i) c

def jacobiRightFirstTerm (D : LatticeData) (p q r : ℤ)
    (a b c : State D) (i : ℕ) : State D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    mu_D D a (p + r - i) (mu_D D b (q + i) c)

def jacobiRightSecondTerm (D : LatticeData) (s : ℂ) (p q r : ℤ)
    (a b c : State D) (i : ℕ) : State D :=
  (((-1 : ℂ)^i) * integerBinomial r i) •
    ((epsilon r * s) • mu_D D b (q + r - i) (mu_D D a (p + i) c))

/-- The signed discrepancy used by the supported Pascal recurrence. -/
def discrepancy (D : LatticeData) (s : ℂ) (a b c : State D)
    (p q r : ℤ) : State D :=
  (∑ᶠ i : ℕ, jacobiLeftTerm D p q r a b c i) -
    (∑ᶠ i : ℕ, jacobiRightFirstTerm D p q r a b c i) +
    (∑ᶠ i : ℕ, jacobiRightSecondTerm D s p q r a b c i)

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem left_support (D : LatticeData) (a b c : State D)
    (p q r : ℤ) :
    Function.HasFiniteSupport (jacobiLeftTerm D p q r a b c) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm
    ((LatticeMatterGhostStateField.Y D a) b)).order - r).toNat, ?_⟩
  intro i hi
  contrapose! hi
  rw [Function.notMem_support]
  have vanish : mu_D D a (r + i) b = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  dsimp only [jacobiLeftTerm]
  rw [vanish]
  simp [mu_D]

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem right_first_support (D : LatticeData) (a b c : State D)
    (p q r : ℤ) :
    Function.HasFiniteSupport (jacobiRightFirstTerm D p q r a b c) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm
    ((LatticeMatterGhostStateField.Y D b) c)).order - q).toNat, ?_⟩
  intro i hi
  contrapose! hi
  rw [Function.notMem_support]
  have vanish : mu_D D b (q + i) c = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  dsimp only [jacobiRightFirstTerm]
  rw [vanish]
  simp [mu_D]

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
/-- The p=0 left sum is the actual coupled mode product, by a genuine
pointwise finsum reduction. -/
private theorem p_zero_left (D : LatticeData) (a b c : State D)
    (q r : ℤ) :
    (∑ᶠ i : ℕ, jacobiLeftTerm D 0 q r a b c i) =
      mu_D D (mu_D D a r b) q c := by
  rw [finsum_eq_single _ 0]
  · simp [jacobiLeftTerm, integerBinomial, mu_D]
  · intro i hi
    simp [jacobiLeftTerm, integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem splitSum {D : LatticeData} (term : ℕ → State D)
    (finite : Function.HasFiniteSupport term) :
    (∑ᶠ i : ℕ, term i) = term 0 + ∑ᶠ i : ℕ, term (i + 1) := by
  let zeroSucc : Option ℕ ≃ ℕ := {
    toFun value := match value with | none => 0 | some i => i + 1
    invFun value := match value with | 0 => none | i + 1 => some i
    left_inv value := by cases value <;> rfl
    right_inv value := by cases value <;> rfl }
  rw [← finsum_comp_equiv zeroSucc, finsum_option]
  · rfl
  · exact finite.fun_comp_of_injective (g := fun i : ℕ => i + 1)
      (fun i j h => Nat.add_right_cancel h)

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem sumPascal {D : LatticeData} (parameter : ℤ) (sequence : ℕ → State D)
    (finite : Function.HasFiniteSupport sequence) :
    (∑ᶠ i : ℕ, integerBinomial (parameter + 1) i • sequence i) =
      (∑ᶠ i : ℕ, integerBinomial parameter i • sequence i) +
      ∑ᶠ i : ℕ, integerBinomial parameter i • sequence (i + 1) := by
  have tailFinite := finite.fun_comp_of_injective
    (g := fun i : ℕ => i + 1) (fun i j h => Nat.add_right_cancel h)
  have nextFinite : Function.HasFiniteSupport
      (fun i : ℕ => integerBinomial (parameter + 1) i • sequence i) :=
    finite.smul_right (integerBinomial (parameter + 1))
  have currentFinite : Function.HasFiniteSupport
      (fun i : ℕ => integerBinomial parameter i • sequence i) :=
    finite.smul_right (integerBinomial parameter)
  rw [splitSum _ nextFinite, splitSum _ currentFinite]
  have chooseZero (n : ℤ) : integerBinomial n 0 = 1 := by
    simp [integerBinomial]
  simp only [chooseZero, one_smul]
  have pascal (i : ℕ) :
      integerBinomial (parameter + 1) (i + 1) =
        integerBinomial parameter i + integerBinomial parameter (i + 1) := by
    unfold integerBinomial
    rw [Ring.choose_succ_succ, Int.cast_add]
  simp_rw [pascal, add_smul]
  have firstTail : Function.HasFiniteSupport
      (fun i : ℕ => integerBinomial parameter i • sequence (i + 1)) :=
    tailFinite.smul_right (integerBinomial parameter)
  have secondTail : Function.HasFiniteSupport
      (fun i : ℕ => integerBinomial parameter (i + 1) • sequence (i + 1)) :=
    tailFinite.smul_right (fun i => integerBinomial parameter (i + 1))
  rw [finsum_add_distrib firstTail secondTail]
  abel

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem weightedPascal {D : LatticeData} (parameter : ℤ) (sequence : ℕ → State D)
    (finite : Function.HasFiniteSupport sequence) :
    (∑ᶠ i : ℕ,
      (((-1 : ℂ)^i) * integerBinomial (parameter + 1) i) • sequence i) =
      (∑ᶠ i : ℕ,
        (((-1 : ℂ)^i) * integerBinomial parameter i) • sequence i) -
      ∑ᶠ i : ℕ,
        (((-1 : ℂ)^i) * integerBinomial parameter i) • sequence (i + 1) := by
  let weight (n : ℤ) (i : ℕ) : ℂ := (-1 : ℂ)^i * integerBinomial n i
  have tailFinite := finite.fun_comp_of_injective
    (g := fun i : ℕ => i + 1) (fun i j h => Nat.add_right_cancel h)
  have nextFinite : Function.HasFiniteSupport
      (fun i : ℕ => weight (parameter + 1) i • sequence i) :=
    finite.smul_right (weight (parameter + 1))
  have currentFinite : Function.HasFiniteSupport (fun i : ℕ => weight parameter i • sequence i) :=
    finite.smul_right (weight parameter)
  have chooseZero (n : ℤ) : integerBinomial n 0 = 1 := by simp [integerBinomial]
  have weightZero (n : ℤ) : weight n 0 = 1 := by simp [weight, chooseZero]
  have pascal (i : ℕ) : weight (parameter + 1) (i + 1) =
      weight parameter (i + 1) - weight parameter i := by
    exact BinomialKernelDelta.chooseSign_pascal parameter i
  rw [splitSum _ nextFinite, splitSum _ currentFinite]
  simp only [weightZero, one_smul]
  simp_rw [pascal, sub_smul]
  have firstTail : Function.HasFiniteSupport
      (fun i : ℕ => weight parameter (i + 1) • sequence (i + 1)) :=
    tailFinite.smul_right (fun i => weight parameter (i + 1))
  have secondTail : Function.HasFiniteSupport
      (fun i : ℕ => weight parameter i • sequence (i + 1)) :=
    tailFinite.smul_right (weight parameter)
  rw [finsum_sub_distrib firstTail secondTail]
  abel

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem first_sequence_finite (D : LatticeData) (a b c : State D)
    (start finish r : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      mu_D D (mu_D D a (r + i) b) (start + finish - i) c) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm
    ((LatticeMatterGhostStateField.Y D a) b)).order - r).toNat, ?_⟩
  intro i hi
  contrapose! hi
  rw [Function.notMem_support]
  have vanish : mu_D D a (r + i) b = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  rw [vanish]
  simp [mu_D]

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem second_sequence_finite (D : LatticeData) (a b c : State D)
    (start finish parameter : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      mu_D D a (start + parameter - i)
        (mu_D D b (finish + i) c)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm
    ((LatticeMatterGhostStateField.Y D b) c)).order - finish).toNat, ?_⟩
  intro i hi
  contrapose! hi
  rw [Function.notMem_support]
  have vanish : mu_D D b (finish + i) c = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  rw [vanish]
  simp [mu_D]

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
private theorem third_sequence_finite (D : LatticeData) (a b c : State D)
    (start finish parameter : ℤ) :
    Function.HasFiniteSupport (fun i : ℕ =>
      mu_D D b (finish + parameter - i)
        (mu_D D a (start + i) c)) := by
  refine BddAbove.finite (bddAbove_def.mpr ?_)
  refine ⟨(-((HahnModule.of ℂ).symm
    ((LatticeMatterGhostStateField.Y D a) c)).order - start).toNat, ?_⟩
  intro i hi
  contrapose! hi
  rw [Function.notMem_support]
  have vanish : mu_D D a (start + i) c = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  rw [vanish]
  simp [mu_D]

set_option maxHeartbeats 4000000 in
-- Retain the supplier budget for supported coefficient and scalar normalization.
/-- The actual coupled three-coordinate Pascal relation, including its
signed reverse term and all finite-support premises discharged on State D. -/
private theorem coupled_discrepancy_recurrence
    (D : LatticeData) (s : ℂ) (a b c : State D)
    (p q r : ℤ) :
    discrepancy D s a b c (p + 1) q r =
      discrepancy D s a b c p (q + 1) r +
        discrepancy D s a b c p q (r + 1) := by
  let weight (n : ℤ) (i : ℕ) : ℂ := (-1 : ℂ)^i * integerBinomial n i
  have leftLaw :
      (∑ᶠ i : ℕ, jacobiLeftTerm D (p + 1) q r a b c i) =
        (∑ᶠ i : ℕ, jacobiLeftTerm D p (q + 1) r a b c i) +
          ∑ᶠ i : ℕ, jacobiLeftTerm D p q (r + 1) a b c i := by
    let sequence (i : ℕ) := mu_D D (mu_D D a (r + i) b)
      (p + 1 + q - i) c
    have initial (i : ℕ) : jacobiLeftTerm D (p + 1) q r a b c i =
        integerBinomial (p + 1) i • sequence i := by rfl
    have current (i : ℕ) : jacobiLeftTerm D p (q + 1) r a b c i =
        integerBinomial p i • sequence i := by
      dsimp [jacobiLeftTerm, sequence]
      rw [show p + (q + 1) - (i : ℤ) = p + 1 + q - i by omega]
    have shifted (i : ℕ) : jacobiLeftTerm D p q (r + 1) a b c i =
        integerBinomial p i • sequence (i + 1) := by
      dsimp [jacobiLeftTerm, sequence]
      rw [show r + ((i : ℤ) + 1) = r + 1 + i by omega,
        show p + 1 + q - ((i : ℤ) + 1) = p + q - i by omega]
    simp_rw [initial, current, shifted]
    exact sumPascal p sequence
      (first_sequence_finite D a b c (p + 1) q r)
  have firstRightLaw :
      (∑ᶠ i : ℕ, jacobiRightFirstTerm D (p + 1) q r a b c i) =
        (∑ᶠ i : ℕ, jacobiRightFirstTerm D p (q + 1) r a b c i) +
          ∑ᶠ i : ℕ, jacobiRightFirstTerm D p q (r + 1) a b c i := by
    let sequence (i : ℕ) := mu_D D a (p + (r + 1) - i)
      (mu_D D b (q + i) c)
    have initial (i : ℕ) : jacobiRightFirstTerm D (p + 1) q r a b c i =
        weight r i • sequence i := by
      dsimp [jacobiRightFirstTerm, weight, sequence]
      rw [show p + 1 + r = p + (r + 1) by omega]
    have current (i : ℕ) : jacobiRightFirstTerm D p q (r + 1) a b c i =
        weight (r + 1) i • sequence i := by rfl
    have shifted (i : ℕ) : jacobiRightFirstTerm D p (q + 1) r a b c i =
        weight r i • sequence (i + 1) := by
      dsimp [jacobiRightFirstTerm, weight, sequence]
      rw [show p + (r + 1) - ((i : ℤ) + 1) = p + r - i by omega,
        show q + ((i : ℤ) + 1) = q + 1 + i by omega]
    simp_rw [initial, current, shifted]
    exact (sub_eq_iff_eq_add').mp
      (weightedPascal r sequence
        (second_sequence_finite D a b c p q (r + 1))).symm
  have epsilon_succ : epsilon (r + 1) = -epsilon r := by
    rw [epsilon, epsilon, zpow_add₀ (by norm_num)]
    norm_num
  have secondRightLaw :
      (∑ᶠ i : ℕ, jacobiRightSecondTerm D s (p + 1) q r a b c i) =
        (∑ᶠ i : ℕ, jacobiRightSecondTerm D s p (q + 1) r a b c i) +
          ∑ᶠ i : ℕ, jacobiRightSecondTerm D s p q (r + 1) a b c i := by
    let sequence (i : ℕ) := mu_D D b (q + (r + 1) - i)
      (mu_D D a (p + i) c)
    have finiteSequence : Function.HasFiniteSupport sequence :=
      third_sequence_finite D a b c p q (r + 1)
    have initial (i : ℕ) : jacobiRightSecondTerm D s p (q + 1) r a b c i =
        (epsilon r * s) • (weight r i • sequence i) := by
      dsimp [jacobiRightSecondTerm, weight, sequence]
      rw [show q + 1 + r = q + (r + 1) by omega, smul_comm]
    have current (i : ℕ) : jacobiRightSecondTerm D s p q (r + 1) a b c i =
        -(epsilon r * s) • (weight (r + 1) i • sequence i) := by
      dsimp [jacobiRightSecondTerm, weight, sequence]
      rw [epsilon_succ, smul_comm, neg_mul]
    have shifted (i : ℕ) : jacobiRightSecondTerm D s (p + 1) q r a b c i =
        (epsilon r * s) • (weight r i • sequence (i + 1)) := by
      dsimp [jacobiRightSecondTerm, weight, sequence]
      rw [show q + (r + 1) - ((i : ℤ) + 1) = q + r - i by omega,
        show p + ((i : ℤ) + 1) = p + 1 + i by omega, smul_comm]
    simp_rw [initial, current, shifted, ← smul_finsum]
    rw [weightedPascal r sequence finiteSequence]
    module
  unfold discrepancy
  rw [leftLaw, firstRightLaw, secondRightLaw]
  abel

end
end D5.S3.VertexAlgebra.LatticeMatterGhostSignedBorcherds
