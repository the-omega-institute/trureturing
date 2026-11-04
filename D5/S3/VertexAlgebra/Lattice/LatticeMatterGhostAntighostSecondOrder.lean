/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
This port preserves the attribution of the field and residue suppliers to
ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea,
VertexAlg/VertexBasic/VertexOperator.lean. The tensor-field construction follows
Bakalov--Kac, math/0402315v1, section 4.1. The ghost state and physical modes
remain those of CountableOccupationFock, BcGhostFock and BcGhostStateField;
Mathlib's Apache-2.0 tensor, finite-support sum and Ring.choose calculus is reused.

Proof provenance: the completed 20261012 OriginalTopologicalApplications source,
lines 238--317 (finite mode-zero/one reductions) and 329--361 (actual B0 defect
and second order), ported to the current full LatticeMatterGhostCoupling.State,
current Y/parity and unchanged ghostB. Historical completion is not current
native acceptance. The completed current tensor Borcherds supplier is reused;
its canonical delivery is pending. This candidate is source-only and uncompiled.
No novelty, source-normalization completion, kernel acceptance or complete
string-theory claim is made. Quotient and cohomology consumers are outside this file.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeMatterGhostStateField (Y parity stateField_parity)
open LatticeMatterGhostSignedBorcherds
  (mu_D jacobiLeftTerm jacobiRightFirstTerm)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.Quantum.Fermionic
open private left_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private homogeneous_borcherds tensorLeft tensorForward tensorReverse reverseTerm from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds
open private p_zero_left from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostSignedBorcherds

noncomputable section

variable (D : LatticeData)

/-- The actual antighost state: lattice vacuum tensor the singleton occupation. -/
def beta : State D :=
  LatticeAllStateField.vacuum D ⊗ₜ[ℂ] CountableOccupationFock.ket {0}

theorem beta_odd : parity D (beta D) = -(beta D) := by
  simp [beta, LatticeMatterGhostStateField.parity, parity_ket,
    TensorProduct.tmul_neg]

/-- Physical b(r) is vertex mode r+1; in particular physical b(0) is mode one. -/
theorem beta_modes (n : ℤ) : ((Y D (beta D))[[n]]) = ghostB D (n - 1) := by
  rw [beta, left_vacuum_modes, BcGhostStateField.stateField_creation.2.2.2.1]
  rfl

theorem beta_mode_one : ((Y D (beta D))[[1]]) = ghostB D 0 := by
  simpa only [sub_self] using beta_modes D 1

theorem beta_mode_zero : ((Y D (beta D))[[0]]) = ghostB D (-1) := by
  simpa only [zero_sub] using beta_modes D 0

/-- The actual vertex mode minus one, on unrestricted original states. -/
def mu (a c : State D) : State D := ((Y D a)[[-1]]) c

-- For r=0, each right-hand coefficient family has support contained in {0}.
-- These reductions are used at first indices 0 and 1 below.
private theorem forward_zero_parameter (a c d : State D) (m : ℤ) :
    tensorForward D m (-1) 0 a c d =
      mu_D D a m (mu_D D c (-1) d) := by
  unfold tensorForward
  rw [finsum_eq_single _ 0]
  · simp [jacobiRightFirstTerm, integerBinomial]
  · intro i different
    simp [jacobiRightFirstTerm, integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]

private theorem reverse_zero_parameter (a c d : State D) (m : ℤ) :
    tensorReverse D m (-1) 0 a c d =
      mu_D D c (-1) (mu_D D a m d) := by
  unfold tensorReverse
  rw [finsum_eq_single _ 0]
  · simp [reverseTerm, integerBinomial]
  · intro i different
    simp [reverseTerm, integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero different)]

/-- The zero mode of an actual parity eigenstate derives the minus-one product. -/
theorem zero_mode_derivation (p q : ℕ) (a c d : State D)
    (ha : parity D a = (-1 : ℂ)^p • a)
    (hc : parity D c = (-1 : ℂ)^q • c) :
    ((Y D a)[[0]]) (mu D c d) =
      mu D (((Y D a)[[0]]) c) d +
        (-1 : ℂ)^(p * q) • mu D c (((Y D a)[[0]]) d) := by
  have law := homogeneous_borcherds D a c d p q ha hc 0 (-1) 0
  dsimp only [tensorLeft] at law
  rw [p_zero_left, forward_zero_parameter, reverse_zero_parameter] at law
  simp only [epsilon, zpow_zero, one_mul] at law
  exact (eq_sub_iff_add_eq.mp law).symm

/-- The first mode has the additional zero-mode term, with the actual Koszul sign. -/
theorem one_mode_commutator (p q : ℕ) (a c d : State D)
    (ha : parity D a = (-1 : ℂ)^p • a)
    (hc : parity D c = (-1 : ℂ)^q • c) :
    ((Y D a)[[1]]) (mu D c d) =
      mu D (((Y D a)[[1]]) c) d +
        (-1 : ℂ)^(p * q) • mu D c (((Y D a)[[1]]) d) +
        ((Y D (((Y D a)[[0]]) c))[[0]]) d := by
  classical
  have law := homogeneous_borcherds D a c d p q ha hc 1 (-1) 0
  have leftValue : tensorLeft D 1 (-1) 0 a c d =
      mu_D D (mu_D D a 0 c) 0 d + mu_D D (mu_D D a 1 c) (-1) d := by
    unfold tensorLeft
    rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
    · simp [jacobiLeftTerm, integerBinomial, Ring.choose_natCast]
    · intro i member
      by_contra outside
      have large : 1 < i := by
        change i ∉ ({0, 1} : Finset ℕ) at outside
        simp only [Finset.mem_insert, Finset.mem_singleton] at outside
        omega
      apply member
      have chooseZero : Ring.choose (1 : ℤ) i = 0 := by
        simpa only [Nat.cast_one, Nat.choose_eq_zero_of_lt large, Nat.cast_zero]
          using (Ring.choose_natCast (R := ℤ) 1 i)
      simp [jacobiLeftTerm, integerBinomial, chooseZero]
  rw [leftValue, forward_zero_parameter, reverse_zero_parameter] at law
  simp only [epsilon, zpow_zero, one_mul] at law
  exact (eq_sub_iff_add_eq.mp law).symm.trans (by abel)

/-- The original physical B0 product defect for a first argument of grade p. -/
def defect (p : ℕ) (a c : State D) : State D :=
  ghostB D 0 (mu D a c) - mu D (ghostB D 0 a) c -
    (-1 : ℂ)^p • mu D a (ghostB D 0 c)

/-- The defect is exactly the zero mode of the original physical B(-1) state. -/
theorem defect_as_actual_b_mode (p : ℕ) (a c : State D)
    (ha : parity D a = (-1 : ℂ)^p • a) :
    defect D p a c = ((Y D (ghostB D (-1) a))[[0]]) c := by
  have law := one_mode_commutator D 1 p (beta D) a c
    (by simpa only [pow_one, neg_one_smul] using beta_odd D) ha
  simp only [beta_mode_one, beta_mode_zero, Nat.one_mul] at law
  unfold defect
  rw [law]
  abel

-- Derived from actual field parity at beta's vertex mode zero, rather than
-- imposing a grading on B(-1)a or transporting a ghost-carrier statement.
private theorem BminusOne_parity (p : ℕ) (a : State D)
    (ha : parity D a = (-1 : ℂ)^p • a) :
    parity D (ghostB D (-1) a) = (-1 : ℂ)^(p + 1) • ghostB D (-1) a := by
  have h := LinearMap.congr_fun (stateField_parity D (beta D) 0) a
  change parity D (((Y D (beta D))[[0]]) a) =
    ((Y D (parity D (beta D)))[[0]]) (parity D a) at h
  rw [beta_odd, ha] at h
  simp only [map_neg, Pi.neg_apply, LinearMap.neg_apply, map_smul,
    beta_mode_zero] at h
  simpa only [pow_succ, mul_smul, neg_one_smul, smul_neg] using h

/-- Raw-state second order for the actual physical B0, without an energy,
rank, Gram, BRST or charge-sector hypothesis. Only a and c are homogeneous;
d is any state of the full original algebraic tensor carrier. -/
theorem actual_B0_second_order (p q : ℕ) (a c d : State D)
    (ha : parity D a = (-1 : ℂ)^p • a)
    (hc : parity D c = (-1 : ℂ)^q • c) :
    defect D p a (mu D c d) =
      mu D (defect D p a c) d +
        (-1 : ℂ)^((p + 1) * q) • mu D c (defect D p a d) := by
  have oddParity := BminusOne_parity D p a ha
  simp only [defect_as_actual_b_mode D p a _ ha]
  exact zero_mode_derivation D (p + 1) q (ghostB D (-1) a) c d oddParity hc

end
end D5.S3.VertexAlgebra.LatticeMatterGhostAntighostSecondOrder
