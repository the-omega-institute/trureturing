/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCurrentIdentities
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTCurrentIdentities
   mirror-E: none(waiver:original-current-identities)
   anchors: []
   utility: none
   digest: Original CAR and Borcherds give relative closure and vector left-Leibniz. -/

/- Original source proof, using the frozen original matter/ghost suppliers.
The lattice, ghost, Scott Carnahan residue-calculus and Mathlib attributions
in those suppliers are retained. No literature novelty is asserted.
proof_shape: current_b0, current_leftLeibniz: content
admission_basis: escape-witness
escape_witness: The two different beta indices give literal b0 closure and
an exact vector identity on the original State, before passage to cohomology.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCurrentIdentities

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeBRSTCohomologyField (originalMode originalMode_apply)
open LatticeBRSTCohomologyBVSecondOrder (descentCurrent)
open LatticeMatterGhostSignedBorcherds (mu_D jacobiLeftTerm)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open D5.S3.Quantum.Fermionic
open private beta beta_modes beta_odd antighost_mode b_parity zero_binomial_sum
  current_cycle current_charge from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyBVSecondOrder
open private charge_parity from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyField
open private parity_square from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation
open private homogeneous_borcherds tensorLeft tensorForward tensorReverse reverseTerm from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds

noncomputable section

variable (D : LatticeData)

/-- The ORIGINAL b CAR lifted to the original tensor carrier. -/
theorem b_car (m n : ℤ) (x : State D) :
    ghostB D m (ghostB D n x) + ghostB D n (ghostB D m x) = 0 := by
  have law : ghostB D m * ghostB D n + ghostB D n * ghostB D m = 0 := by
    apply TensorProduct.ext'
    intro v w
    have h := LinearMap.congr_fun (BcGhostFock.ghost_b_car m n) w
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
    simp only [ghostB, LinearMap.add_apply, Module.End.mul_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
    rw [← TensorProduct.tmul_add, h, TensorProduct.tmul_zero]
  exact LinearMap.congr_fun law x

/-- In characteristic zero, the same-mode CAR kills the literal square. -/
theorem b_square (m : ℤ) (x : State D) : ghostB D m (ghostB D m x) = 0 := by
  have h := b_car D m m x
  have h2 : (2 : ℂ) • ghostB D m (ghostB D m x) = 0 := by
    simpa only [two_smul] using h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- beta mode ONE is b0. The last summand contains b(-1) squared. -/
theorem current_b0 (x y : State D)
    (hx : ghostB D 0 x = 0) (hy : ghostB D 0 y = 0) :
    ghostB D 0 (descentCurrent D x y) = 0 := by
  have cross : ghostB D 0 (ghostB D (-1) x) = 0 := by
    have h := b_car D 0 (-1) x
    simpa only [hx, map_zero, add_zero] using h
  have law := antighost_mode D (ghostB D (-1) x) y 0
  simpa only [hy, cross, b_square D (-1) x, map_zero,
    LinearMap.zero_apply, sub_zero, zero_add, descentCurrent,
    LinearMap.comp_apply] using law

private theorem current_b0_derivation (x y : State D) :
    ghostB D 0 (descentCurrent D x y) =
      -descentCurrent D (ghostB D 0 x) y -
        descentCurrent D (LatticeMatterGhostStateField.parity D x) (ghostB D 0 y) := by
  have cross : ghostB D 0 (ghostB D (-1) x) = -ghostB D (-1) (ghostB D 0 x) :=
    eq_neg_iff_add_eq_zero.mpr (b_car D 0 (-1) x)
  have law := antighost_mode D (ghostB D (-1) x) y 0
  rw [cross, b_square, b_parity] at law
  simp only [map_neg, LinearMap.neg_apply, map_zero, LinearMap.zero_apply,
    add_zero] at law
  change ghostB D 0 (descentCurrent D x y) -
      -(descentCurrent D (LatticeMatterGhostStateField.parity D x) (ghostB D 0 y)) =
        -descentCurrent D (ghostB D 0 x) y at law
  exact (sub_eq_iff_eq_add.mp law).trans (by abel)

/-- Actual energy covariance of the composite current follows from original
{Q,b0}=L0 and the two original odd current laws. No weight axiom is added. -/
theorem current_L0
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (x y : State D) :
    LatticeBRSTZeroEnergyReduction.totalL0 D H (descentCurrent D x y) =
      descentCurrent D (LatticeBRSTZeroEnergyReduction.totalL0 D H x) y +
        descentCurrent D x (LatticeBRSTZeroEnergyReduction.totalL0 D H y) := by
  have ward (z : State D) : LatticeBRSTZeroEnergyReduction.totalL0 D H z =
      LatticeBRST.totalCharge D H (ghostB D 0 z) +
        ghostB D 0 (LatticeBRST.totalCharge D H z) :=
    (LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) z).symm
  rw [ward, current_b0_derivation, current_charge D H hHG hGH x y]
  simp only [map_sub, map_neg, current_charge D H hHG hGH,
    current_b0_derivation, charge_parity, b_parity, parity_square,
    LinearMap.neg_apply, ward, map_add, LinearMap.add_apply]
  abel

/-- beta mode ZERO is b(-1), and acts as a superderivation of every actual mode. -/
theorem b_minus_one_mode (x y : State D) (n : ℤ) :
    ghostB D (-1) (originalMode D n x y) =
      originalMode D n (ghostB D (-1) x) y +
        originalMode D n (LatticeMatterGhostStateField.parity D x) (ghostB D (-1) y) := by
  have law := (LatticeMatterGhostBorcherds.borcherds D (beta D) x y 0 n 0).2.2.2.2
  dsimp only at law
  have proj0 : (2 : ℂ)⁻¹ •
      (beta D + LatticeMatterGhostStateField.parity D (beta D)) = 0 := by
    rw [beta_odd, add_neg_cancel, smul_zero]
  have proj1 : (2 : ℂ)⁻¹ •
      (beta D - LatticeMatterGhostStateField.parity D (beta D)) = beta D := by
    rw [beta_odd]
    module
  rw [proj0, proj1, finsum_eq_single _ 0] at law
  · rw [finsum_eq_single _ 0] at law
    · have h : originalMode D n (ghostB D (-1) x) y =
          ghostB D (-1) (originalMode D n x y) -
            originalMode D n (LatticeMatterGhostStateField.parity D x)
              (ghostB D (-1) y) := by
        simpa [jacobiLeftTerm, integerBinomial, epsilon, mu_D,
          ← originalMode_apply, beta_modes] using law
      exact (eq_sub_iff_add_eq.mp h).symm
    · intro i hi
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  · intro i hi
    simp [jacobiLeftTerm, integerBinomial,
      Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

/-- The even zero-mode commutator is an actual vector equality, for every target mode. -/
theorem even_zero_mode (u v w : State D) (n : ℤ)
    (hu : LatticeMatterGhostStateField.parity D u = u)
    (hv : LatticeMatterGhostStateField.parity D v = v) :
    originalMode D 0 u (originalMode D n v w) =
      originalMode D n (originalMode D 0 u v) w +
        originalMode D n v (originalMode D 0 u w) := by
  have law := homogeneous_borcherds D u v w 0 0
    (by simpa only [pow_zero, one_smul] using hu)
    (by simpa only [pow_zero, one_smul] using hv) 0 n 0
  simp only [tensorLeft, tensorForward, tensorReverse, reverseTerm,
    LatticeMatterGhostSignedBorcherds.jacobiLeftTerm,
    LatticeMatterGhostSignedBorcherds.jacobiRightFirstTerm] at law
  have left : (∑ᶠ i : ℕ, integerBinomial 0 i •
      mu_D D (mu_D D u (0 + i) v) (0 + n - i) w) =
      originalMode D n (originalMode D 0 u v) w := by
    rw [finsum_eq_single _ 0]
    · simp [integerBinomial, mu_D, originalMode_apply]
    · intro i hi
      simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]
  rw [left, zero_binomial_sum, zero_binomial_sum] at law
  simpa [epsilon, mu_D, originalMode_apply] using
    (eq_sub_iff_add_eq.mp law).symm

set_option backward.isDefEq.respectTransparency true in
/-- The unsigned current has exact left-Leibniz on odd ORIGINAL states. -/
theorem current_leftLeibniz (x y z : State D)
    (hx : LatticeMatterGhostStateField.parity D x = -x)
    (hy : LatticeMatterGhostStateField.parity D y = -y) :
    descentCurrent D x (descentCurrent D y z) =
      descentCurrent D (descentCurrent D x y) z +
        descentCurrent D y (descentCurrent D x z) := by
  have ex : LatticeMatterGhostStateField.parity D (ghostB D (-1) x) =
      ghostB D (-1) x := by
    calc
      _ = -ghostB D (-1) (LatticeMatterGhostStateField.parity D x) := b_parity D (-1) x
      _ = -ghostB D (-1) (-x) := congrArg (fun w : State D => -ghostB D (-1) w) hx
      _ = -(-ghostB D (-1) x) :=
        congrArg (fun w : State D => -w) ((ghostB D (-1)).map_neg x)
      _ = _ := neg_neg _
  have ey : LatticeMatterGhostStateField.parity D (ghostB D (-1) y) =
      ghostB D (-1) y := by
    calc
      _ = -ghostB D (-1) (LatticeMatterGhostStateField.parity D y) := b_parity D (-1) y
      _ = -ghostB D (-1) (-y) := congrArg (fun w : State D => -ghostB D (-1) w) hy
      _ = -(-ghostB D (-1) y) :=
        congrArg (fun w : State D => -w) ((ghostB D (-1)).map_neg y)
      _ = _ := neg_neg _
  have bc : ghostB D (-1) (descentCurrent D x y) =
      originalMode D 0 (ghostB D (-1) x) (ghostB D (-1) y) := by
    change ghostB D (-1) (originalMode D 0 (ghostB D (-1) x) y) = _
    rw [b_minus_one_mode D (ghostB D (-1) x) y 0, b_square D (-1) x, ex]
    simp only [map_zero, LinearMap.zero_apply, zero_add]
  change originalMode D 0 (ghostB D (-1) x)
      (originalMode D 0 (ghostB D (-1) y) z) = _
  rw [even_zero_mode D _ _ z 0 ex ey]
  change _ = originalMode D 0 (ghostB D (-1) (descentCurrent D x y)) z + _
  rw [bc]
  rfl

/-- Representative energy closure follows from the ACTUAL Ward identity,
without assuming a missing weight theorem or any positivity. -/
theorem current_zero_energy
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)
    (x y : LatticeBRSTCohomologyField.cycles D H)
    (hx : ghostB D 0 x = 0) (hy : ghostB D 0 y = 0) :
    LatticeBRSTZeroEnergyReduction.totalL0 D H (descentCurrent D x y) = 0 := by
  have law := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0)
    (descentCurrent D x y)
  have closed := current_cycle D H hHG hGH x y
  change LatticeBRST.totalCharge D H (ghostB D 0 (descentCurrent D x y)) +
      ghostB D 0 (LatticeBRST.totalCharge D H (descentCurrent D x y)) =
        LatticeBRSTZeroEnergyReduction.totalL0 D H (descentCurrent D x y) at law
  rw [current_b0 D _ _ hx hy, closed, map_zero, map_zero, add_zero] at law
  exact law.symm

end
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTCurrentIdentities
