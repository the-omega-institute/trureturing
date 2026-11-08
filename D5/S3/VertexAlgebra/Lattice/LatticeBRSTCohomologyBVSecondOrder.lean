/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder
   mirror-E: none(waiver:actual-brst-second-order)
   anchors: []
   utility: none
   digest: Actual antighost descent identifies Delta's quotient defect and graded Leibniz law. -/

/-
The low-mode proof mechanism follows OriginalTopologicalApplications
(SHA256 85302c4b23c6e4e0f271ca7aa794ba69c65fbef4af813ca5e0204940696d95ad),
without importing its historical carrier, charge, or quotient. All operators
here are the actual lattice matter-ghost operators. Supplier attribution is
retained: Bakalov--Kac's lattice construction, Scott Carnahan's Apache-2.0
vertexAlg residue calculus, Kalle Kytölä's Sugawara architecture, and the
original ghost and Mathlib authors. No literature novelty is claimed.

proof_shape: Delta_product_defect, Delta_second_order: content
admission_basis: escape-witness
escape_witness: Explicit current primitives descend through both actual boundary
ideals. Applying Q to the antighost identity establishes the actual reduced
product's zero energy, connecting the independent descended current to Delta.
The parity-shifted zero-mode derivation then supplies the quotient Leibniz law.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyProduct
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTZeroEnergyReduction
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBorcherds

/-! Antighost descent and the second-order law on the actual full quotient. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder

open LatticeGeneratingFieldLocality (LatticeData)
open LatticeMatterGhostCoupling (State ghostB)
open LatticeBRSTCohomologyField
open LatticeBRSTZeroEnergyReduction
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket)
open LatticeMatterGhostSignedBorcherds (mu_D jacobiLeftTerm)
open StateFieldResidueReconstruction (integerBinomial epsilon)
open private left_vacuum_modes identity_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private parity_square from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostBRSTDerivation
open private charge_parity parity_cycle cycle_mode_closed from
  D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyField
open private homogeneous_iterate leftSum rightSum from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateFieldIterate

noncomputable section

variable (D : LatticeData)

private def beta : State D := LatticeAllStateField.vacuum D ⊗ₜ[ℂ] ket {0}

private theorem beta_modes (n : ℤ) :
    ((LatticeMatterGhostStateField.Y D (beta D))[[n]]) = ghostB D (n - 1) := by
  rw [beta, left_vacuum_modes, BcGhostStateField.stateField_creation.2.2.2.1]
  rfl

private theorem beta_odd : LatticeMatterGhostStateField.parity D (beta D) = -beta D := by
  simp [beta, LatticeMatterGhostStateField.parity, TensorProduct.map_tmul,
    parity_ket, TensorProduct.tmul_neg]

/-- Actual all-state one-mode commutator; the reverse parity family is retained. -/
private theorem antighost_mode (x y : State D) (n : ℤ) :
    ghostB D 0 (originalMode D n x y) -
        originalMode D n (LatticeMatterGhostStateField.parity D x) (ghostB D 0 y) =
      originalMode D n (ghostB D 0 x) y +
        originalMode D (n + 1) (ghostB D (-1) x) y := by
  classical
  have law := (LatticeMatterGhostBorcherds.borcherds D (beta D) x y 1 n 0).2.2.2.2
  dsimp only at law
  have proj0 : (2 : ℂ)⁻¹ • (beta D + LatticeMatterGhostStateField.parity D (beta D)) = 0 := by
    rw [beta_odd, add_neg_cancel, smul_zero]
  have proj1 : (2 : ℂ)⁻¹ • (beta D - LatticeMatterGhostStateField.parity D (beta D)) = beta D := by
    rw [beta_odd]; module
  rw [proj0, proj1] at law
  have left : (∑ᶠ i : ℕ, jacobiLeftTerm D 1 n 0 (beta D) x y i) =
      originalMode D (n + 1) (ghostB D (-1) x) y +
        originalMode D n (ghostB D 0 x) y := by
    rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
    · simp [jacobiLeftTerm, integerBinomial, mu_D,
        ← originalMode_apply, beta_modes, add_comm]
    · intro i hi
      by_contra outside
      have large : 1 < i := by
        change i ∉ ({0, 1} : Finset ℕ) at outside
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at outside
        omega
      have chooseZero : Ring.choose (1 : ℤ) i = 0 := by
        simpa only [Nat.cast_one, Nat.choose_eq_zero_of_lt large, Nat.cast_zero]
          using (Ring.choose_natCast (R := ℤ) 1 i)
      exact hi (by simp [jacobiLeftTerm, integerBinomial, chooseZero])
  rw [left, finsum_eq_single _ 0] at law
  · simpa [integerBinomial, epsilon, mu_D, ← originalMode_apply,
      beta_modes, add_comm] using law.symm
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem translation_residue (x y : State D) :
    originalMode D 0 (LatticeMatterGhostStateField.translation D x) y = 0 := by
  have creation := LatticeMatterGhostStateField.stateField_vacuum_creation D
  have tx : LatticeMatterGhostStateField.translation D x =
      originalMode D (-2) x (LatticeMatterGhostStateField.vacuum D) := by
    have h := LinearMap.congr_fun
      (LatticeMatterGhostStateField.stateField_covariance D x (-1))
      (LatticeMatterGhostStateField.vacuum D)
    simpa only [originalMode_apply, Module.End.mul_apply, LinearMap.sub_apply, creation.2.1,
      creation.2.2.2, map_zero, sub_zero, Int.cast_neg, Int.cast_one,
      neg_neg, one_smul, show (-1 - 1 : ℤ) = -2 by omega] using h
  rw [tx]
  have law := (LatticeMatterGhostStateFieldIterate.stateField_iterate D x
    (LatticeMatterGhostStateField.vacuum D) y (-2) 0).2.2.2
  dsimp only at law
  have vacuumMode (n : ℤ) (hn : n ≠ -1) :
      ((LatticeMatterGhostStateField.Y D (LatticeMatterGhostStateField.vacuum D))[[n]]) = 0 := by
    rw [creation.1, identity_modes, ite_eq_right hn]
  have forward : (∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * (Ring.choose (-2 : ℤ) i : ℤ)) •
      (((LatticeMatterGhostStateField.Y D x)[[-2 - (i : ℤ)]])
        (((LatticeMatterGhostStateField.Y D (LatticeMatterGhostStateField.vacuum D))
          [[0 + (i : ℤ)]]) y))) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [vacuumMode _ (by omega)]
    simp
  rw [forward] at law
  have back (z : State D) : (∑ᶠ i : ℕ,
      ((-1 : ℂ) ^ i * (Ring.choose (-2 : ℤ) i : ℤ)) •
        (((LatticeMatterGhostStateField.Y D (LatticeMatterGhostStateField.vacuum D))
          [[-2 + 0 - (i : ℤ)]]) (((LatticeMatterGhostStateField.Y D z)[[(i : ℤ)]]) y))) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [vacuumMode _ (by omega)]
    simp
  rw [back] at law
  have pv : LatticeMatterGhostStateField.parity D (LatticeMatterGhostStateField.vacuum D) =
      LatticeMatterGhostStateField.vacuum D := by
    simp [LatticeMatterGhostStateField.parity, LatticeMatterGhostStateField.vacuum,
      TensorProduct.map_tmul, CountableOccupationFock.vacuum, parity_ket]
  rw [pv, back] at law
  simpa only [originalMode_apply, zero_add, smul_zero, sub_zero] using law

private theorem b_parity (j : ℤ) (x : State D) :
    LatticeMatterGhostStateField.parity D (ghostB D j x) =
      -ghostB D j (LatticeMatterGhostStateField.parity D x) := by
  have h := LinearMap.congr_fun
    (LatticeMatterGhostStateField.stateField_parity D (beta D) (j + 1)) x
  rw [beta_odd] at h
  simpa only [map_neg, Pi.neg_apply, LinearMap.neg_apply, beta_modes,
    show j + 1 - 1 = j by omega, Module.End.mul_apply] using h

/-- The current is defined on the literal states, independently of Delta and product. -/
def descentCurrent : State D →ₗ[ℂ] Module.End ℂ (State D) :=
  (originalMode D 0).comp (ghostB D (-1))

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

include hHG hGH in
private theorem current_charge (x y : State D) :
    LatticeBRST.totalCharge D H (descentCurrent D x y) =
      -(descentCurrent D (LatticeBRST.totalCharge D H x) y) -
        descentCurrent D (LatticeMatterGhostStateField.parity D x)
          (LatticeBRST.totalCharge D H y) := by
  have ward := LinearMap.congr_fun
    (original_translation_eq_charge_b D H hHG hGH) x
  change LatticeMatterGhostStateField.translation D x =
    LatticeBRST.totalCharge D H (ghostB D (-1) x) +
      ghostB D (-1) (LatticeBRST.totalCharge D H x) at ward
  have qb := eq_sub_iff_add_eq.mpr ward.symm
  change LatticeBRST.totalCharge D H (originalMode D 0 (ghostB D (-1) x) y) = _
  rw [charge_mode, qb, b_parity]
  simp only [map_sub, LinearMap.sub_apply, translation_residue, zero_sub,
    map_neg, LinearMap.neg_apply]
  rfl

include hHG hGH in
private theorem current_cycle (x y : cycles D H) :
    LatticeBRST.totalCharge D H (descentCurrent D x y) = 0 := by
  rw [current_charge D H hHG hGH, show LatticeBRST.totalCharge D H x = 0 from x.property,
    show LatticeBRST.totalCharge D H y = 0 from y.property]
  simp

private def cycleCurrent : cycles D H →ₗ[ℂ] Module.End ℂ (cycles D H) where
  toFun x := {
    toFun y := ⟨descentCurrent D x y, current_cycle D H hHG hGH x y⟩
    map_add' y z := Subtype.ext (map_add (descentCurrent D x) (y : State D) z)
    map_smul' c y := Subtype.ext (map_smul (descentCurrent D x) c (y : State D)) }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (descentCurrent D) (x : State D) y) z
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (descentCurrent D) c (x : State D)) y

private theorem cycleCurrent_val (x y : cycles D H) :
    (cycleCurrent D H hHG hGH x y : State D) = descentCurrent D x y := rfl

private theorem group_neg_neg {V : Type*} [AddCommGroup V] (w : V) : -(-w) = w :=
  _root_.neg_neg w

include hHG hGH in
private theorem current_left_primitive (z : State D) (y : cycles D H) :
    LatticeBRST.totalCharge D H (-(descentCurrent D z y)) =
      descentCurrent D (LatticeBRST.totalCharge D H z) y := by
  have hq : LatticeBRST.totalCharge D H (descentCurrent D z y) =
      -(descentCurrent D (LatticeBRST.totalCharge D H z) y) := by
    rw [current_charge D H hHG hGH,
      show LatticeBRST.totalCharge D H y = 0 from y.property,
      (descentCurrent D (LatticeMatterGhostStateField.parity D z)).map_zero, sub_zero]
  exact ((LatticeBRST.totalCharge D H).map_neg _).trans
    ((congrArg (fun w : State D => -w) hq).trans
      (group_neg_neg (V := State D) (descentCurrent D (LatticeBRST.totalCharge D H z) y)))

include hHG hGH in
private theorem current_right_primitive (x : cycles D H) (z : State D) :
    LatticeBRST.totalCharge D H
      (-(descentCurrent D (LatticeMatterGhostStateField.parity D x) z)) =
      descentCurrent D x (LatticeBRST.totalCharge D H z) := by
  have hz : descentCurrent D (0 : State D) z = 0 :=
    LinearMap.congr_fun (descentCurrent D |>.map_zero) z
  have hq : LatticeBRST.totalCharge D H
      (descentCurrent D (LatticeMatterGhostStateField.parity D x) z) =
      -(descentCurrent D x (LatticeBRST.totalCharge D H z)) := by
    rw [current_charge D H hHG hGH, parity_cycle, parity_square, hz, neg_zero, zero_sub]
  exact ((LatticeBRST.totalCharge D H).map_neg _).trans
    ((congrArg (fun w : State D => -w) hq).trans
      (group_neg_neg (V := State D) (descentCurrent D x (LatticeBRST.totalCharge D H z))))

private theorem current_left_boundary (x y : cycles D H)
    (hx : x ∈ boundaries D H h26 hHG hGH) :
    cycleCurrent D H hHG hGH x y ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨z, hz⟩ := (mem_boundaries D H h26 hHG hGH x).mp hx
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨-(descentCurrent D z y), ?_⟩
  exact (current_left_primitive D H hHG hGH z y).trans
    ((congrArg (fun t : State D => descentCurrent D t y) hz).trans
      (cycleCurrent_val D H hHG hGH x y).symm)

private theorem current_right_boundary (x y : cycles D H)
    (hy : y ∈ boundaries D H h26 hHG hGH) :
    cycleCurrent D H hHG hGH x y ∈ boundaries D H h26 hHG hGH := by
  obtain ⟨z, hz⟩ := (mem_boundaries D H h26 hHG hGH y).mp hy
  apply (mem_boundaries D H h26 hHG hGH _).mpr
  refine ⟨-(descentCurrent D (LatticeMatterGhostStateField.parity D x) z), ?_⟩
  exact (current_right_primitive D H hHG hGH x z).trans
    ((congrArg (fun t : State D => descentCurrent D x t) hz).trans
      (cycleCurrent_val D H hHG hGH x y).symm)

private def cycleClassCurrent :
    cycles D H →ₗ[ℂ] cycles D H →ₗ[ℂ] Cohomology D H h26 hHG hGH where
  toFun x := (classOf D H h26 hHG hGH).comp (cycleCurrent D H hHG hGH x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, map_add, LinearMap.add_apply]
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply]

/-- Both actual boundary ideals are killed by explicit current primitives. -/
def cohomologyCurrent : Cohomology D H h26 hHG hGH →ₗ[ℂ]
    Module.End ℂ (Cohomology D H h26 hHG hGH) :=
  LinearMap.liftQ₂ (R := ℂ) (R₂ := ℂ) (S := ℂ) (S₂ := ℂ)
    (M := cycles D H) (N := cycles D H) (P := Cohomology D H h26 hHG hGH)
    (ρ := RingHom.id ℂ) (σ := RingHom.id ℂ)
    (boundaries D H h26 hHG hGH) (boundaries D H h26 hHG hGH)
    (cycleClassCurrent D H h26 hHG hGH)
    (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro y
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (current_left_boundary D H h26 hHG hGH x y hx))
    (by
      intro y hy
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (current_right_boundary D H h26 hHG hGH x y hy))

private theorem current_classOf (x y : cycles D H) :
    cohomologyCurrent D H h26 hHG hGH (classOf D H h26 hHG hGH x)
      (classOf D H h26 hHG hGH y) =
      classOf D H h26 hHG hGH (cycleCurrent D H hHG hGH x y) := rfl

include h26 hHG hGH in
private theorem b_cycle_fixed (x : cycles D H)
    (hx : P0 D (x : State D) = x) :
    LatticeBRST.totalCharge D H (ghostB D 0 x) = 0 := by
  rw [← hx]
  exact B0_P0_cycle D H h26 hHG hGH x x.property

include h26 hHG hGH in
private theorem product_fixed (x y : cycles D H)
    (hx : P0 D (x : State D) = x) (hy : P0 D (y : State D) = y) :
    P0 D (originalMode D (-1) x y) = originalMode D (-1) x y := by
  have bx := b_cycle_fixed D H h26 hHG hGH x hx
  have by' := b_cycle_fixed D H h26 hHG hGH y hy
  have law := antighost_mode D (x : State D) y (-1)
  have rearranged : ghostB D 0 (originalMode D (-1) x y) =
      originalMode D (-1) (ghostB D 0 x) y + descentCurrent D x y +
        originalMode D (-1) (LatticeMatterGhostStateField.parity D x) (ghostB D 0 y) := by
    change _ - _ = _ + descentCurrent D x y at law
    exact (sub_eq_iff_eq_add.mp law).trans (by abel)
  have closed : LatticeBRST.totalCharge D H
      (ghostB D 0 (originalMode D (-1) x y)) = 0 := by
    rw [rearranged, map_add, map_add, charge_mode, charge_mode,
      current_cycle D H hHG hGH, bx, by', parity_cycle]
    simp only [show LatticeBRST.totalCharge D H y = 0 from y.property,
      map_zero, LinearMap.zero_apply, add_zero]
  apply (P0_fixed_iff D H hHG hGH _).mpr
  have ward := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0)
    (originalMode D (-1) x y)
  change LatticeBRST.totalCharge D H (ghostB D 0 (originalMode D (-1) x y)) +
    ghostB D 0 (LatticeBRST.totalCharge D H (originalMode D (-1) x y)) =
      totalL0 D H (originalMode D (-1) x y) at ward
  rw [closed, cycle_mode_closed, map_zero, add_zero] at ward
  exact ward.symm

private theorem delta_defect_fixed (x y : cycles D H)
    (hx : P0 D (x : State D) = x) (hy : P0 D (y : State D) = y) :
    Delta D H h26 hHG hGH
        (product D H h26 hHG hGH (classOf D H h26 hHG hGH x) (classOf D H h26 hHG hGH y)) -
      product D H h26 hHG hGH (Delta D H h26 hHG hGH (classOf D H h26 hHG hGH x))
        (classOf D H h26 hHG hGH y) -
      product D H h26 hHG hGH (parity D H h26 hHG hGH (classOf D H h26 hHG hGH x))
        (Delta D H h26 hHG hGH (classOf D H h26 hHG hGH y)) =
      cohomologyCurrent D H h26 hHG hGH (classOf D H h26 hHG hGH x)
        (classOf D H h26 hHG hGH y) := by
  have hc : cycleDelta D H h26 hHG hGH (cycleMode D H (-1) x y) -
      cycleMode D H (-1) (cycleDelta D H h26 hHG hGH x) y -
      cycleMode D H (-1) (cycleParity D H x) (cycleDelta D H h26 hHG hGH y) =
      cycleCurrent D H hHG hGH x y := by
    apply Subtype.ext
    change ghostB D 0 (P0 D (originalMode D (-1) x y)) -
        originalMode D (-1) (ghostB D 0 (P0 D x)) y -
        originalMode D (-1) (LatticeMatterGhostStateField.parity D x) (ghostB D 0 (P0 D y)) =
      descentCurrent D x y
    rw [product_fixed D H h26 hHG hGH x y hx hy, hx, hy]
    have law := antighost_mode D (x : State D) y (-1)
    change _ - _ = _ + descentCurrent D x y at law
    rw [sub_eq_iff_eq_add.mp law]
    abel
  change classOf D H h26 hHG hGH (cycleDelta D H h26 hHG hGH (cycleMode D H (-1) x y)) -
      classOf D H h26 hHG hGH (cycleMode D H (-1) (cycleDelta D H h26 hHG hGH x) y) -
      classOf D H h26 hHG hGH
        (cycleMode D H (-1) (cycleParity D H x) (cycleDelta D H h26 hHG hGH y)) = _
  rw [current_classOf]
  simpa only [map_sub] using congrArg (classOf D H h26 hHG hGH) hc

/-- On the full existing quotient, the independently descended current is
exactly the defect of the existing physical Delta for arbitrary classes. -/
theorem Delta_product_defect (a b : Cohomology D H h26 hHG hGH) :
    Delta D H h26 hHG hGH (product D H h26 hHG hGH a b) -
      product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b -
      product D H h26 hHG hGH (parity D H h26 hHG hGH a) (Delta D H h26 hHG hGH b) =
      cohomologyCurrent D H h26 hHG hGH a b := by
  obtain ⟨x, rfl⟩ := classOf_surjective D H h26 hHG hGH a
  obtain ⟨y, rfl⟩ := classOf_surjective D H h26 hHG hGH b
  have hx : P0 D (cycleP0 D H h26 hHG hGH x : State D) =
      (cycleP0 D H h26 hHG hGH x : State D) :=
    (P0_fixed_iff D H hHG hGH _).mpr (totalL0_P0 D H hHG hGH x)
  have hy : P0 D (cycleP0 D H h26 hHG hGH y : State D) =
      (cycleP0 D H h26 hHG hGH y : State D) :=
    (P0_fixed_iff D H hHG hGH _).mpr (totalL0_P0 D H hHG hGH y)
  simpa only [classOf_P0] using delta_defect_fixed D H h26 hHG hGH
    (cycleP0 D H h26 hHG hGH x) (cycleP0 D H h26 hHG hGH y) hx hy

private theorem zero_binomial_sum (f : ℕ → State D) :
    (∑ᶠ i : ℕ, ((-1 : ℂ) ^ i * integerBinomial 0 i) • f i) = f 0 := by
  rw [finsum_eq_single _ 0]
  · simp [integerBinomial]
  · intro i hi
    simp [integerBinomial, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero hi)]

private theorem zero_mode_derivation (u v w : State D) (p q : ℕ)
    (hu : LatticeMatterGhostStateField.parity D u = (-1 : ℂ) ^ p • u)
    (hv : LatticeMatterGhostStateField.parity D v = (-1 : ℂ) ^ q • v) :
    originalMode D 0 u (originalMode D (-1) v w) =
      originalMode D (-1) (originalMode D 0 u v) w +
        (-1 : ℂ) ^ (p*q) • originalMode D (-1) v (originalMode D 0 u w) := by
  have law := homogeneous_iterate D u v w p q hu hv 0 (-1)
  simp only [leftSum, rightSum, SignedFieldResidueLocality.residueLeft,
    SignedFieldResidueLocality.residueRight, zero_binomial_sum,
    epsilon, zpow_zero, one_mul, Nat.cast_zero, sub_zero, add_zero,
    zero_add] at law
  simpa only [originalMode_apply] using (eq_sub_iff_add_eq.mp law).symm

private theorem current_leibniz (u v w : State D) (p q : ℕ)
    (hu : LatticeMatterGhostStateField.parity D u = (-1 : ℂ) ^ p • u)
    (hv : LatticeMatterGhostStateField.parity D v = (-1 : ℂ) ^ q • v) :
    descentCurrent D u (originalMode D (-1) v w) =
      originalMode D (-1) (descentCurrent D u v) w +
        (-1 : ℂ) ^ ((p + 1) * q) • originalMode D (-1) v (descentCurrent D u w) := by
  have shifted : LatticeMatterGhostStateField.parity D (ghostB D (-1) u) =
      (-1 : ℂ) ^ (p + 1) • ghostB D (-1) u := by
    rw [b_parity, hu, map_smul, pow_succ, mul_smul]
    simp only [neg_one_smul, smul_neg]
  exact zero_mode_derivation D (ghostB D (-1) u) v w (p + 1) q shifted hv

private theorem quotient_current_leibniz (a b c : Cohomology D H h26 hHG hGH)
    (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ) ^ p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ) ^ q • b) :
    cohomologyCurrent D H h26 hHG hGH a (product D H h26 hHG hGH b c) =
      product D H h26 hHG hGH (cohomologyCurrent D H h26 hHG hGH a b) c +
        (-1 : ℂ) ^ ((p + 1) * q) • product D H h26 hHG hGH b
          (cohomologyCurrent D H h26 hHG hGH a c) := by
  obtain ⟨u, rfl, hu⟩ := homogeneous_cycle_lift D H h26 hHG hGH a p ha
  obtain ⟨v, rfl, hv⟩ := homogeneous_cycle_lift D H h26 hHG hGH b q hb
  obtain ⟨w, rfl⟩ := classOf_surjective D H h26 hHG hGH c
  have hc : cycleCurrent D H hHG hGH u (cycleMode D H (-1) v w) =
      cycleMode D H (-1) (cycleCurrent D H hHG hGH u v) w +
        (-1 : ℂ) ^ ((p + 1) * q) • cycleMode D H (-1) v (cycleCurrent D H hHG hGH u w) :=
    Subtype.ext (current_leibniz D (u : State D) v w p q hu hv)
  change classOf D H h26 hHG hGH (cycleCurrent D H hHG hGH u (cycleMode D H (-1) v w)) =
    classOf D H h26 hHG hGH (cycleMode D H (-1) (cycleCurrent D H hHG hGH u v) w) +
      (-1 : ℂ) ^ ((p + 1) * q) •
        classOf D H h26 hHG hGH (cycleMode D H (-1) v (cycleCurrent D H hHG hGH u w))
  simpa only [map_add, map_smul] using congrArg (classOf D H h26 hHG hGH) hc

/-- The actual Delta defect with the homogeneous first input's scalar sign. -/
def homogeneousDefect (p : ℕ) (a b : Cohomology D H h26 hHG hGH) :
    Cohomology D H h26 hHG hGH :=
  Delta D H h26 hHG hGH (product D H h26 hHG hGH a b) -
    product D H h26 hHG hGH (Delta D H h26 hHG hGH a) b -
    (-1 : ℂ) ^ p • product D H h26 hHG hGH a (Delta D H h26 hHG hGH b)

private theorem homogeneousDefect_eq_current (p : ℕ) (a b : Cohomology D H h26 hHG hGH)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ) ^ p • a) :
    homogeneousDefect D H h26 hHG hGH p a b = cohomologyCurrent D H h26 hHG hGH a b := by
  simpa only [homogeneousDefect, ha, map_smul, LinearMap.smul_apply]
    using Delta_product_defect D H h26 hHG hGH a b

/-- The genuine second-order endpoint on the existing full BRST quotient.
Only the first two classes are homogeneous; the third class is arbitrary. -/
theorem Delta_second_order (a b c : Cohomology D H h26 hHG hGH) (p q : ℕ)
    (ha : parity D H h26 hHG hGH a = (-1 : ℂ) ^ p • a)
    (hb : parity D H h26 hHG hGH b = (-1 : ℂ) ^ q • b) :
    homogeneousDefect D H h26 hHG hGH p a (product D H h26 hHG hGH b c) =
      product D H h26 hHG hGH (homogeneousDefect D H h26 hHG hGH p a b) c +
        (-1 : ℂ) ^ ((p + 1) * q) • product D H h26 hHG hGH b
          (homogeneousDefect D H h26 hHG hGH p a c) := by
  simp only [homogeneousDefect_eq_current D H h26 hHG hGH p a _ ha]
  exact quotient_current_leibniz D H h26 hHG hGH a b c p q ha hb

end
end D5.S3.VertexAlgebra.LatticeBRSTCohomologyBVSecondOrder
