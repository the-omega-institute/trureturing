/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTSquare
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTSquare
   mirror-E: none(waiver:algebraic-total-brst)
   anchors: []
   utility: none
   digest: The full rank-dependent signed anomaly on every original tensor state. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostDegree

/-! The exact rank-dependent square of the original total matter and cubic BRST charge. -/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeBRST

private theorem tensorNumber_eq (D : LatticeData) :
    LatticeMatterGhostDegree.tensorNumber D =
      BcGhostChargeTensor.number (M := Carrier D) := rfl

private theorem ghostCharge_eq_G (D : LatticeData) :
    ghostCharge D = LatticeMatterGhostDegree.G D := rfl

private theorem totalCharge_eq_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    totalCharge D H = LatticeMatterGhostDegree.Q D H := rfl

-- This is an operator equality, not a replacement of the native ghost square.
private theorem ghostSquareAnomaly_eq_G_square (D : LatticeData) :
    ghostSquareAnomaly D = LatticeMatterGhostDegree.G D ^ 2 := by
  calc
    ghostSquareAnomaly D = ghostCharge D * ghostCharge D :=
      (ghostCharge_square D).symm
    _ = LatticeMatterGhostDegree.G D ^ 2 := by
      simp only [ghostCharge_eq_G, pow_two]

private theorem squareResidual_eq_E (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    squareResidual D H = LatticeMatterGhostDegree.E D H := by
  change totalCharge D H * totalCharge D H -
      ((26 - (D.rank : ℂ)) / 26) • ghostSquareAnomaly D =
    LatticeMatterGhostDegree.Q D H ^ 2 -
      ((26 - (D.rank : ℂ)) / 26) • (LatticeMatterGhostDegree.G D ^ 2)
  rw [← totalCharge_eq_Q D H, ← ghostSquareAnomaly_eq_G_square D, pow_two]

private theorem squareResidual_degree (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    BcGhostChargeTensor.number (M := Carrier D) * squareResidual D H -
      squareResidual D H * BcGhostChargeTensor.number (M := Carrier D) =
        (2 : ℂ) • squareResidual D H := by
  rw [squareResidual_eq_E D H]
  simpa only [tensorNumber_eq D] using
    (LatticeMatterGhostDegree.tensorNumber_E D H)

private theorem squareResidual_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    squareResidual D H = 0 := by
  -- The tensor B/C here are definitionally the Ward supplier's ghostB/ghostC.
  exact BcGhostChargeTensor.charged_commutant_vanishes (M := Carrier D)
    (squareResidual D H)
    (fun r => squareResidual_b D H hHG hGH r)
    (fun r => squareResidual_c D H r)
    (2 : ℂ) (by norm_num) (squareResidual_degree D H)

/-- The full actual total square is the exact scalar multiple of the native ghost square. -/
theorem total_square_anomaly (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) :
    totalCharge D H ^ 2 =
      ((26 - (D.rank : ℂ)) / 26) • ghostSquareAnomaly D := by
  have hz : totalCharge D H * totalCharge D H -
      ((26 - (D.rank : ℂ)) / 26) • ghostSquareAnomaly D = 0 :=
    squareResidual_zero D H hHG hGH
  simpa only [pow_two] using sub_eq_zero.mp hz

-- Only the action on a state is summed; this lifted family is never finsummed
-- in the space of endomorphisms.
private def liftedSquareTerm (D : LatticeData) (n : ℤ) :
    Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (BcGhostBRST.squareTerm n)

private theorem liftedSquareTerm_finite (D : LatticeData) (x : State D) :
    Function.HasFiniteSupport (fun n : ℤ => liftedSquareTerm D n x) := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    simpa only [liftedSquareTerm, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.mk_apply] using
      (BcGhostBRST.squareTerm_finite w).fun_comp
        (map_zero (TensorProduct.mk ℂ (Carrier D) Fock v))
  | add x y hx hy =>
    apply (hx.union hy).subset
    intro n hn
    by_contra hnot
    have hx0 : liftedSquareTerm D n x = 0 := by
      by_contra hz
      exact hnot (Or.inl hz)
    have hy0 : liftedSquareTerm D n y = 0 := by
      by_contra hz
      exact hnot (Or.inr hz)
    exact hn (by simp only [map_add, hx0, hy0, add_zero])

private theorem liftedSquareTerm_eq (D : LatticeData) (n : ℤ) :
    liftedSquareTerm D n =
      ((-26 / 24 : ℂ) * ((n : ℂ) ^ 3 - n)) •
        (ghostC D (-n) * ghostC D n) := by
  apply TensorProduct.ext'
  intro v w
  simp only [liftedSquareTerm, BcGhostBRST.squareTerm, ghostC,
    LinearMap.smul_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply, TensorProduct.tmul_smul]

private theorem ghostSquareAnomaly_apply (D : LatticeData) (x : State D) :
    ghostSquareAnomaly D x = ∑ᶠ n : ℤ, liftedSquareTerm D n x := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    simp only [ghostSquareAnomaly, TensorProduct.map_tmul, LinearMap.id_apply]
    change v ⊗ₜ[ℂ] (∑ᶠ n : ℤ, BcGhostBRST.squareTerm n w) =
      ∑ᶠ n : ℤ, liftedSquareTerm D n (v ⊗ₜ[ℂ] w)
    simpa only [liftedSquareTerm, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.mk_apply] using
      (map_finsum (TensorProduct.mk ℂ (Carrier D) Fock v)
        (BcGhostBRST.squareTerm_finite w))
  | add x y hx hy =>
    rw [map_add, hx, hy]
    simp only [map_add]
    exact (finsum_add_distrib (liftedSquareTerm_finite D x)
      (liftedSquareTerm_finite D y)).symm

private theorem scaled_liftedSquareTerm_apply (D : LatticeData) (n : ℤ)
    (x : State D) :
    ((26 - (D.rank : ℂ)) / 26) • (liftedSquareTerm D n x) =
      (((D.rank : ℂ) - 26) / 24 * ((n : ℂ) ^ 3 - n)) •
        ((ghostC D (-n) * ghostC D n) x) := by
  rw [liftedSquareTerm_eq, LinearMap.smul_apply, smul_smul]
  congr 1
  ring

/-- The full signed anomaly is finite on every original tensor state. -/
theorem total_square_finite (D : LatticeData) (x : State D) :
    Function.HasFiniteSupport (fun n : ℤ =>
      (((D.rank : ℂ) - 26) / 24 * ((n : ℂ) ^ 3 - n)) •
        ((ghostC D (-n) * ghostC D n) x)) := by
  have h : Function.HasFiniteSupport (fun n : ℤ =>
      ((26 - (D.rank : ℂ)) / 26) • (liftedSquareTerm D n x)) :=
    (liftedSquareTerm_finite D x).fun_comp
      (smul_zero ((26 - (D.rank : ℂ)) / 26) :
        ((26 - (D.rank : ℂ)) / 26) • (0 : State D) = 0)
  simpa only [scaled_liftedSquareTerm_apply] using h

/-- The all-state, all-integer BRST square with the full signed (rank-26)/24 coefficient. -/
theorem total_square_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (x : State D) :
    (totalCharge D H ^ 2) x =
      ∑ᶠ n : ℤ, (((D.rank : ℂ) - 26) / 24 * ((n : ℂ) ^ 3 - n)) •
        ((ghostC D (-n) * ghostC D n) x) := by
  classical
  -- One finite capture for the two state-action families. In particular, the
  -- right-hand finsum has genuine finite support even away from pure tensors.
  have hg := liftedSquareTerm_finite D x
  have hf := total_square_finite D x
  let s : Finset ℤ := hg.toFinset ∪ hf.toFinset
  have hsg : Function.support (fun n : ℤ => liftedSquareTerm D n x) ⊆
      (s : Set ℤ) := by
    intro n hn
    exact Finset.mem_union_left _ (hg.mem_toFinset.mpr hn)
  have hsf : Function.support (fun n : ℤ =>
      (((D.rank : ℂ) - 26) / 24 * ((n : ℂ) ^ 3 - n)) •
        ((ghostC D (-n) * ghostC D n) x)) ⊆ (s : Set ℤ) := by
    intro n hn
    exact Finset.mem_union_right _ (hf.mem_toFinset.mpr hn)
  rw [total_square_anomaly D H hHG hGH, LinearMap.smul_apply,
    ghostSquareAnomaly_apply D x,
    finsum_eq_sum_of_support_subset _ hsg,
    finsum_eq_sum_of_support_subset _ hsf, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun n hn => scaled_liftedSquareTerm_apply D n x)

end D5.S3.VertexAlgebra.LatticeBRST
