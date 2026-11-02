/- GID: D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeMatterGhostDegree
   mirror-E: none(waiver:algebraic-total-brst)
   anchors: []
   utility: none
   digest: Ghost degrees of the matter coupling, total charge and square residual. -/

import D5.S3.Quantum.Fermionic.BcGhostBRSTDegree
import D5.S3.Quantum.Fermionic.BcGhostChargeTensor
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling

/-! Ghost-number degrees of the original matter coupling, cubic lift and total square residual. -/


set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostCharge

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeMatterGhostDegree

open D5.S3.Quantum.Fermionic

/-- The exact number operator used by charged_commutant_vanishes. -/
abbrev tensorNumber (D : LatticeData) : Module.End ℂ (State D) :=
  BcGhostChargeTensor.number (M := Carrier D)

private theorem summand_ghost_number (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m : ℤ) :
    tensorNumber D * summand D H m - summand D H m * tensorNumber D =
      summand D H m := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (ghost_number_relations.2.2 (-m)) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [tensorNumber, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
    summand, LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub, h]

/-- Degree one of the actual matter coupling; one finite set captures x and N x. -/
theorem tensorNumber_T (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    tensorNumber D * T D H - T D H * tensorNumber D = T D H := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨s, hs⟩ := common_capture D H {x, tensorNumber D x}
  have hx := hs x (by simp)
  have hNx := hs (tensorNumber D x) (by simp)
  change tensorNumber D (T D H x) - T D H (tensorNumber D x) = T D H x
  calc
    _ = ∑ m ∈ s, (tensorNumber D (summand D H m x) -
        summand D H m (tensorNumber D x)) := by
      rw [LatticeMatterGhostCoupling.finite_capture D H x s hx,
        LatticeMatterGhostCoupling.finite_capture D H (tensorNumber D x) s hNx, map_sum,
        Finset.sum_sub_distrib]
    _ = ∑ m ∈ s, summand D H m x := by
      apply Finset.sum_congr rfl
      intro m hm
      exact LinearMap.congr_fun (summand_ghost_number D H m) x
    _ = T D H x := (LatticeMatterGhostCoupling.finite_capture D H x s hx).symm

/-- The actual tensor lift of the original cubic charge. -/
abbrev G (D : LatticeData) : Module.End ℂ (State D) :=
  BcGhostChargeTensor.liftGhost (M := Carrier D) BcGhostBRST.Qg

/-- The actual total charge, with no additional c-zero term. -/
abbrev Q (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) := T D H + G D

/-- The degree-two residual in the anomaly comparison. -/
abbrev E (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) :=
  Q D H ^ 2 - ((26 - (D.rank : ℂ)) / 26) • (G D ^ 2)

theorem tensorNumber_G (D : LatticeData) :
    tensorNumber D * G D - G D * tensorNumber D = G D := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun BcGhostBRST.ghost_number_Qg w
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  simp only [tensorNumber, G, BcGhostChargeTensor.number, BcGhostChargeTensor.liftGhost,
    LinearMap.sub_apply, Module.End.mul_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub, h]

theorem tensorNumber_Q (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    tensorNumber D * Q D H - Q D H * tensorNumber D = Q D H := by
  change tensorNumber D * (T D H + G D) -
    (T D H + G D) * tensorNumber D = T D H + G D
  calc
    _ = (tensorNumber D * T D H - T D H * tensorNumber D) +
        (tensorNumber D * G D - G D * tensorNumber D) := by noncomm_ring
    _ = _ := by rw [tensorNumber_T, tensorNumber_G]

private theorem square_degree (D : LatticeData) (A : Module.End ℂ (State D))
    (hA : tensorNumber D * A - A * tensorNumber D = A) :
    tensorNumber D * A ^ 2 - A ^ 2 * tensorNumber D = (2 : ℂ) • A ^ 2 := by
  simp only [pow_two]
  calc
    _ = (tensorNumber D * A - A * tensorNumber D) * A +
        A * (tensorNumber D * A - A * tensorNumber D) := by
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    _ = _ := by simp only [hA, two_smul]

theorem tensorNumber_E (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    tensorNumber D * E D H - E D H * tensorNumber D = (2 : ℂ) • E D H := by
  change tensorNumber D * (Q D H ^ 2 - ((26 - (D.rank : ℂ)) / 26) • (G D ^ 2)) -
      (Q D H ^ 2 - ((26 - (D.rank : ℂ)) / 26) • (G D ^ 2)) * tensorNumber D =
        (2 : ℂ) • (Q D H ^ 2 - ((26 - (D.rank : ℂ)) / 26) • (G D ^ 2))
  calc
    _ = (tensorNumber D * Q D H ^ 2 - Q D H ^ 2 * tensorNumber D) -
        ((26 - (D.rank : ℂ)) / 26) •
          (tensorNumber D * G D ^ 2 - G D ^ 2 * tensorNumber D) := by
      simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
      abel
    _ = (2 : ℂ) • Q D H ^ 2 -
        ((26 - (D.rank : ℂ)) / 26) • ((2 : ℂ) • G D ^ 2) := by
      rw [square_degree D (Q D H) (tensorNumber_Q D H),
        square_degree D (G D) (tensorNumber_G D)]
    _ = _ := by module

end D5.S3.VertexAlgebra.LatticeMatterGhostDegree
