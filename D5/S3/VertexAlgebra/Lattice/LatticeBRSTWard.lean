/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTWard
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTWard
   mirror-E: none(waiver:algebraic-total-brst-ward)
   anchors: []
   utility: none
   digest: Actual total BRST Ward identities, finite covariance and square commutators. -/

import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCovariance
import D5.S3.Quantum.Fermionic.BcGhostSquare
import D5.S3.Quantum.Fermionic.BcGhostChargeTensor

/-! All-integer Ward identities and square commutators of the original total charge. -/


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct
open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeMatterGhostCoupling
open D5.S3.Quantum.Fermionic
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock (b c)
open private lift_mul from D5.S3.Quantum.Fermionic.BcGhostChargeTensor
open private cc_c squareAnomaly_b squareAnomaly_c from
  D5.S3.Quantum.Fermionic.BcGhostSquare

noncomputable section
namespace D5.S3.VertexAlgebra.LatticeBRST

/-- Identity on the original all-charge matter carrier, tensored with the actual cubic. -/
def ghostCharge (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id BcGhostBRST.Qg

/-- The actual matter coupling plus the actual cubic ghost charge. -/
def totalCharge (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) := T D H + ghostCharge D

/-- The original finite pure-c Ward operator, lifted to the matter tensor carrier. -/
def ghostR (D : LatticeData) (r : ℤ) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id (BcGhostBRST.R r)

/-- The already established native ghost square, on the actual tensor carrier. -/
def ghostSquareAnomaly (D : LatticeData) : Module.End ℂ (State D) :=
  TensorProduct.map LinearMap.id BcGhostBRST.squareAnomaly

-- This linear packaging uses the existing tensor lift, not a new representation.
private def lift (D : LatticeData) :
    Module.End ℂ Fock →ₗ[ℂ] Module.End ℂ (State D) where
  toFun := BcGhostChargeTensor.liftGhost (M := Carrier D)
  map_add' A B := by
    apply TensorProduct.ext'
    intro v w
    simp only [BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.add_apply, TensorProduct.tmul_add]
  map_smul' a A := by
    apply TensorProduct.ext'
    intro v w
    simp only [BcGhostChargeTensor.liftGhost, TensorProduct.map_tmul,
      LinearMap.id_apply, LinearMap.smul_apply, RingHom.id_apply,
      TensorProduct.tmul_smul]

private theorem lift_product (D : LatticeData) (A B : Module.End ℂ Fock) :
    lift D (A * B) = lift D A * lift D B := by
  exact lift_mul A B

private theorem ghost_ward_b (D : LatticeData) (r : ℤ) :
    ghostCharge D * ghostB D r + ghostB D r * ghostCharge D =
      ghostVirasoro D r := by
  change lift D BcGhostBRST.Qg * lift D (b r) +
    lift D (b r) * lift D BcGhostBRST.Qg = lift D (BcGhostVirasoro.L r)
  simpa only [map_add, lift_product] using
    congrArg (lift D) (BcGhostBRST.ward_b r)

private theorem ghost_ward_c (D : LatticeData) (r : ℤ) :
    ghostCharge D * ghostC D r + ghostC D r * ghostCharge D = ghostR D r := by
  change lift D BcGhostBRST.Qg * lift D (c r) +
    lift D (c r) * lift D BcGhostBRST.Qg = lift D (BcGhostBRST.R r)
  simpa only [map_add, lift_product] using
    congrArg (lift D) (BcGhostBRST.ward_c r)

/-- Both actual summands contribute to the all-integer b Ward identity. -/
theorem total_ward_b (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    totalCharge D H * ghostB D r + ghostB D r * totalCharge D H =
      matterMode D H r + ghostVirasoro D r := by
  calc
    _ = (T D H * ghostB D r + ghostB D r * T D H) +
        (ghostCharge D * ghostB D r + ghostB D r * ghostCharge D) := by
      unfold totalCharge
      noncomm_ring
    _ = _ := by rw [LatticeMatterGhostCoupling.ward_b, ghost_ward_b]

/-- The matter summand anticommutes with c; the cubic supplies the actual R. -/
theorem total_ward_c (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    totalCharge D H * ghostC D r + ghostC D r * totalCharge D H = ghostR D r := by
  calc
    _ = (T D H * ghostC D r + ghostC D r * T D H) +
        (ghostCharge D * ghostC D r + ghostC D r * ghostCharge D) := by
      unfold totalCharge
      noncomm_ring
    _ = _ := by rw [LatticeMatterGhostCoupling.ward_c, ghost_ward_c, zero_add]

/-- Reuse the native ghost-only square, without a new signed double-sum argument. -/
theorem ghostCharge_square (D : LatticeData) :
    ghostCharge D * ghostCharge D = ghostSquareAnomaly D := by
  change lift D BcGhostBRST.Qg * lift D BcGhostBRST.Qg =
    lift D BcGhostBRST.squareAnomaly
  rw [← lift_product D, BcGhostBRST.square_anomaly]

/-- The matching native b square commutator, with the supplier's exact coefficient. -/
theorem ghostSquareAnomaly_b (D : LatticeData) (r : ℤ) :
    ghostSquareAnomaly D * ghostB D r - ghostB D r * ghostSquareAnomaly D =
      BcGhostBRST.anomalyCoefficient r • ghostC D r := by
  change lift D BcGhostBRST.squareAnomaly * lift D (b r) -
    lift D (b r) * lift D BcGhostBRST.squareAnomaly =
      BcGhostBRST.anomalyCoefficient r • lift D (c r)
  simpa only [map_sub, map_smul, lift_product] using
    congrArg (lift D) (squareAnomaly_b r)

/-- The matching native c square commutator. -/
theorem ghostSquareAnomaly_c (D : LatticeData) (r : ℤ) :
    ghostSquareAnomaly D * ghostC D r - ghostC D r * ghostSquareAnomaly D = 0 := by
  change lift D BcGhostBRST.squareAnomaly * lift D (c r) -
    lift D (c r) * lift D BcGhostBRST.squareAnomaly = 0
  simpa only [map_sub, map_zero, lift_product] using
    congrArg (lift D) (squareAnomaly_c r)

-- Pass the already proved cc_c relation through the actual finite R action.
private theorem R_c (r s : ℤ) :
    BcGhostBRST.R r * c s - c s * BcGhostBRST.R r = 0 := by
  apply LinearMap.ext
  intro w
  have hw := BcGhostBRST.rTerm_finite r w
  have hc := BcGhostBRST.rTerm_finite r (c s w)
  have hmap := hw.fun_comp (map_zero (c s))
  change (∑ᶠ p : ℤ, BcGhostBRST.rTerm r p (c s w)) -
    c s (∑ᶠ p : ℤ, BcGhostBRST.rTerm r p w) = 0
  rw [map_finsum (c s) hw, ← finsum_sub_distrib hc hmap]
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  have h := LinearMap.congr_fun (cc_c p (r-p) s) w
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at h
  simp only [BcGhostBRST.rTerm, LinearMap.smul_apply, map_smul, Module.End.mul_apply]
  rw [← smul_sub, h, smul_zero]

private theorem summand_R (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (m r : ℤ) :
    summand D H m * ghostR D r - ghostR D r * summand D H m = 0 := by
  apply TensorProduct.ext'
  intro v w
  have h := LinearMap.congr_fun (sub_eq_zero.mp (R_c r (-m))) w
  simp only [Module.End.mul_apply] at h
  simp only [summand, ghostR, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply]
  rw [h, sub_self]

/-- One common finite capture of x and R_r x proves the actual T-R commutator.
The capture is state dependent; no finite support of the operator family is asserted. -/
theorem T_R (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    T D H * ghostR D r - ghostR D r * T D H = 0 := by
  classical
  apply LinearMap.ext
  intro x
  obtain ⟨s, hs⟩ := common_capture D H {x, ghostR D r x}
  have hx := hs x (by simp)
  have hR := hs (ghostR D r x) (by simp)
  change T D H (ghostR D r x) - ghostR D r (T D H x) = 0
  rw [finite_capture D H _ s hR, finite_capture D H _ s hx, map_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro m hm
  exact LinearMap.congr_fun (summand_R D H m r) x

private theorem ghostCharge_R (D : LatticeData) (r : ℤ) :
    ghostCharge D * ghostR D r - ghostR D r * ghostCharge D = 0 := by
  calc
    _ = (ghostCharge D * ghostCharge D) * ghostC D r -
        ghostC D r * (ghostCharge D * ghostCharge D) := by
      rw [← ghost_ward_c D r]
      noncomm_ring
    _ = 0 := by rw [ghostCharge_square, ghostSquareAnomaly_c]

/-- The full charge commutes with its actual c Ward operator. -/
theorem total_R (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    totalCharge D H * ghostR D r - ghostR D r * totalCharge D H = 0 := by
  calc
    _ = (T D H * ghostR D r - ghostR D r * T D H) +
        (ghostCharge D * ghostR D r - ghostR D r * ghostCharge D) := by
      unfold totalCharge
      noncomm_ring
    _ = 0 := by rw [T_R, ghostCharge_R, add_zero]

private theorem ghostCharge_matterMode (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    ghostCharge D * matterMode D H r - matterMode D H r * ghostCharge D = 0 := by
  apply TensorProduct.ext'
  intro v w
  simp only [ghostCharge, matterMode, Module.End.mul_apply, LinearMap.sub_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.zero_apply, sub_self]

private theorem ghost_mixed_anomaly (D : LatticeData) (r : ℤ) :
    ghostCharge D * ghostVirasoro D r - ghostVirasoro D r * ghostCharge D =
      ((26/12 : ℂ) * ((r : ℂ)^3-r)) • ghostC D r := by
  change lift D BcGhostBRST.Qg * lift D (BcGhostVirasoro.L r) -
    lift D (BcGhostVirasoro.L r) * lift D BcGhostBRST.Qg =
      ((26/12 : ℂ) * ((r : ℂ)^3-r)) • lift D (c r)
  simpa only [map_sub, map_smul, lift_product] using
    congrArg (lift D) (BcGhostBRST.mixed_anomaly r)

/-- The negative rank contribution and the positive 26 contribution combine exactly. -/
theorem total_covariance (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (r : ℤ) :
    totalCharge D H * (matterMode D H r + ghostVirasoro D r) -
      (matterMode D H r + ghostVirasoro D r) * totalCharge D H =
        (((26-(D.rank : ℂ))/12) * ((r : ℂ)^3-r)) • ghostC D r := by
  calc
    _ = (T D H * (matterMode D H r + ghostVirasoro D r) -
          (matterMode D H r + ghostVirasoro D r) * T D H) +
        (ghostCharge D * matterMode D H r - matterMode D H r * ghostCharge D) +
        (ghostCharge D * ghostVirasoro D r - ghostVirasoro D r * ghostCharge D) := by
      unfold totalCharge
      noncomm_ring
    _ = _ := by
      rw [LatticeMatterGhostCovariance.covariance D H hHG hGH r,
        ghostCharge_matterMode, ghost_mixed_anomaly]
      simp only [add_zero, ← add_smul]
      congr 1
      ring

/-- Ordinary [Q²,b] = [Q,{Q,b}] has no factor of one half. -/
theorem total_square_b (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (r : ℤ) :
    (totalCharge D H * totalCharge D H) * ghostB D r -
      ghostB D r * (totalCharge D H * totalCharge D H) =
        (((26-(D.rank : ℂ))/12) * ((r : ℂ)^3-r)) • ghostC D r := by
  calc
    _ = totalCharge D H * (totalCharge D H * ghostB D r +
          ghostB D r * totalCharge D H) -
        (totalCharge D H * ghostB D r + ghostB D r * totalCharge D H) *
          totalCharge D H := by noncomm_ring
    _ = _ := by rw [total_ward_b, total_covariance D H hHG hGH r]

/-- The c square commutator uses the statewise finite T-R proof. -/
theorem total_square_c (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    (totalCharge D H * totalCharge D H) * ghostC D r -
      ghostC D r * (totalCharge D H * totalCharge D H) = 0 := by
  calc
    _ = totalCharge D H * (totalCharge D H * ghostC D r +
          ghostC D r * totalCharge D H) -
        (totalCharge D H * ghostC D r + ghostC D r * totalCharge D H) *
          totalCharge D H := by noncomm_ring
    _ = 0 := by rw [total_ward_c, total_R]

/-- Scaling the native ghost square gives the predicted (rank-26)/24 pure-c anomaly.
This definition makes no assertion that it is already the full total square. -/
def squareResidual (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) :=
  totalCharge D H * totalCharge D H -
    ((26-(D.rank : ℂ))/26) • ghostSquareAnomaly D

private theorem residual_commutator (D : LatticeData)
    (A S C : Module.End ℂ (State D)) (a : ℂ) :
    (A - a • S) * C - C * (A - a • S) =
      (A * C - C * A) - a • (S * C - C * S) := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

/-- The concrete scaled residual commutes with every actual tensor b mode. -/
theorem squareResidual_b (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
    (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1) (r : ℤ) :
    squareResidual D H * ghostB D r = ghostB D r * squareResidual D H := by
  apply sub_eq_zero.mp
  change (totalCharge D H * totalCharge D H -
      ((26-(D.rank : ℂ))/26) • ghostSquareAnomaly D) * ghostB D r -
    ghostB D r * (totalCharge D H * totalCharge D H -
      ((26-(D.rank : ℂ))/26) • ghostSquareAnomaly D) = 0
  rw [residual_commutator, total_square_b D H hHG hGH r,
    ghostSquareAnomaly_b, smul_smul]
  have hcoeff : (((26-(D.rank : ℂ))/26) * BcGhostBRST.anomalyCoefficient r) =
      (((26-(D.rank : ℂ))/12) * ((r : ℂ)^3-r)) := by
    unfold BcGhostBRST.anomalyCoefficient
    ring
  rw [hcoeff, sub_self]

/-- The same concrete residual commutes with every actual tensor c mode. -/
theorem squareResidual_c (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (r : ℤ) :
    squareResidual D H * ghostC D r = ghostC D r * squareResidual D H := by
  apply sub_eq_zero.mp
  change (totalCharge D H * totalCharge D H -
      ((26-(D.rank : ℂ))/26) • ghostSquareAnomaly D) * ghostC D r -
    ghostC D r * (totalCharge D H * totalCharge D H -
      ((26-(D.rank : ℂ))/26) • ghostSquareAnomaly D) = 0
  rw [residual_commutator, total_square_c, ghostSquareAnomaly_c, smul_zero, sub_self]

end D5.S3.VertexAlgebra.LatticeBRST
