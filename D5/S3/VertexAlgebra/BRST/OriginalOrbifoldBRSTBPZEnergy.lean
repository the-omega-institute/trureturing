/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Eigenspace.Basic]
   utility: none
   digest: Total Virasoro BPZ transposition and orthogonality of unequal energies. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Batteries.Tactic.OpenPrivate

/-! The charge and antighost Ward identities give opposite-mode transposition
for the total Virasoro action on the full native matter-ghost carrier. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZEnergy

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock)
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_b)
open OriginalOrbifoldBRSTBPZWard (betaTotal betaTotal_Q_ward)

open private ket_homogeneous parity_ket_charge ghost_adjoint tensor_adjoint from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTBPZWard
open private Q_parity b_parity parity_square from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private theorem ghost_b_adjoint (m : ℤ) (x y : Fock) :
    beta (BcGhostFock.b m x) y =
      (1 : ℂ) * beta (CountableOccupationFock.parity x) (BcGhostFock.b (-m) y) := by
  refine ghost_adjoint (BcGhostFock.b m) (BcGhostFock.b (-m)) 1 y ?_ x
  intro S
  rw [parity_ket_charge, map_smul, LinearMap.smul_apply, smul_eq_mul, one_mul]
  exact beta_b m (ket_homogeneous S) y

/-- Every native antighost mode transposes to the opposite mode with left ghost parity. -/
theorem betaTotal_b_ward (m : ℤ) (x y : State) :
    betaTotal (b m x) y = betaTotal (parity x) (b (-m) y) := by
  change betaTotal (TensorProduct.map LinearMap.id (BcGhostFock.b m) x) y =
    betaTotal (parity x) (TensorProduct.map LinearMap.id (BcGhostFock.b (-m)) y)
  simpa only [one_mul] using
    tensor_adjoint LinearMap.id LinearMap.id (BcGhostFock.b m) (BcGhostFock.b (-m))
      (1 : ℂ) (fun _ _ => rfl) (ghost_b_adjoint m) x y

private theorem betaTotal_Q_b (m : ℤ) (x y : State) :
    betaTotal (Q (b m x)) y = betaTotal x (b (-m) (Q y)) := by
  calc
    _ = -betaTotal (parity (b m x)) (Q y) :=
      eq_neg_iff_add_eq_zero.mpr (betaTotal_Q_ward (b m x) y)
    _ = betaTotal (b m (parity x)) (Q y) := by
      rw [b_parity, betaTotal.map_neg, LinearMap.neg_apply, neg_neg]
    _ = _ := by rw [betaTotal_b_ward, parity_square]

private theorem betaTotal_b_Q (m : ℤ) (x y : State) :
    betaTotal (b m (Q x)) y = betaTotal x (Q (b (-m) y)) := by
  calc
    _ = betaTotal (parity (Q x)) (b (-m) y) := betaTotal_b_ward m (Q x) y
    _ = -betaTotal (Q (parity x)) (b (-m) y) := by
      rw [Q_parity, betaTotal.map_neg, LinearMap.neg_apply, neg_neg]
    _ = _ := by
      rw [eq_neg_iff_add_eq_zero.mpr (betaTotal_Q_ward (parity x) (b (-m) y)),
        neg_neg, parity_square]

/-- The full BPZ form transposes each total Virasoro mode to the opposite mode. -/
theorem betaTotal_Ltotal_ward (m : ℤ) (x y : State) :
    betaTotal (VirasoroBRST.Ltotal matterDatum m x) y =
      betaTotal x (VirasoroBRST.Ltotal matterDatum (-m) y) := by
  have ward (n : ℤ) (z : State) :
      Q (b n z) + b n (Q z) = VirasoroBRST.Ltotal matterDatum n z :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_b matterDatum n) z
  rw [← ward m x, ← ward (-m) y, betaTotal.map_add, LinearMap.add_apply,
    (betaTotal x).map_add, betaTotal_Q_b, betaTotal_b_Q]
  exact add_comm _ _

/-- The actual total zero mode is self-transpose for the full BPZ form. -/
theorem betaTotal_L0_ward (x y : State) :
    betaTotal (VirasoroBRST.Ltotal matterDatum 0 x) y =
      betaTotal x (VirasoroBRST.Ltotal matterDatum 0 y) := by
  simpa only [neg_zero] using betaTotal_Ltotal_ward 0 x y

/-- Distinct eigenspaces of the actual total zero mode are BPZ orthogonal. -/
theorem betaTotal_eq_zero_of_ne_weight {a d : ℂ} {x y : State} (hne : a ≠ d)
    (hx : x ∈ (VirasoroBRST.Ltotal matterDatum 0).eigenspace a)
    (hy : y ∈ (VirasoroBRST.Ltotal matterDatum 0).eigenspace d) : betaTotal x y = 0 := by
  have h : a * betaTotal x y = d * betaTotal x y := by
    simpa only [Module.End.mem_eigenspace_iff.mp hx, Module.End.mem_eigenspace_iff.mp hy,
      map_smul, LinearMap.smul_apply, smul_eq_mul] using betaTotal_L0_ward x y
  have hmul : (a - d) * betaTotal x y = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

#print axioms betaTotal_Ltotal_ward
#print axioms betaTotal_eq_zero_of_ne_weight

end

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZEnergy
