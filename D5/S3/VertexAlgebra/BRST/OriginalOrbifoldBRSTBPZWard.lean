/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZWard
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldBRSTBPZWard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.TensorProduct]
   utility: none
   digest: BPZ Ward identities with ghost parity for the native full and relative BRST charges. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBPZ
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldMatterBPZ
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.RingTheory.TensorProduct.Maps

/-! The critical matter and ghost BPZ forms give a complex bilinear form on
the native tensor carrier. Inserting the ghost zero mode on the right gives
the relative form and reverses the sign in the parity Ward identity. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct

noncomputable section
namespace D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZWard

open D5.S3.Quantum.Fermionic
open CountableOccupationFock (Fock ket)
open BcGhostCharge (charge)
open BcGhostHermitian (Homogeneous)
open OriginalOrbifoldCriticalMatter (Matter State Q b matterDatum mode)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent (relativeStates relativeDifferential)
open OriginalOrbifoldMatterBPZ (matterBPZ matterBPZ_mode)
open OriginalOrbifoldBRSTGhostBPZ (beta beta_b beta_c beta_Qg)

open private parity_ket from D5.S3.Quantum.Fermionic.CountableOccupationFock
open private parity_zpow from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBPZ
open private zero_mixed_car from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTGhostBilinear
open private parity_mem_relativeStates from D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTDescent

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

/-- The literal tensor product of the critical matter and ghost BPZ forms. -/
def betaTotal : LinearMap.BilinForm ℂ State := matterBPZ.tmul beta

private theorem betaTotal_tmul (u v : Matter) (a d : Fock) :
    betaTotal (u ⊗ₜ[ℂ] a) (v ⊗ₜ[ℂ] d) = matterBPZ u v * beta a d := by
  change beta a d * matterBPZ u v = matterBPZ u v * beta a d
  exact mul_comm _ _

private theorem ket_homogeneous (S : Finset ℕ) : Homogeneous (charge S) (ket S) := by
  intro T hT
  by_cases h : S = T
  · subst T
    rfl
  · change Finsupp.single S (1 : ℂ) T ≠ 0 at hT
    exact (hT (Finsupp.single_eq_of_ne' h)).elim

private theorem parity_ket_charge (S : Finset ℕ) :
    CountableOccupationFock.parity (ket S) = (-1 : ℂ) ^ charge S • ket S := by
  have hodd : S.filter (fun j => ¬j % 2 = 0) = S.filter (fun j => j % 2 = 1) := by
    ext j
    have hj : (¬j % 2 = 0) ↔ j % 2 = 1 := by omega
    simp only [Finset.mem_filter, hj]
  have hcard := S.card_filter_add_card_filter_not (fun j => j % 2 = 0)
  rw [hodd] at hcard
  have hmod : (S.card : ℤ) % 2 = charge S % 2 := by
    unfold charge
    omega
  have hsign : (-1 : ℂ) ^ S.card = (-1 : ℂ) ^ charge S := by
    rw [← zpow_natCast (-1 : ℂ) S.card, parity_zpow (S.card : ℤ),
      parity_zpow (charge S), hmod]
  rw [parity_ket, hsign]

-- All three ghost adjoints extend from the same finite occupation basis.
private theorem ghost_adjoint (A B : Module.End ℂ Fock) (s : ℂ) (y : Fock)
    (h : ∀ S : Finset ℕ,
      beta (A (ket S)) y = s * beta (CountableOccupationFock.parity (ket S)) (B y))
    (x : Fock) :
    beta (A x) y = s * beta (CountableOccupationFock.parity x) (B y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply, mul_zero]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, mul_add]
  | single S a =>
    have hs : Finsupp.single S a = a • ket S := by simp [ket]
    rw [hs]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, h S]
    exact mul_left_comm _ _ _

private theorem ghost_c_adjoint (n : ℤ) (x y : Fock) :
    beta (BcGhostFock.c n x) y =
      (-1 : ℂ) * beta (CountableOccupationFock.parity x) (BcGhostFock.c (-n) y) := by
  refine ghost_adjoint (BcGhostFock.c n) (BcGhostFock.c (-n)) (-1) y ?_ x
  intro S
  rw [parity_ket_charge, map_smul, LinearMap.smul_apply, smul_eq_mul, ← mul_assoc,
    neg_one_mul]
  exact beta_c n (ket_homogeneous S) y

private theorem ghost_Qg_adjoint (x y : Fock) :
    beta (BcGhostBRST.Qg x) y =
      (-1 : ℂ) * beta (CountableOccupationFock.parity x) (BcGhostBRST.Qg y) := by
  refine ghost_adjoint BcGhostBRST.Qg BcGhostBRST.Qg (-1) y ?_ x
  intro S
  rw [parity_ket_charge, map_smul, LinearMap.smul_apply, smul_eq_mul, neg_one_mul]
  exact eq_neg_iff_add_eq_zero.mpr (beta_Qg (ket_homogeneous S) y)

private theorem ghost_b_zero_adjoint (x y : Fock) :
    beta (BcGhostFock.b 0 x) y =
      (1 : ℂ) * beta (CountableOccupationFock.parity x) (BcGhostFock.b 0 y) := by
  refine ghost_adjoint (BcGhostFock.b 0) (BcGhostFock.b 0) 1 y ?_ x
  intro S
  rw [parity_ket_charge, map_smul, LinearMap.smul_apply, smul_eq_mul, one_mul]
  simpa only [neg_zero] using beta_b 0 (ket_homogeneous S) y

private theorem tensor_adjoint (A B : Module.End ℂ Matter) (G H : Module.End ℂ Fock) (s : ℂ)
    (hm : ∀ u v : Matter, matterBPZ (A u) v = matterBPZ u (B v))
    (hg : ∀ a d : Fock, beta (G a) d = s * beta (CountableOccupationFock.parity a) (H d))
    (x y : State) :
    betaTotal (TensorProduct.map A G x) y =
      s * betaTotal (parity x) (TensorProduct.map B H y) := by
  induction x using TensorProduct.inductionOn generalizing y with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, mul_add]
  | tmul u a =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz, mul_add]
    | tmul v d =>
      simp only [parity, TensorProduct.map_tmul, LinearMap.id_apply, betaTotal_tmul, hm, hg]
      exact mul_left_comm _ _ _

private theorem summand_adjoint (m : ℤ) (x y : State) :
    betaTotal (VirasoroBRST.summand matterDatum m x) y =
      -betaTotal (parity x) (VirasoroBRST.summand matterDatum (-m) y) := by
  have h := tensor_adjoint (mode m) (mode (-m)) (BcGhostFock.c (-m)) (BcGhostFock.c m)
    (-1 : ℂ) (matterBPZ_mode m)
    (fun a d => by simpa only [neg_neg] using ghost_c_adjoint (-m) a d) x y
  change betaTotal (TensorProduct.map (mode m) (BcGhostFock.c (-m)) x) y =
    -betaTotal (parity x) (TensorProduct.map (mode (-m)) (BcGhostFock.c (-(-m))) y)
  rw [neg_neg]
  simpa only [neg_one_mul] using h

private theorem ghostCharge_adjoint (x y : State) :
    betaTotal (VirasoroBRST.ghostCharge matterDatum x) y =
      -betaTotal (parity x) (VirasoroBRST.ghostCharge matterDatum y) := by
  change betaTotal (TensorProduct.map LinearMap.id BcGhostBRST.Qg x) y =
    -betaTotal (parity x) (TensorProduct.map LinearMap.id BcGhostBRST.Qg y)
  simpa only [neg_one_mul] using
    tensor_adjoint LinearMap.id LinearMap.id BcGhostBRST.Qg BcGhostBRST.Qg
      (-1 : ℂ) (fun _ _ => rfl) ghost_Qg_adjoint x y

private theorem T_adjoint (x y : State) :
    betaTotal (VirasoroBRST.T matterDatum x) y =
      -betaTotal (parity x) (VirasoroBRST.T matterDatum y) := by
  let left : State →ₗ[ℂ] ℂ := betaTotal.flip y
  let right : State →ₗ[ℂ] ℂ := betaTotal (parity x)
  let term : ℤ → ℂ := fun m => right (VirasoroBRST.summand matterDatum m y)
  let reflect : ℤ ≃ ℤ :=
    { toFun := fun m => -m
      invFun := fun m => -m
      left_inv := fun m => neg_neg m
      right_inv := fun m => neg_neg m }
  change left (∑ᶠ m : ℤ, VirasoroBRST.summand matterDatum m x) =
    -right (∑ᶠ m : ℤ, VirasoroBRST.summand matterDatum m y)
  rw [map_finsum left (VirasoroBRST.summand_finite matterDatum x),
    map_finsum right (VirasoroBRST.summand_finite matterDatum y)]
  calc
    _ = ∑ᶠ m : ℤ, -term (reflect m) := by
      apply finsum_congr
      intro m
      exact summand_adjoint m x y
    _ = -(∑ᶠ m : ℤ, term (reflect m)) := finsum_neg_distrib _
    _ = _ := congrArg (fun z : ℂ => -z) (finsum_comp_equiv reflect (f := term))

/-- The native BRST charge is BPZ skew with parity on the left input. -/
theorem betaTotal_Q_ward (x y : State) :
    betaTotal (Q x) y + betaTotal (parity x) (Q y) = 0 := by
  change betaTotal (VirasoroBRST.T matterDatum x + VirasoroBRST.ghostCharge matterDatum x) y +
    betaTotal (parity x) (VirasoroBRST.T matterDatum y + VirasoroBRST.ghostCharge matterDatum y) = 0
  rw [betaTotal.map_add, LinearMap.add_apply, (betaTotal (parity x)).map_add,
    T_adjoint, ghostCharge_adjoint]
  abel

private abbrev c0 : Module.End ℂ State := VirasoroBRST.ghostC matterDatum 0
private abbrev R0 : Module.End ℂ State := VirasoroBRST.ghostR matterDatum 0

private def liftGhost : Module.End ℂ Fock →ₐ[ℂ] Module.End ℂ State :=
  Module.End.lTensorAlgHom ℂ Fock Matter

private theorem b_zero_c_zero_car : b 0 * c0 + c0 * b 0 = (1 : Module.End ℂ State) := by
  change liftGhost (BcGhostFock.b 0) * liftGhost (BcGhostFock.c 0) +
    liftGhost (BcGhostFock.c 0) * liftGhost (BcGhostFock.b 0) = 1
  simpa only [map_add, map_mul, map_one] using congrArg liftGhost zero_mixed_car

private theorem b_zero_R_zero_commute : b 0 * R0 = R0 * b 0 := by
  change liftGhost (BcGhostFock.b 0) * liftGhost (BcGhostBRST.R 0) =
    liftGhost (BcGhostBRST.R 0) * liftGhost (BcGhostFock.b 0)
  simpa only [map_mul] using
    congrArg liftGhost OriginalOrbifoldBRSTGhostBilinear.b_zero_commutes_R_zero

private theorem betaTotal_b_zero (x y : State) :
    betaTotal (b 0 x) y = betaTotal (parity x) (b 0 y) := by
  change betaTotal (TensorProduct.map LinearMap.id (BcGhostFock.b 0) x) y =
    betaTotal (parity x) (TensorProduct.map LinearMap.id (BcGhostFock.b 0) y)
  simpa only [one_mul] using
    tensor_adjoint LinearMap.id LinearMap.id (BcGhostFock.b 0) (BcGhostFock.b 0)
      (1 : ℂ) (fun _ _ => rfl) ghost_b_zero_adjoint x y

private theorem betaTotal_isotropic {x y : State} (hx : b 0 x = 0) (hy : b 0 y = 0) :
    betaTotal x y = 0 := by
  have hsplit : b 0 (c0 x) = x := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hx, map_zero, add_zero,
      Module.End.one_apply] using LinearMap.congr_fun b_zero_c_zero_car x
  calc
    betaTotal x y = betaTotal (b 0 (c0 x)) y :=
      congrArg (fun z : State => betaTotal z y) hsplit.symm
    _ = betaTotal (parity (c0 x)) (b 0 y) := betaTotal_b_zero (c0 x) y
    _ = 0 := by rw [hy, map_zero]

private theorem b_zero_R_zero {y : State} (hy : b 0 y = 0) : b 0 (R0 y) = 0 := by
  simpa only [Module.End.mul_apply, hy, map_zero] using
    LinearMap.congr_fun b_zero_R_zero_commute y

/-- The ambient BPZ form with the native c-zero mode inserted on the right. -/
def betaRelTotal : LinearMap.BilinForm ℂ relativeStates :=
  betaTotal.compl₁₂ relativeStates.subtype (c0.comp relativeStates.subtype)

/-- Native ghost parity restricted to the relative state space. -/
def parityRelative : Module.End ℂ relativeStates :=
  parity.restrict parity_mem_relativeStates

private theorem b_zero_of_relative (x : relativeStates) : b 0 (x : State) = 0 := by
  have hx := x.property
  change b 0 (x : State) = 0 ∧ VirasoroBRST.Ltotal matterDatum 0 (x : State) = 0 at hx
  exact hx.1

/-- On relative states the c-zero insertion gives the parity-twisted equality
with a positive right-hand sign. -/
theorem betaRelTotal_ward (x y : relativeStates) :
    betaRelTotal (relativeDifferential x) y =
      betaRelTotal (parityRelative x) (relativeDifferential y) := by
  let px : State := parity (x : State)
  have hpx : b 0 px = 0 := b_zero_of_relative (parityRelative x)
  have hc : Q (c0 (y : State)) + c0 (Q (y : State)) = R0 (y : State) :=
    LinearMap.congr_fun (VirasoroBRST.Q_ward_c matterDatum 0) (y : State)
  have hz : betaTotal px (Q (c0 (y : State))) + betaTotal px (c0 (Q (y : State))) = 0 := by
    rw [← (betaTotal px).map_add, hc]
    exact betaTotal_isotropic hpx (b_zero_R_zero (b_zero_of_relative y))
  change betaTotal (Q (x : State)) (c0 (y : State)) = betaTotal px (c0 (Q (y : State)))
  calc
    _ = -betaTotal px (Q (c0 (y : State))) :=
      eq_neg_iff_add_eq_zero.mpr (betaTotal_Q_ward (x : State) (c0 (y : State)))
    _ = _ := by rw [eq_neg_iff_add_eq_zero.mpr hz, neg_neg]

#print axioms betaTotal_Q_ward
#print axioms betaRelTotal_ward

end D5.S3.VertexAlgebra.OriginalOrbifoldBRSTBPZWard
