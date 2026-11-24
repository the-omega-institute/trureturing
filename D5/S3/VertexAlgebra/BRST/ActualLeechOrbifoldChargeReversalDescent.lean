/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldChargeReversalDescent
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldChargeReversalDescent
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: Complex-linear plane charge reversal on actual ghost-one relative BRST cohomology. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldPlaneChargeReversal
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeInvariantForm
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws

/-!
The original plane involution acts on the relative kernel/image quotient and
preserves the literal momentum Lie bracket and the native BPZ form.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped DirectSum TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechOrbifoldCriticalMatter (Matter matter hyperbolicPlane)
open D5.S3.Quantum.Fermionic.BcGhostChargeTensor (liftGhost)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open LatticeGeneratingFieldLocality (Charge)
open LatticeInvolution (theta)
open RelativeBracket (B N Degree current relative_iff nativeValue
  bracket bracket_mk MomentumH1 momentumBracket momentumBracket_incl nativeRelativeBPZ
  nativeRelativeBPZ_incl_mk)
open RelativeCohomology (GradedCycles GradedBoundaries GradedCohomology)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open SourceBPZ.SourcePairingLaws (sourcePairing_theta)
open private gradedBoundaryMap
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private degree_shell native_mem native_degree native_closed cycleOf nativeValue_injective
  native_add native_smul native_boundary boundary_of_native native_cycleCurrent
  from D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket

local instance chargeReversalStateAddCommGroup : AddCommGroup ComplexState :=
  TensorProduct.addCommGroup

private theorem chargeReversal_liftGhost (F : Module.End ℂ Fock) (x : ComplexState) :
    chargeReversal (liftGhost F x) = liftGhost F (chargeReversal x) := by
  have h : chargeReversal.comp (liftGhost F) = (liftGhost F).comp chargeReversal := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, liftGhost, TensorProduct.map_tmul, LinearMap.id_apply,
      chargeReversal_tmul]
  exact LinearMap.congr_fun h x

/-- The literal antighost modes commute with plane charge reversal. -/
theorem chargeReversal_ghostB (n : ℤ) (x : ComplexState) :
    chargeReversal (VirasoroBRST.ghostB matter n x) =
      VirasoroBRST.ghostB matter n (chargeReversal x) :=
  chargeReversal_liftGhost _ x

/-- The literal ghost modes commute with plane charge reversal. -/
theorem chargeReversal_ghostC (n : ℤ) (x : ComplexState) :
    chargeReversal (VirasoroBRST.ghostC matter n x) =
      VirasoroBRST.ghostC matter n (chargeReversal x) :=
  chargeReversal_liftGhost _ x

theorem chargeReversal_N (x : ComplexState) :
    chargeReversal (N x) = N (chargeReversal x) :=
  chargeReversal_liftGhost _ x

theorem chargeReversal_b0 (x : ComplexState) :
    chargeReversal (b0 x) = b0 (chargeReversal x) :=
  chargeReversal_ghostB 0 x

/-- Both summands of the original total energy commute with the involution. -/
theorem chargeReversal_E (x : ComplexState) :
    chargeReversal (E x) = E (chargeReversal x) := by
  have h : chargeReversal.comp E = E.comp chargeReversal := by
    apply TensorProduct.ext'
    intro v g
    simp only [LinearMap.comp_apply, E, VirasoroBRST.Ltotal, VirasoroBRST.matterMode,
      VirasoroBRST.ghostVirasoro, LinearMap.add_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, map_add, chargeReversal_tmul, matterChargeReversal_virasoro]
  exact LinearMap.congr_fun h x

/-- Covariance of the original antighost-descended current on arbitrary states. -/
theorem chargeReversal_current (x y : ComplexState) :
    chargeReversal (current x y) = current (chargeReversal x) (chargeReversal y) := by
  change chargeReversal (originalMode 0 (B x) y) =
    originalMode 0 (B (chargeReversal x)) (chargeReversal y)
  rw [chargeReversal_originalMode, chargeReversal_ghostB (-1) x]

local notation "PlaneMomentum" => Charge hyperbolicPlane
local notation "Cycles" => fun p : PlaneMomentum => GradedCycles planeFrame planeBasis p 1
local notation "Boundaries" => fun p : PlaneMomentum => GradedBoundaries planeFrame planeBasis p 1
local notation "H" => fun p : PlaneMomentum => GradedCohomology planeFrame planeBasis p 1

local instance chargeReversalShellAddCommGroup (p : PlaneMomentum) :
    AddCommGroup (relativeShell p) := Submodule.addCommGroup _
local instance chargeReversalCyclesAddCommGroup (p : PlaneMomentum) :
    AddCommGroup (Cycles p) := Submodule.addCommGroup _

private theorem chargeReversal_shell {p : PlaneMomentum} {x : ComplexState}
    (hx : reassoc x ∈ relativeShell p) : reassoc (chargeReversal x) ∈ relativeShell (-p) := by
  obtain ⟨hp, hb, he⟩ := (relative_iff p x).mp hx
  refine (relative_iff (-p) (chargeReversal x)).mpr ⟨?_, ?_, ?_⟩
  · exact (chargeReversal_momentum_iff p x).mpr hp
  · rw [← chargeReversal_b0, hb, map_zero]
  · rw [← chargeReversal_E, he, map_zero]

private theorem chargeReversal_degree {g : ℤ} {x : ComplexState} (hx : Degree g x) :
    Degree g (chargeReversal x) := by
  change N (chargeReversal x) = (g : ℂ) • chargeReversal x
  rw [← chargeReversal_N, hx, map_smul]

private theorem chargeReversal_closed {x : ComplexState} (hx : Q x = 0) :
    Q (chargeReversal x) = 0 := by
  rw [← chargeReversal_Q, hx, map_zero]

/-- The original involution carries the actual relative ghost-one cycles at p to those at -p. -/
def chargeReversalCycles (p : PlaneMomentum) : Cycles p →ₗ[ℂ] Cycles (-p) := by
  let reverse (x : Cycles p) : Cycles (-p) :=
    cycleOf (chargeReversal (nativeValue x)) (chargeReversal_shell (native_mem x))
      (chargeReversal_degree (native_degree x)) (chargeReversal_closed (native_closed x))
  have value (x : Cycles p) : nativeValue (reverse x) = chargeReversal (nativeValue x) :=
    reassoc.symm_apply_apply _
  exact {
    toFun := reverse
    map_add' x y := nativeValue_injective _ (by simp only [value, native_add, map_add])
    map_smul' c x := nativeValue_injective _ (by
      simp only [value, native_smul, map_smul, RingHom.id_apply]) }

theorem chargeReversalCycles_nativeValue {p : PlaneMomentum} (x : Cycles p) :
    nativeValue (chargeReversalCycles p x) = chargeReversal (nativeValue x) :=
  reassoc.symm_apply_apply _

/-- An actual Q-boundary is sent to Q of the reversed relative ghost-zero primitive. -/
theorem chargeReversal_mem_boundaries {p : PlaneMomentum} {x : Cycles p}
    (hx : x ∈ Boundaries p) : chargeReversalCycles p x ∈ Boundaries (-p) := by
  obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
  let v := reassoc.symm a.val.val
  have hs : reassoc v ∈ relativeShell p := by
    simpa only [v, reassoc.apply_symm_apply] using a.val.property
  have hd : Degree 0 v := by
    simpa only [sub_self] using (degree_shell p _ a.val).mp a.property
  apply boundary_of_native _ (chargeReversal v) (chargeReversal_shell hs)
    (chargeReversal_degree hd)
  rw [chargeReversalCycles_nativeValue, native_boundary, chargeReversal_Q]

private theorem chargeReversal_le_comap (p : PlaneMomentum) :
    Boundaries p ≤ Submodule.comap (chargeReversalCycles p) (Boundaries (-p)) :=
  fun _ hx => Submodule.mem_comap.mpr (chargeReversal_mem_boundaries hx)

set_option maxHeartbeats 1500000 in
-- The kernel checks the nested submodule instances for both momentum quotients.
/-- Charge reversal on the actual ghost-one kernel/image quotient in each momentum. -/
def chargeReversalCohomology (p : PlaneMomentum) : H p →ₗ[ℂ] H (-p) :=
  Submodule.mapQ (R := ℂ) (R₂ := ℂ) (M := Cycles p) (M₂ := Cycles (-p))
    (τ₁₂ := RingHom.id ℂ) (Boundaries p) (Boundaries (-p)) (chargeReversalCycles p)
    (chargeReversal_le_comap p)

@[simp] theorem chargeReversalCohomology_mk {p : PlaneMomentum} (x : Cycles p) :
    chargeReversalCohomology p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (chargeReversalCycles p x) := rfl

private theorem nativeValue_transport {p q : PlaneMomentum} (h : p = q) (x : Cycles p) :
    nativeValue (h ▸ x : Cycles q) = nativeValue x := by
  subst q
  rfl

private theorem quotient_mk_transport {p q : PlaneMomentum} (h : p = q) (x : Cycles p) :
    (h ▸ (Submodule.Quotient.mk x : H p) : H q) =
      Submodule.Quotient.mk (h ▸ x : Cycles q) := by
  subst q
  rfl

/-- The two momentum-reversing quotient maps compose to the identity. -/
theorem chargeReversalCohomology_involutive (p : PlaneMomentum) (x : H p) :
    (neg_neg p ▸ chargeReversalCohomology (-p) (chargeReversalCohomology p x) : H p) = x := by
  refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
  simp only [chargeReversalCohomology_mk, quotient_mk_transport]
  apply congrArg (fun z : Cycles p => (Submodule.Quotient.mk z : H p))
  apply nativeValue_injective
  simp only [nativeValue_transport, chargeReversalCycles_nativeValue]
  exact chargeReversal_involutive _

/-- Covariance of the literal quotient bracket, with the momentum identity -(p+q) = -p+-q. -/
theorem chargeReversalCohomology_bracket (p q : PlaneMomentum) (x : H p) (y : H q) :
    (neg_add p q ▸ chargeReversalCohomology (p + q) (bracket p q x y) : H (-p + -q)) =
      bracket (-p) (-q) (chargeReversalCohomology p x) (chargeReversalCohomology q y) := by
  refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
  refine Submodule.Quotient.induction_on (Boundaries q) y fun b => ?_
  simp only [bracket_mk, chargeReversalCohomology_mk, quotient_mk_transport]
  apply congrArg (fun z : Cycles (-p + -q) => (Submodule.Quotient.mk z : H (-p + -q)))
  apply nativeValue_injective
  simp only [nativeValue_transport, chargeReversalCycles_nativeValue, native_cycleCurrent,
    chargeReversal_current]

local notation "incl" => DirectSum.lof ℂ PlaneMomentum H

private theorem incl_transport {p q : PlaneMomentum} (h : p = q) (x : H p) :
    incl q (h ▸ x : H q) = incl p x := by
  subst q
  rfl

/-- Complex-linear charge reversal on the existing finite-support momentum sum. -/
def chargeReversalMomentum : Module.End ℂ MomentumH1 :=
  DirectSum.toModule ℂ PlaneMomentum _ fun p => (incl (-p)).comp (chargeReversalCohomology p)

@[simp] theorem chargeReversalMomentum_incl (p : PlaneMomentum) (x : H p) :
    chargeReversalMomentum (incl p x) = incl (-p) (chargeReversalCohomology p x) := by
  simp only [chargeReversalMomentum, DirectSum.toModule_lof, LinearMap.comp_apply]

private theorem chargeReversalMomentum_involutive : Function.Involutive chargeReversalMomentum := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p x =>
    change chargeReversalMomentum (chargeReversalMomentum (incl p x)) = incl p x
    rw [chargeReversalMomentum_incl, chargeReversalMomentum_incl,
      ← incl_transport (neg_neg p), chargeReversalCohomology_involutive]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem chargeReversalMomentum_bracket (x y : MomentumH1) :
    chargeReversalMomentum (momentumBracket x y) =
      momentumBracket (chargeReversalMomentum x) (chargeReversalMomentum y) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of p x =>
    change chargeReversalMomentum (momentumBracket (incl p x) y) =
      momentumBracket (chargeReversalMomentum (incl p x)) (chargeReversalMomentum y)
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of q y =>
      change chargeReversalMomentum (momentumBracket (incl p x) (incl q y)) =
        momentumBracket (chargeReversalMomentum (incl p x)) (chargeReversalMomentum (incl q y))
      simp only [momentumBracket_incl, chargeReversalMomentum_incl]
      rw [← incl_transport (neg_add p q), chargeReversalCohomology_bracket]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- The hyperbolic-plane charge reversal is a complex Lie automorphism of actual relative H¹. -/
def chargeReversalLieEquiv : MomentumH1 ≃ₗ⁅ℂ⁆ MomentumH1 where
  toLieHom :=
    { toLinearMap := chargeReversalMomentum
      map_lie' := by
        intro x y
        exact chargeReversalMomentum_bracket x y }
  invFun := chargeReversalMomentum
  left_inv := chargeReversalMomentum_involutive
  right_inv := chargeReversalMomentum_involutive

theorem chargeReversalLieEquiv_involutive : Function.Involutive chargeReversalLieEquiv :=
  chargeReversalMomentum_involutive

/-- On each summand the automorphism is the map induced by the original involution on cycles. -/
@[simp] theorem chargeReversalLieEquiv_incl (p : PlaneMomentum) (x : H p) :
    chargeReversalLieEquiv (incl p x) = incl (-p) (chargeReversalCohomology p x) :=
  chargeReversalMomentum_incl p x

private theorem chargeReversal_matterPairing (a b : Matter) :
    NativeBPZ.matterPairing (matterChargeReversal a) (matterChargeReversal b) =
      NativeBPZ.matterPairing a b := by
  induction a using TensorProduct.inductionOn with
  | tmul u v =>
    induction b using TensorProduct.inductionOn with
    | tmul w z =>
      change sourcePairing hyperbolicPlane (theta hyperbolicPlane v) (theta hyperbolicPlane z) *
          NativeBPZ.orbifoldPairing u w =
        sourcePairing hyperbolicPlane v z * NativeBPZ.orbifoldPairing u w
      rw [sourcePairing_theta]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- Plane reversal preserves the original c(0)-inserted BPZ form on the carrier. -/
theorem chargeReversal_relativePairing (x y : ComplexState) :
    NativeBPZ.relativePairing (chargeReversal x) (chargeReversal y) =
      NativeBPZ.relativePairing x y := by
  induction x using TensorProduct.inductionOn with
  | tmul a g =>
    induction y using TensorProduct.inductionOn with
    | tmul b h =>
      simp only [chargeReversal_tmul, NativeBPZ.relativePairing_tmul,
        chargeReversal_matterPairing]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The automorphism is an isometry for the signed native BPZ form on actual H¹. -/
theorem chargeReversalLieEquiv_bpz (x y : MomentumH1) :
    nativeRelativeBPZ (chargeReversalLieEquiv x) (chargeReversalLieEquiv y) =
      nativeRelativeBPZ x y := by
  change nativeRelativeBPZ (chargeReversalMomentum x) (chargeReversalMomentum y) =
    nativeRelativeBPZ x y
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | of p x =>
    change nativeRelativeBPZ (chargeReversalMomentum (incl p x)) (chargeReversalMomentum y) =
      nativeRelativeBPZ (incl p x) y
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of q y =>
      change nativeRelativeBPZ (chargeReversalMomentum (incl p x))
        (chargeReversalMomentum (incl q y)) = nativeRelativeBPZ (incl p x) (incl q y)
      refine Submodule.Quotient.induction_on (Boundaries p) x fun a => ?_
      refine Submodule.Quotient.induction_on (Boundaries q) y fun b => ?_
      simp only [chargeReversalMomentum_incl, chargeReversalCohomology_mk,
        nativeRelativeBPZ_incl_mk, chargeReversalCycles_nativeValue, chargeReversal_relativePairing]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
