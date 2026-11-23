/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCartanAction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldCartanAction
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The original Cartan action on actual relative BRST cohomology. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum

/-!
The native antighost mode zero is the physical b(-1). Applied to a
zero-momentum degree-one representative, it removes the single c(1)
occupation with sign +1. Both vacuum fields then collapse the two tensor
convolutions to the literal plane Heisenberg mode.

proof_shape: reassoc_cartan_mode, cartan_zero_mode_of_momentum, cohomologyCartan_apply: content
admission_basis: escape-witness
escape_witness: The two vacuum supports identify the native coefficient
before restriction. The charge projector then gives a scalar on the
entire momentum fiber and induces the scalar on the graded quotient.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane matter)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear unitCharge)
open LatticeFiniteNegativeGeneration (neutralField neutralMode)
open LatticeQuartetContraction (chargeMatter chargeProject tp tp_tmul)
open RelativeCohomology (NativeShell nativeQ NativeCohomology
  GradedCycles GradedBoundaries GradedCohomology)
open TwistedGround.Orbifold
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket vacuum)
open private ghost_B_neg_down from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum
open private assoc_vacuum_left from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private right_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private nativeShellEquiv nativeQ_sq from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology
open private cycleMap cohomologyMap cohomologyMap_mk from
  D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

private abbrev orbVac := OriginalOrbifoldField.vacuumState leechData leechUnit
private abbrev planeCurrent := LatticeZeroMomentumBRST.current hyperbolicPlane

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local instance (p : Charge hyperbolicPlane) : AddCommGroup (NativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Charge hyperbolicPlane) (g : ℤ) :
    AddCommGroup (GradedCycles planeFrame planeBasis p g) := Submodule.addCommGroup _

/-- The pure level-one plane state with the actual orbifold and ghost vacua. -/
def cartanCurrent (i : Fin 2) : ComplexState :=
  (orbVac ⊗ₜ[ℂ] planeCurrent i) ⊗ₜ[ℂ] vacuum

/-- Physical b(-1) removes the c(1) occupation with coefficient +1. -/
theorem ghostB_minus_one_u (i : Fin 2) :
    VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i) = cartanCurrent i := by
  change (orbVac ⊗ₜ[ℂ] planeCurrent i) ⊗ₜ[ℂ] BcGhostFock.b (-1) (ket {1}) =
    (orbVac ⊗ₜ[ℂ] planeCurrent i) ⊗ₜ[ℂ] vacuum
  rw [ghost_B_neg_down]

/-- The same computation in normalized vertex mode indexing. -/
theorem originalAntighost_zero_u (i : Fin 2) :
    originalMode 0 originalAntighost (RelativeZeroMomentum.u i) = cartanCurrent i := by
  rw [originalAntighost_modes]
  exact ghostB_minus_one_u i

private theorem assoc_cartan_modes (i : Fin 2) (n : ℤ) :
    ((assocY (reassoc (cartanCurrent i)))[[n]]) =
      rightLift (tp (neutralMode hyperbolicPlane i n) LinearMap.id) := by
  simp only [cartanCurrent, reassoc, TensorProduct.assoc_tmul, assoc_vacuum_left,
    right_vacuum_modes]
  have hfield : LatticeAllStateField.Y hyperbolicPlane (planeCurrent i) =
      neutralField hyperbolicPlane i :=
    LatticeActualConformalState.current_state_field hyperbolicPlane i
  change rightLift (tp ((LatticeAllStateField.Y hyperbolicPlane (planeCurrent i))[[n]])
    LinearMap.id) = _
  rw [hfield, LatticeSugawaraCurrents.neutralField_ncoeff]

/-- Every native mode of the extracted current is the literal plane Heisenberg mode. -/
theorem reassoc_cartan_mode (i : Fin 2) (n : ℤ) (x : ComplexState) :
    reassoc (originalMode n (originalMode 0 originalAntighost (RelativeZeroMomentum.u i)) x) =
      rightLift (tp (neutralMode hyperbolicPlane i n) LinearMap.id) (reassoc x) := by
  rw [originalAntighost_zero_u, reassoc_originalMode, assoc_cartan_modes]

/-- The native linear endomorphism is the conjugate of the plane mode. -/
theorem original_cartan_mode (i : Fin 2) (n : ℤ) :
    originalMode n (VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i)) =
      (reassoc.symm.conjAlgEquiv ℂ)
        (rightLift (tp (neutralMode hyperbolicPlane i n) LinearMap.id)) := by
  apply LinearMap.ext
  intro x
  apply reassoc.injective
  have h := reassoc_cartan_mode i n x
  rw [originalAntighost_zero_u] at h
  rw [ghostB_minus_one_u]
  exact h.trans (reassoc.apply_symm_apply _).symm

/-- The Gram pairing of the i-th current with the integral plane momentum. -/
def cartanEigenvalue (i : Fin 2) (p : Charge hyperbolicPlane) : ℂ :=
  (bilinear hyperbolicPlane (unitCharge hyperbolicPlane i) p : ℂ)

theorem cartanEigenvalue_coordinates (p : Charge hyperbolicPlane) :
    cartanEigenvalue 0 p = (p (1 : Fin 2) : ℂ) ∧
      cartanEigenvalue 1 p = (p (0 : Fin 2) : ℂ) := by
  simp only [cartanEigenvalue, bilinear, unitCharge, hyperbolicPlane]
  norm_num [Fin.sum_univ_two]

@[simp] theorem cartanEigenvalue_zero (i : Fin 2) : cartanEigenvalue i 0 = 0 := by
  simp [cartanEigenvalue, bilinear]

private theorem plane_zero_mode_project (i : Fin 2) (p : Charge hyperbolicPlane)
    (v : Carrier hyperbolicPlane) :
    neutralMode hyperbolicPlane i 0 (chargeMatter p v) =
      cartanEigenvalue i p • chargeMatter p v := by
  change neutralMode hyperbolicPlane i 0 (Finsupp.single p (v p)) =
    cartanEigenvalue i p • Finsupp.single p (v p)
  exact LatticeSugawaraVirasoro.neutralMode_zero_single hyperbolicPlane i p (v p)

private theorem assoc_zero_mode_project (i : Fin 2) (p : Charge hyperbolicPlane) :
    rightLift (tp (neutralMode hyperbolicPlane i 0) LinearMap.id) * rightLift (chargeProject p) =
      cartanEigenvalue i p • rightLift (chargeProject p) := by
  have hplane :
      tp (neutralMode hyperbolicPlane i 0) LinearMap.id * chargeProject p =
        cartanEigenvalue i p • chargeProject p := by
    apply TensorProduct.ext'
    intro v b
    change neutralMode hyperbolicPlane i 0 (chargeMatter p v) ⊗ₜ[ℂ] b =
      cartanEigenvalue i p • (chargeMatter p v ⊗ₜ[ℂ] b)
    rw [plane_zero_mode_project, TensorProduct.smul_tmul']
  rw [← map_mul, hplane, map_smul]

private theorem assoc_zero_mode_of_momentum (i : Fin 2) (p : Charge hyperbolicPlane)
    (x : AssocState) (hx : rightLift (chargeProject p) x = x) :
    rightLift (tp (neutralMode hyperbolicPlane i 0) LinearMap.id) x =
      cartanEigenvalue i p • x := by
  simpa only [Module.End.mul_apply, LinearMap.smul_apply, hx] using
    LinearMap.congr_fun (assoc_zero_mode_project i p) x

/-- The original Cartan zero mode is scalar on the entire actual momentum fiber. -/
theorem cartan_zero_mode_of_momentum (i : Fin 2) (p : Charge hyperbolicPlane)
    (x : ComplexState) (hx : rightLift (chargeProject p) (reassoc x) = reassoc x) :
    originalMode 0 (VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i)) x =
      cartanEigenvalue i p • x := by
  have hb : originalMode 0 originalAntighost = VirasoroBRST.ghostB matter (-1) :=
    originalAntighost_modes 0
  rw [← hb]
  apply reassoc.injective
  rw [reassoc_cartan_mode, map_smul]
  exact assoc_zero_mode_of_momentum i p (reassoc x) hx

theorem cartan_zero_mode_on_native_shell (i : Fin 2) (p : Charge hyperbolicPlane)
    (x : NativeShell p) :
    originalMode 0 (VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i)) x.val =
      cartanEigenvalue i p • x.val :=
  cartan_zero_mode_of_momentum i p x.val ((mem_relativeShell_iff p (reassoc x.val)).mp x.property).1

/-- The original zero mode restricted in the native tensor association. -/
def nativeCartan (i : Fin 2) (p : Charge hyperbolicPlane) : Module.End ℂ (NativeShell p) :=
  (originalMode 0 (VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i))).restrict
    (fun x hx => by
      rw [cartan_zero_mode_on_native_shell i p (⟨x, hx⟩ : NativeShell p)]
      exact (NativeShell p).smul_mem _ hx)

theorem nativeCartan_eq_smul (i : Fin 2) (p : Charge hyperbolicPlane) :
    nativeCartan i p = cartanEigenvalue i p • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact cartan_zero_mode_on_native_shell i p x

private theorem nativeCartan_chain (i : Fin 2) (p : Charge hyperbolicPlane) :
    (nativeCartan i p).comp (nativeQ p) = (nativeQ p).comp (nativeCartan i p) := by
  ext x
  simp only [nativeCartan_eq_smul, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_smul]

/-- The original mode descends along the kernel and image of the original differential. -/
def nativeCohomologyCartan (i : Fin 2) (p : Charge hyperbolicPlane) :
    Module.End ℂ (NativeCohomology p) :=
  cohomologyMap (nativeQ p) (nativeQ p) (nativeQ_sq p) (nativeQ_sq p)
    (nativeCartan i p) (nativeCartan_chain i p)

set_option maxHeartbeats 800000 in
theorem nativeCohomologyCartan_eq_smul (i : Fin 2) (p : Charge hyperbolicPlane) :
    nativeCohomologyCartan i p = cartanEigenvalue i p • LinearMap.id := by
  let boundaries := D5.S3.HomologicalAlgebra.FinitePerturbation.Boundaries (nativeQ p) (nativeQ_sq p)
  apply LinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on boundaries z (fun x => ?_)
  have hx : cycleMap (nativeQ p) (nativeQ p) (nativeCartan i p) (nativeCartan_chain i p) x =
      cartanEigenvalue i p • x := by
    apply Subtype.ext
    change nativeCartan i p x.val = cartanEigenvalue i p • x.val
    rw [nativeCartan_eq_smul, LinearMap.smul_apply, LinearMap.id_apply]
  rw [nativeCohomologyCartan, cohomologyMap_mk, hx, LinearMap.smul_apply, LinearMap.id_apply]
  exact boundaries.mkQ.map_smul (cartanEigenvalue i p) x

/-- Restrict the actual zero mode to the reassociated relative shell. -/
def shellCartan (i : Fin 2) (p : Charge hyperbolicPlane) : Module.End ℂ (relativeShell p) :=
  ((assocY (reassoc (cartanCurrent i)))[[0]]).restrict (fun x hx => by
    rw [assoc_cartan_modes,
      assoc_zero_mode_of_momentum i p x ((mem_relativeShell_iff p x).mp hx).1]
    exact (relativeShell p).smul_mem _ hx)

theorem shellCartan_apply (i : Fin 2) (p : Charge hyperbolicPlane) (x : relativeShell p) :
    shellCartan i p x = cartanEigenvalue i p • x := by
  apply Subtype.ext
  change ((assocY (reassoc (cartanCurrent i)))[[0]]) x.val = cartanEigenvalue i p • x.val
  rw [assoc_cartan_modes]
  exact assoc_zero_mode_of_momentum i p x.val ((mem_relativeShell_iff p x.val).mp x.property).1

theorem shellCartan_reassoc (i : Fin 2) (p : Charge hyperbolicPlane) :
    (shellCartan i p).comp (nativeShellEquiv p).toLinearMap =
      (nativeShellEquiv p).toLinearMap.comp (nativeCartan i p) := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, shellCartan_apply, nativeCartan_eq_smul,
    LinearMap.smul_apply, LinearMap.id_apply, map_smul]

theorem shellCartan_commutes_Q (i : Fin 2) (p : Charge hyperbolicPlane) (x : relativeShell p) :
    shellCartan i p (relativeQ planeFrame planeBasis p x) =
      relativeQ planeFrame planeBasis p (shellCartan i p x) := by
  simp only [shellCartan_apply, map_smul]

variable (i : Fin 2) (p : Charge hyperbolicPlane) (g : ℤ)

/-- The original mode preserves cycles in every ghost degree. -/
def cyclesCartan : Module.End ℂ (GradedCycles planeFrame planeBasis p g) :=
  (shellCartan i p).restrict (fun x hx => by
    rw [shellCartan_apply]
    exact (GradedCycles planeFrame planeBasis p g).smul_mem _ hx)

theorem cyclesCartan_apply (x : GradedCycles planeFrame planeBasis p g) :
    cyclesCartan i p g x = cartanEigenvalue i p • x := by
  apply Subtype.ext
  exact shellCartan_apply i p x.val

theorem cyclesCartan_preserves_boundaries (x : GradedCycles planeFrame planeBasis p g)
    (hx : x ∈ GradedBoundaries planeFrame planeBasis p g) :
    cyclesCartan i p g x ∈ GradedBoundaries planeFrame planeBasis p g := by
  rw [cyclesCartan_apply]
  exact (GradedBoundaries planeFrame planeBasis p g).smul_mem _ hx

/-- Quotient the restricted original mode by the actual relative boundaries. -/
def cohomologyCartan : Module.End ℂ (GradedCohomology planeFrame planeBasis p g) :=
  (GradedBoundaries planeFrame planeBasis p g).mapQ (GradedBoundaries planeFrame planeBasis p g)
    (cyclesCartan i p g) (fun x hx => cyclesCartan_preserves_boundaries i p g x hx)

theorem cohomologyCartan_mk :
    (cohomologyCartan i p g).comp (GradedBoundaries planeFrame planeBasis p g).mkQ =
      (GradedBoundaries planeFrame planeBasis p g).mkQ.comp (cyclesCartan i p g) :=
  Submodule.mapQ_mkQ _ _ _

theorem cohomologyCartan_apply (z : GradedCohomology planeFrame planeBasis p g) :
    cohomologyCartan i p g z = cartanEigenvalue i p • z := by
  refine Submodule.Quotient.induction_on _ z (fun x => ?_)
  simpa only [cohomologyCartan, Submodule.mapQ_apply, cyclesCartan_apply, Submodule.mkQ_apply] using
    (GradedBoundaries planeFrame planeBasis p g).mkQ.map_smul (cartanEigenvalue i p) x

theorem cohomologyCartan_eq_smul :
    cohomologyCartan i p g = cartanEigenvalue i p • LinearMap.id := by
  apply LinearMap.ext
  exact cohomologyCartan_apply i p g

/-- In particular the zero-momentum action on physical H¹ is zero. -/
theorem cohomologyCartan_zero_momentum
    (z : GradedCohomology planeFrame planeBasis (0 : Charge hyperbolicPlane) 1) :
    cohomologyCartan i 0 1 z = 0 := by
  rw [cohomologyCartan_apply, cartanEigenvalue_zero, zero_smul]

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST
