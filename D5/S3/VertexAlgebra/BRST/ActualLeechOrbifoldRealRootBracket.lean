/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealRootBracket
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRealRootBracket
   mirror-E: none(waiver:algebraic-original-orbifold-tensor-field)
   anchors: []
   utility: none
   digest: The original BRST zero-mode product of the two literal norm-two roots. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldCartanAction
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldEvenCurrent
import D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector

/-!
The physical antighost removes the occupied c(1) site with coefficient one.
The orbifold and bc vacuum fields leave the original plane zero mode. Its
ordered cocycle is negative in both orders and the linear creation
coefficient distinguishes the two orders.

proof_shape: opposite_root_products, positive_root_product_class: content
admission_basis: escape-witness
escape_witness: The original convolution is reduced on the two literal tensors.
The coefficient at Laurent power minus one is evaluated in the native null
basis, and the relative degree bound and vacuum slices detect the classes.
The quotient bracket is then computed by comparing the actual cycles at
opposite momenta with the zero-momentum representatives.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RealRootBracket

open ActualLeechHyperbolic (leechData)
open ActualLeechOrbifoldMatter (leechUnit)
open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane matter)
open LatticeGeneratingFieldLocality (Carrier Charge Oscillator bilinear lowerCocycleExponent
  halfDiagonal epsilon paritySign creationCoeff)
open LatticeActualGeneratorLocality (actual_modes)
open LatticeActualOrderedProducts (raw_ground)
open LatticeSugawaraConformal (chargePolynomial)
open LatticePositiveEnergy (chargeEnergy)
open LatticeRelativeShellDegreeBounds (frameEnergy ghost_abs_charge_sub_one_le_count
  ghost_count_le_relativeEnergy)
open RelativeCohomology (OrbifoldWeight GhostSpace GradedCycles GradedBoundaries
  GradedCohomology groundBasis_eq relativeQ_degree NativeShell)
open TwistedGround.Orbifold
open D5.S3.Quantum.Fermionic
open CountableOccupationFock (ket vacuum)
open BcGhostQuartetCount (c1vac_eq)
open BcGhostRelativeEnergy (relativeEnergy)

open private creation_one charge_neg from
  D5.S3.VertexAlgebra.Lattice.NormFourVirasoroVector
open private ghost_B_neg_down vacCoeff vacCoeff_vac representative_one one_mem_degree from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum
open private assoc_vacuum_left from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldOriginalModes
open private rightLift_tmul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightCone
open private right_vacuum_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField
open private mode_vacuum from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLowWeights
open private eq_zero_of_all_rightSlices from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldLightConeDegreeBounds
open private groundIndex groundTensor groundTensor_mem_shell slice_groundTensor
  ghostSpace_iff_slices gradedBoundaryMap assocQ_reassoc from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology

local instance : AddCommGroup ComplexState := TensorProduct.addCommGroup

local instance (q : Charge hyperbolicPlane) : AddCommGroup (relativeShell q) :=
  Submodule.addCommGroup _

local instance (q : Charge hyperbolicPlane) :
    AddCommGroup (GradedCycles planeFrame planeBasis q 1) := Submodule.addCommGroup _

private abbrev orbVac := OriginalOrbifoldField.vacuumState leechData leechUnit
private abbrev planeGround (q : Charge hyperbolicPlane) : Carrier hyperbolicPlane :=
  Finsupp.single q (1 : Oscillator hyperbolicPlane)
private abbrev planeCurrent := LatticeZeroMomentumBRST.current hyperbolicPlane

/-- The norm-two integral vector with coordinates (1,1) in the ordered null basis. -/
def positiveRoot : Charge hyperbolicPlane := fun _ => 1

/-- The literal three-factor state, in the native association of the BRST complex. -/
def psi (q : Charge hyperbolicPlane) : ComplexState :=
  (orbVac ⊗ₜ[ℂ] planeGround q) ⊗ₜ[ℂ] ket {1}

private theorem root_norms :
    positiveRoot (0 : Fin 2) * positiveRoot (1 : Fin 2) = 1 ∧
      (-positiveRoot) (0 : Fin 2) * (-positiveRoot) (1 : Fin 2) = 1 := by
  norm_num [positiveRoot, Pi.neg_apply]

private theorem plane_pairing (a b : Charge hyperbolicPlane) :
    bilinear hyperbolicPlane a b =
      a (0 : Fin 2) * b (1 : Fin 2) + a (1 : Fin 2) * b (0 : Fin 2) := by
  change (∑ i : Fin 2, ∑ j : Fin 2, a i * OrderedHyperbolicExtension.U i j * b j) = _
  norm_num [Fin.sum_univ_two]

private theorem plane_cocycle_exponent (a b : Charge hyperbolicPlane) :
    lowerCocycleExponent hyperbolicPlane a b = a (1 : Fin 2) * b (0 : Fin 2) := by
  classical
  change (∑ i : Fin 2, ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => j < i),
    OrderedHyperbolicExtension.U i j * a i * b j) +
    (∑ i : Fin 2, (OrderedHyperbolicExtension.U i i / 2) * a i * b i) = _
  norm_num [Finset.sum_filter, Fin.sum_univ_two, show (0 : Fin 2) < 1 by decide,
    show ¬ (1 : Fin 2) < 0 by decide]

/-- The signs refer to the actual ordered lattice cocycle in each root order. -/
theorem opposite_root_pairings_and_signs :
    (bilinear hyperbolicPlane positiveRoot (-positiveRoot) = -2 ∧
      epsilon hyperbolicPlane positiveRoot (-positiveRoot) = -1) ∧
    (bilinear hyperbolicPlane (-positiveRoot) positiveRoot = -2 ∧
      epsilon hyperbolicPlane (-positiveRoot) positiveRoot = -1) := by
  have hodd : ¬ Even (-1 : ℤ) := by
    rintro ⟨k, hk⟩
    omega
  norm_num [plane_pairing, epsilon, plane_cocycle_exponent, paritySign, positiveRoot,
    Pi.neg_apply, hodd]

-- The existing exponential recurrence at t = 0 gives creation_one.
-- Its chargePolynomial is the sum of the two frequency-zero variables with charge coefficients.
private theorem root_creation_coefficients :
    creationCoeff hyperbolicPlane positiveRoot 1 =
      MvPolynomial.X ((0 : Fin 2), 0) + MvPolynomial.X ((1 : Fin 2), 0) ∧
    creationCoeff hyperbolicPlane (-positiveRoot) 1 =
      -(MvPolynomial.X ((0 : Fin 2), 0) + MvPolynomial.X ((1 : Fin 2), 0)) := by
  have h : chargePolynomial hyperbolicPlane positiveRoot =
      MvPolynomial.X ((0 : Fin 2), 0) + MvPolynomial.X ((1 : Fin 2), 0) := by
    change (∑ i : Fin 2, (positiveRoot i : ℂ) •
      (MvPolynomial.X (i, 0) : Oscillator hyperbolicPlane)) = _
    norm_num [positiveRoot, Fin.sum_univ_two]
  exact ⟨(creation_one hyperbolicPlane positiveRoot).trans h,
    by rw [creation_one, charge_neg, h]⟩

private theorem plane_ground_zero_mode (a b : Charge hyperbolicPlane) :
    ((LatticeAllStateField.Y hyperbolicPlane (planeGround a))[[0]]) (planeGround b) =
      epsilon hyperbolicPlane a b • Finsupp.single (a + b)
        (creationCoeff hyperbolicPlane a (-1 - bilinear hyperbolicPlane a b)) := by
  simp only [LatticeAllStateField.stateField_ground, actual_modes, raw_ground, neg_zero, zero_sub]

private theorem opposite_plane_zero_modes :
    ((LatticeAllStateField.Y hyperbolicPlane (planeGround positiveRoot))[[0]])
        (planeGround (-positiveRoot)) = -(planeCurrent (0 : Fin 2) + planeCurrent (1 : Fin 2)) ∧
    ((LatticeAllStateField.Y hyperbolicPlane (planeGround (-positiveRoot)))[[0]])
        (planeGround positiveRoot) = planeCurrent (0 : Fin 2) + planeCurrent (1 : Fin 2) := by
  obtain ⟨⟨hp, he⟩, ⟨hp', he'⟩⟩ := opposite_root_pairings_and_signs
  obtain ⟨hc, hc'⟩ := root_creation_coefficients
  constructor
  · rw [plane_ground_zero_mode, hp, he, add_neg_cancel, show (-1 : ℤ) - (-2) = 1 by decide, hc]
    simp only [neg_one_smul, Finsupp.single_add, LatticeActualConformalState.currentState]
  · rw [plane_ground_zero_mode, hp', he', neg_add_cancel, show (-1 : ℤ) - (-2) = 1 by decide, hc']
    simp only [neg_one_smul, Finsupp.single_neg, neg_neg, Finsupp.single_add,
      LatticeActualConformalState.currentState]

-- In the b(-1) image both the orbifold and ghost fields are vacuum fields.
private theorem original_ground_zero_mode (a b : Charge hyperbolicPlane) :
    originalMode 0 (VirasoroBRST.ghostB matter (-1) (psi a)) (psi b) =
      (orbVac ⊗ₜ[ℂ] (((LatticeAllStateField.Y hyperbolicPlane (planeGround a))[[0]])
        (planeGround b))) ⊗ₜ[ℂ] ket {1} := by
  have hb : VirasoroBRST.ghostB matter (-1) (psi a) =
      (orbVac ⊗ₜ[ℂ] planeGround a) ⊗ₜ[ℂ] vacuum := by
    change (orbVac ⊗ₜ[ℂ] planeGround a) ⊗ₜ[ℂ] BcGhostFock.b (-1) (ket {1}) = _
    rw [ghost_B_neg_down]
  apply reassoc.injective
  rw [hb, reassoc_originalMode]
  simp only [psi, reassoc, TensorProduct.assoc_tmul, assoc_vacuum_left, right_vacuum_modes,
    rightLift_tmul, TensorProduct.map_tmul, LinearMap.id_apply]

/-- The two raw original products, in the existing degree-one null-basis states. -/
theorem opposite_root_products :
    (originalMode 0 (VirasoroBRST.ghostB matter (-1) (psi positiveRoot))
      (psi (-positiveRoot)) = -(RelativeZeroMomentum.u 0 + RelativeZeroMomentum.u 1)) ∧
    (originalMode 0 (VirasoroBRST.ghostB matter (-1) (psi (-positiveRoot)))
      (psi positiveRoot) = RelativeZeroMomentum.u 0 + RelativeZeroMomentum.u 1) := by
  constructor
  · rw [original_ground_zero_mode, opposite_plane_zero_modes.1]
    simp only [RelativeZeroMomentum.u, TensorProduct.tmul_neg, TensorProduct.neg_tmul,
      TensorProduct.tmul_add, TensorProduct.add_tmul]
  · rw [original_ground_zero_mode, opposite_plane_zero_modes.2]
    simp only [RelativeZeroMomentum.u, TensorProduct.tmul_add, TensorProduct.add_tmul]

private theorem reassoc_psi (q : Charge hyperbolicPlane) :
    reassoc (psi q) = groundTensor planeFrame planeBasis q orbVac := by
  change orbVac ⊗ₜ[ℂ] (planeGround q ⊗ₜ[ℂ] ket {1}) =
    orbVac ⊗ₜ[ℂ] LatticeQuartetContraction.actualBasis planeFrame planeBasis (groundIndex q)
  rw [groundBasis_eq, c1vac_eq]

private def rootCochain (q : Charge hyperbolicPlane)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) : relativeShell q :=
  ⟨reassoc (psi q), by
    let v : OrbifoldWeight q := ⟨orbVac, by
      apply Module.End.mem_eigenspace_iff.mpr
      simpa only [hq, sub_self, Int.cast_zero, zero_smul] using (mode_vacuum 0 (by decide))⟩
    rw [reassoc_psi]
    exact groundTensor_mem_shell planeFrame planeBasis q v⟩

-- At plane ground energy one the relative slice bound leaves zero excitation energy.
-- In particular every occupied right slice has ghost number one.
private theorem normTwo_shell_degree_one (q : Charge hyperbolicPlane)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) (x : relativeShell q) :
    x ∈ GhostSpace q 1 := by
  apply (ghostSpace_iff_slices planeFrame planeBasis q 1 x).mpr
  intro i hi
  obtain ⟨_, hb, _, hlevel⟩ := relativeShell_rightSlice_bounds planeFrame planeBasis q
    x.val x.property i hi
  have hf : 0 ≤ (frameEnergy i.1.2 : ℤ) := Int.natCast_nonneg _
  rw [plane_chargeEnergy, hq] at hlevel
  have hghost : relativeEnergy i.2 ≤ 0 := by omega
  have habs : |BcGhostCharge.charge i.2 - 1| ≤ 0 :=
    (ghost_abs_charge_sub_one_le_count i.2 hb).trans
      ((ghost_count_le_relativeEnergy i.2 hb).trans hghost)
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  change BcGhostCharge.charge i.2 = 1
  omega

private theorem normTwo_relativeQ (q : Charge hyperbolicPlane)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) :
    relativeQ planeFrame planeBasis q = 0 := by
  apply LinearMap.ext
  intro x
  have h2 := relativeQ_degree planeFrame planeBasis q 1 x (normTwo_shell_degree_one q hq x)
  change relativeQ planeFrame planeBasis q x ∈ GhostSpace q 2 at h2
  rw [LinearMap.zero_apply]
  apply Subtype.ext
  apply eq_zero_of_all_rightSlices planeFrame planeBasis
  intro i
  by_contra hi
  let y := relativeQ planeFrame planeBasis q x
  have h1' := (ghostSpace_iff_slices planeFrame planeBasis q 1 y).mp
    (normTwo_shell_degree_one q hq y) i hi
  have h2' := (ghostSpace_iff_slices planeFrame planeBasis q 2 y).mp h2 i hi
  exact (by decide : (2 : ℤ) ≠ 1) (h2'.symm.trans h1')

private def rootCycle (q : Charge hyperbolicPlane)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) : GradedCycles planeFrame planeBasis q 1 :=
  ⟨rootCochain q hq, normTwo_shell_degree_one q hq _, by
    change relativeQ planeFrame planeBasis q (rootCochain q hq) = 0
    rw [normTwo_relativeQ q hq, LinearMap.zero_apply]⟩

private theorem psi_ne_zero (q : Charge hyperbolicPlane) : psi q ≠ 0 := by
  have hv : orbVac ≠ 0 := by
    intro h
    have h0 : vacCoeff orbVac = 1 := vacCoeff_vac
    rw [h, vacCoeff.map_zero] at h0
    exact zero_ne_one h0
  have hs : rightSlice planeFrame planeBasis (groundIndex q) (reassoc (psi q)) = orbVac := by
    rw [reassoc_psi, slice_groundTensor, ite_eq_left rfl]
  intro h
  rw [h, reassoc.map_zero, (rightSlice planeFrame planeBasis (groundIndex q)).map_zero] at hs
  exact hv hs.symm

private theorem root_class_ne_zero (q : Charge hyperbolicPlane)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) :
    (Submodule.Quotient.mk (rootCycle q hq) : GradedCohomology planeFrame planeBasis q 1) ≠ 0 := by
  intro h
  have hm := (Submodule.Quotient.mk_eq_zero (GradedBoundaries planeFrame planeBasis q 1)).mp h
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hm
  change gradedBoundaryMap planeFrame planeBasis q 1 y = rootCycle q hq at hy
  have hz : relativeQ planeFrame planeBasis q y.val = rootCochain q hq :=
    congrArg Subtype.val hy
  rw [normTwo_relativeQ q hq, LinearMap.zero_apply] at hz
  apply psi_ne_zero q
  apply reassoc.injective
  rw [reassoc.map_zero]
  exact congrArg Subtype.val hz.symm

private theorem genuine_representative (q : Charge hyperbolicPlane)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) :
    psi q ∈ NativeShell q ∧ Q (psi q) = 0 ∧
      ∃ x : GradedCycles planeFrame planeBasis q 1,
        x.val.val = reassoc (psi q) ∧
          (Submodule.Quotient.mk x : GradedCohomology planeFrame planeBasis q 1) ≠ 0 := by
  refine ⟨(rootCochain q hq).property, ?_, rootCycle q hq, rfl, root_class_ne_zero q hq⟩
  apply reassoc.injective
  rw [reassoc.map_zero, ← assocQ_reassoc]
  change (relativeQ planeFrame planeBasis q (rootCochain q hq)).val = 0
  rw [normTwo_relativeQ q hq, LinearMap.zero_apply]
  rfl

/-- Both literal root states are degree-one relative BRST cycles with nonzero classes. -/
theorem real_root_representatives :
    ∀ q : Charge hyperbolicPlane, q = positiveRoot ∨ q = -positiveRoot →
      psi q ∈ NativeShell q ∧ Q (psi q) = 0 ∧
        ∃ x : GradedCycles planeFrame planeBasis q 1,
          x.val.val = reassoc (psi q) ∧
            (Submodule.Quotient.mk x : GradedCohomology planeFrame planeBasis q 1) ≠ 0 := by
  intro q h
  rcases h with rfl | rfl
  · exact genuine_representative positiveRoot root_norms.1
  · exact genuine_representative (-positiveRoot) root_norms.2

/-- Each of the two native null-basis Cartan zero modes has eigenvalues +1 and -1. -/
theorem cartan_on_real_roots (i : Fin 2) :
    (originalMode 0 (VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i))
      (psi positiveRoot) = psi positiveRoot) ∧
    (originalMode 0 (VirasoroBRST.ghostB matter (-1) (RelativeZeroMomentum.u i))
      (psi (-positiveRoot)) = -psi (-positiveRoot)) := by
  have hp : cartanEigenvalue i positiveRoot = 1 := by
    have h := cartanEigenvalue_coordinates positiveRoot
    fin_cases i
    · simpa [positiveRoot] using h.1
    · simpa [positiveRoot] using h.2
  have hn : cartanEigenvalue i (-positiveRoot) = -1 := by
    have h := cartanEigenvalue_coordinates (-positiveRoot)
    fin_cases i
    · simpa [positiveRoot, Pi.neg_apply] using h.1
    · simpa [positiveRoot, Pi.neg_apply] using h.2
  constructor
  · rw [cartan_zero_mode_on_native_shell i positiveRoot
      ⟨psi positiveRoot, (rootCochain positiveRoot root_norms.1).property⟩, hp, one_smul]
  · rw [cartan_zero_mode_on_native_shell i (-positiveRoot)
      ⟨psi (-positiveRoot), (rootCochain (-positiveRoot) root_norms.2).property⟩, hn, neg_one_smul]

/-- The forward product is a nonzero state and represents Cartan coordinates (-1,-1)
in the actual zero-momentum ghost-one quotient. -/
theorem positive_root_product_class :
    let z := originalMode 0 (VirasoroBRST.ghostB matter (-1) (psi positiveRoot))
      (psi (-positiveRoot))
    z ≠ 0 ∧ ∃ x : GhostSpace 0 1, reassoc.symm x.val.val = z ∧
      RelativeZeroMomentum.classOf 1 x =
        RelativeZeroMomentum.ghostOneCohomologyEquiv.symm (fun _ => -1) ∧
      RelativeZeroMomentum.classOf 1 x ≠ 0 := by
  dsimp only
  let f : Fin 2 → ℂ := fun _ => -1
  let x : GhostSpace 0 1 :=
    ⟨RelativeZeroMomentum.shellEquiv.symm (0, (f, 0)), one_mem_degree f⟩
  have hx : reassoc.symm x.val.val = -(RelativeZeroMomentum.u 0 + RelativeZeroMomentum.u 1) := by
    change RelativeZeroMomentum.representative (0, (f, 0)) = _
    rw [representative_one]
    simp only [f, Fin.sum_univ_two, neg_one_smul, RelativeZeroMomentum.u,
      TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.tmul_neg,
      TensorProduct.neg_tmul, neg_add]
  have hc : RelativeZeroMomentum.classOf 1 x =
      RelativeZeroMomentum.ghostOneCohomologyEquiv.symm f :=
    (RelativeZeroMomentum.ghostOneCohomologyEquiv_symm f).symm
  have hf : f ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num [f] at h0
  rw [opposite_root_products.1]
  refine ⟨?_, x, hx, hc, ?_⟩
  · intro h
    have hx0 := reassoc.symm.map_eq_zero_iff.mp (hx.trans h)
    have hz : RelativeZeroMomentum.shellEquiv.symm (0, (f, 0)) = 0 := Subtype.ext hx0
    have hc0 := RelativeZeroMomentum.shellEquiv.symm.map_eq_zero_iff.mp hz
    exact hf (congrArg (fun t : RelativeZeroMomentum.Coordinates => t.2.1) hc0)
  · rw [hc]
    exact fun h => hf (RelativeZeroMomentum.ghostOneCohomologyEquiv.symm.map_eq_zero_iff.mp h)

section MomentumSum

open RelativeBracket (MomentumH1 current nativeValue cycleCurrent momentumBracket
  momentumBracket_incl bracket_mk)
open private inclCycle inclCycle_congr from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldEvenCurrent
open private native_cycleCurrent native_smul from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeBracket
open private cyclesEquiv from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum

local notation "Momentum" => Charge hyperbolicPlane
local notation "H" => fun p : Momentum => GradedCohomology planeFrame planeBasis p 1
local notation "Cycles" => fun p : Momentum => GradedCycles planeFrame planeBasis p 1
local notation "incl" => DirectSum.lof ℂ Momentum H

/-- The class of the literal positive root representative in the momentum sum. -/
def positiveRootClass : MomentumH1 := inclCycle positiveRoot (rootCycle positiveRoot root_norms.1)

/-- The class of the literal negative root representative in the momentum sum. -/
def negativeRootClass : MomentumH1 :=
  inclCycle (-positiveRoot) (rootCycle (-positiveRoot) root_norms.2)

/-- Cartan coordinates in the actual zero-momentum summand of relative cohomology. -/
def cartanClass : (Fin 2 → ℂ) →ₗ[ℂ] MomentumH1 :=
  (incl 0).comp RelativeZeroMomentum.ghostOneCohomologyEquiv.symm.toLinearMap

private def cartanCycle (f : Fin 2 → ℂ) : Cycles 0 :=
  cyclesEquiv 1 ⟨RelativeZeroMomentum.shellEquiv.symm (0, (f, 0)), one_mem_degree f⟩

private theorem cartanClass_eq (f : Fin 2 → ℂ) :
    cartanClass f = inclCycle 0 (cartanCycle f) := by
  exact congrArg (incl 0) (RelativeZeroMomentum.ghostOneCohomologyEquiv_symm f)

private theorem cartanCycle_native (f : Fin 2 → ℂ) :
    nativeValue (cartanCycle f) =
      f 0 • RelativeZeroMomentum.u 0 + f 1 • RelativeZeroMomentum.u 1 := by
  change RelativeZeroMomentum.representative (0, (f, 0)) = _
  rw [representative_one]
  simp only [Fin.sum_univ_two, RelativeZeroMomentum.u, TensorProduct.tmul_add,
    TensorProduct.add_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

private theorem rootCycle_native (q : Momentum) (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) :
    nativeValue (rootCycle q hq) = psi q := reassoc.symm_apply_apply _

private theorem lie_cycles {p q : Momentum} (x : Cycles p) (y : Cycles q) :
    ⁅inclCycle p x, inclCycle q y⁆ = inclCycle (p + q) (cycleCurrent x y) := by
  change momentumBracket (incl p (Submodule.Quotient.mk x)) (incl q (Submodule.Quotient.mk y)) =
    incl (p + q) (Submodule.Quotient.mk (cycleCurrent x y))
  rw [momentumBracket_incl, bracket_mk]

private theorem incl_injective (q : Momentum) : Function.Injective (incl q) := by
  classical
  intro x y h
  simpa only [DirectSum.component.lof_self] using
    congrArg (fun z : MomentumH1 => DirectSum.component ℂ Momentum H q z) h

private theorem inclCycle_root_ne_zero (q : Momentum) (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1) :
    inclCycle q (rootCycle q hq) ≠ 0 := by
  intro h
  apply root_class_ne_zero q hq
  exact incl_injective q (h.trans ((incl q).map_zero).symm)

/-- Both lifted roots and their forward bracket are nonzero. The two orders give
the Cartan coordinates `(-1,-1)` and `(1,1)` in the original BRST Lie algebra. -/
theorem opposite_root_lie_brackets :
    positiveRootClass ≠ 0 ∧ negativeRootClass ≠ 0 ∧
    ⁅positiveRootClass, negativeRootClass⁆ = cartanClass (fun _ => -1) ∧
    ⁅negativeRootClass, positiveRootClass⁆ = cartanClass (fun _ => 1) ∧
    ⁅positiveRootClass, negativeRootClass⁆ ≠ 0 := by
  have hp : ⁅positiveRootClass, negativeRootClass⁆ = cartanClass (fun _ => -1) := by
    rw [positiveRootClass, negativeRootClass, lie_cycles, cartanClass_eq]
    apply inclCycle_congr (add_neg_cancel positiveRoot)
    rw [native_cycleCurrent, rootCycle_native, rootCycle_native, cartanCycle_native]
    change originalMode 0 (VirasoroBRST.ghostB matter (-1) (psi positiveRoot))
      (psi (-positiveRoot)) = (-1 : ℂ) • RelativeZeroMomentum.u 0 +
        (-1 : ℂ) • RelativeZeroMomentum.u 1
    simpa only [neg_one_smul, neg_add] using opposite_root_products.1
  have hn : ⁅negativeRootClass, positiveRootClass⁆ = cartanClass (fun _ => 1) := by
    rw [positiveRootClass, negativeRootClass, lie_cycles, cartanClass_eq]
    apply inclCycle_congr (neg_add_cancel positiveRoot)
    rw [native_cycleCurrent, rootCycle_native, rootCycle_native, cartanCycle_native,
      one_smul, one_smul]
    exact opposite_root_products.2
  refine ⟨inclCycle_root_ne_zero _ _, inclCycle_root_ne_zero _ _, hp, hn, ?_⟩
  rw [hp]
  intro hz
  let c := RelativeZeroMomentum.ghostOneCohomologyEquiv.symm
  change incl 0 (c (fun _ => -1)) = 0 at hz
  have h := c.map_eq_zero_iff.mp (incl_injective 0 (hz.trans ((incl 0).map_zero).symm))
  have h₀ := congrFun h (0 : Fin 2)
  norm_num at h₀

private theorem cartan_lie_root (f : Fin 2 → ℂ) (q : Momentum)
    (hq : q (0 : Fin 2) * q (1 : Fin 2) = 1)
    (c : ℂ) (hc : ∀ i : Fin 2, current (RelativeZeroMomentum.u i) (psi q) = c • psi q) :
    ⁅cartanClass f, inclCycle q (rootCycle q hq)⁆ =
      ((f 0 + f 1) * c) • inclCycle q (rootCycle q hq) := by
  rw [cartanClass_eq, lie_cycles, ← (inclCycle q).map_smul]
  apply inclCycle_congr (zero_add q)
  rw [native_cycleCurrent, cartanCycle_native, rootCycle_native, native_smul, rootCycle_native]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hc,
    add_smul, mul_smul]

/-- In the actual BRST Lie algebra, the positive root class, the negative of the
opposite root class, and the Cartan class of `(1,1)` obey the normalized relations. -/
theorem normalized_real_root_triple :
    let e := positiveRootClass
    let f := -negativeRootClass
    let h := cartanClass (fun _ => 1)
    ⁅e, f⁆ = h ∧ ⁅h, e⁆ = (2 : ℂ) • e ∧ ⁅h, f⁆ = (-2 : ℂ) • f := by
  dsimp only
  have hp : ⁅cartanClass (fun _ => 1), positiveRootClass⁆ = (2 : ℂ) • positiveRootClass := by
    have h := cartan_lie_root (fun _ => 1) positiveRoot root_norms.1 1
      (fun i => by
        simpa only [current, LinearMap.comp_apply, one_smul] using (cartan_on_real_roots i).1)
    norm_num at h
    exact h
  have hn : ⁅cartanClass (fun _ => 1), negativeRootClass⁆ = (-2 : ℂ) • negativeRootClass := by
    unfold negativeRootClass
    have h := cartan_lie_root (fun _ => 1) (-positiveRoot) root_norms.2 (-1)
      (fun i => by
        simpa only [current, LinearMap.comp_apply, neg_one_smul] using (cartan_on_real_roots i).2)
    change _ = ((1 + 1) * (-1) : ℂ) • _ at h
    rw [show ((1 + 1) * (-1) : ℂ) = -2 by norm_num] at h
    exact h
  refine ⟨?_, hp, ?_⟩
  · rw [lie_neg, opposite_root_lie_brackets.2.2.1, ← map_neg]
    apply congrArg cartanClass
    funext i
    simp
  · rw [lie_neg, hn, smul_neg]

end MomentumSum

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.RealRootBracket
