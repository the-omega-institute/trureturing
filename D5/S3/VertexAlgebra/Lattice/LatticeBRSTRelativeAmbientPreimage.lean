/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTRelativeAmbientPreimage
   generality: I
   mirror-B: none
   mirror-E: none(waiver:source-only-flight)
   anchors: []
   utility: none
   digest: Relative primitives for unrestricted ambient boundaries of the current original Q. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullGhostNumberCohomology

/-!
Faithful current-coordinate port of the supplied historical
`OriginalQQuartetSource.relative_ambient_boundary_homotopy_preimage` and
`OriginalQQuartetSource.literal_physical_equality_iff_relative_preimage` in
`OriginalQRelativeAmbientPreimage.lean`, with the antighost mechanism of
`OriginalQRelativeFiniteHpl.lean` and the incoming projection mechanism of
`OriginalQAmbientEnergyProjectionTransient.lean`.

The input is the actual `fixedSector`, the charge is the original
`LatticeBRST.totalCharge`, the antighost is the actual `ghostB0`, and the
integer grading is the native `Number.N`. The primitive is the existing
`FinitePerturbation.Input.H` instantiated by the accepted27 `finiteInput`.
Its cutoff is derived by the supplier's signed-filtration theorem. In
particular there is no truncation of the incoming original `State D`.

The two compatibility steps are proved here. First, the actual basis defines
a charge/energy projector on all states; original Q commutes with it because
Q preserves every actual basis vector's charge and energy sector. Second,
the original Ward identity, the existing quartet anticommutators and the
finite inverse polynomial imply B0 anticommutation with the corrected H.
The vanishing of the transferred differential is derived only ON SHELL,
from the actual full-Q tail and zero-count compression suppliers. It is
not asserted on the unrestricted absolute ground space.

Attribution: original BRST (Becchi--Rouet--Stora--Tyutin), Kato--Ogawa and
Lian--Zuckerman; algebraic HPL of Gugenheim--Lambe--Stasheff. This port adapts
the saved proofs named above; it asserts no new attribution or acceptance
for those historical modules. The native suppliers retain the Bakalov--Kac,
Scott Carnahan, Kalle Kytölä, Mathlib and Batteries attribution and Apache
2.0 notices. No supplier is copied into or modified by this file.

The endpoint uses the existing global `LatticeBRSTCohomologyField` quotient,
whose boundaries are the range of Q on ALL original states. It does not
define a new quotient or assume a relative primitive, an SDR, compatibility,
positivity, old/new-Q equality, or an all-charge/no-ghost conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private N_actual_coefficient N_totalCharge N_d0 N_h
  comm_sub comm_mul commutes_inversePolynomial
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
open private fixedMomentum_iff_project
  from D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullNonzeroAbsoluteCohomology

namespace D5.S3.VertexAlgebra.LatticeBRSTRelativeAmbientPreimage

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction LatticeBRSTPerturbationFiltration
open LatticeBRSTFiniteTransfer
open LatticeRelativeBRSTCohomology.Number (N)
open D5.S3.HomologicalAlgebra
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ)

local notation "E" => fixedSector H beta level
local notation "qE" => sectorQ F B H hHG hGH beta level
local notation "dE" => sectorD0 F B H hHG hGH beta level
local notation "hE" => sectorH F B H hHG hGH beta level
local notation "pE" => sectorP0 F B H hHG hGH beta level

/-- The actual fixed sector has the literal current fixedMomentum condition. -/
theorem fixedSector_mem_fixedMomentum (v : E) :
    v.val ∈ LatticeRelativeMassShell.fixedMomentum D beta :=
  (fixedMomentum_iff_project beta v.val).mpr v.property.1

/-- Selection on the finite support of the actual original-state basis.
No energy or ghost condition is imposed on the argument of this map. -/
def ambientSectorProjection : Module.End ℂ (State D) := by
  classical
  exact diagonal (actualBasis F B)
    (fun i => if i.1.1 = beta ∧ indexLevel i = level then 1 else 0)

private theorem ambientSectorProjection_coefficient (v : State D) (i : StateIndex D t) :
    (actualBasis F B).repr (ambientSectorProjection F B beta level v) i =
      (if i.1.1 = beta ∧ indexLevel i = level then (1 : ℂ) else 0) *
        (actualBasis F B).repr v i := by
  classical
  exact diagonal_coefficient (actualBasis F B) _ v i

include hHG hGH in
private theorem ambientSectorProjection_mem (v : State D) :
    ambientSectorProjection F B beta level v ∈ E := by
  classical
  apply (mem_fixedSector_iff F B H hHG hGH beta level _).mpr
  intro i hi
  by_contra hn
  exact hi (by rw [ambientSectorProjection_coefficient, if_neg hn, zero_mul])

include hHG hGH in
private theorem ambientSectorProjection_fixed (v : State D) (hv : v ∈ E) :
    ambientSectorProjection F B beta level v = v := by
  classical
  apply (actualBasis F B).repr.injective
  ext i
  rw [ambientSectorProjection_coefficient]
  by_cases hz : (actualBasis F B).repr v i = 0
  · simp only [hz, mul_zero]
  · have hi := (mem_fixedSector_iff F B H hHG hGH beta level v).mp hv i hz
    rw [if_pos hi, one_mul]

include hHG hGH in
/-- Incoming ambient projection is a chain map for the original Q.
This is proved on every actual basis vector, including all other charges,
all energies and both zero-mode occupations. -/
theorem ambientSectorProjection_Q :
    ambientSectorProjection F B beta level * LatticeBRST.totalCharge D H =
      LatticeBRST.totalCharge D H * ambientSectorProjection F B beta level := by
  classical
  apply (actualBasis F B).ext
  intro i
  have hQi : LatticeBRST.totalCharge D H (actualBasis F B i) ∈
      fixedSector H i.1.1 (indexLevel i) :=
    Q_preserves F B H hHG hGH i.1.1 (indexLevel i) (actualBasis F B i)
      (basis_mem_fixedSector F B H hHG hGH i)
  have hPi : ambientSectorProjection F B beta level (actualBasis F B i) =
      (if i.1.1 = beta ∧ indexLevel i = level then (1 : ℂ) else 0) •
        actualBasis F B i := by
    exact diagonal_basis (actualBasis F B) _ i
  apply (actualBasis F B).repr.injective
  ext j
  change (actualBasis F B).repr
      (ambientSectorProjection F B beta level
        (LatticeBRST.totalCharge D H (actualBasis F B i))) j =
    (actualBasis F B).repr
      (LatticeBRST.totalCharge D H
        (ambientSectorProjection F B beta level (actualBasis F B i))) j
  rw [ambientSectorProjection_coefficient, hPi, map_smul]
  simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hz : (actualBasis F B).repr
      (LatticeBRST.totalCharge D H (actualBasis F B i)) j = 0
  · simp only [hz, mul_zero]
  · have hji := (mem_fixedSector_iff F B H hHG hGH
      i.1.1 (indexLevel i) _).mp hQi j hz
    rw [hji.1, hji.2]

def ambientToSector : State D →ₗ[ℂ] E :=
  (ambientSectorProjection F B beta level).codRestrict E
    (ambientSectorProjection_mem F B H hHG hGH beta level)

@[simp] theorem ambientToSector_coe (v : State D) :
    (ambientToSector F B H hHG hGH beta level v : State D) =
      ambientSectorProjection F B beta level v := rfl

/-- An unrestricted original-Q primitive can be projected to the same actual
charge/energy sector. No relative or homogeneous property of that primitive
is assumed or needed. -/
theorem ambient_boundary_sector_preimage (state : E) :
    (∃ preimage : State D, LatticeBRST.totalCharge D H preimage = state.val) ↔
      ∃ preimage : E, qE preimage = state := by
  constructor
  · rintro ⟨preimage, equation⟩
    refine ⟨ambientToSector F B H hHG hGH beta level preimage, ?_⟩
    apply Subtype.ext
    have commute := LinearMap.congr_fun
      (ambientSectorProjection_Q F B H hHG hGH beta level) preimage
    change ambientSectorProjection F B beta level
        (LatticeBRST.totalCharge D H preimage) =
      LatticeBRST.totalCharge D H
        (ambientSectorProjection F B beta level preimage) at commute
    change LatticeBRST.totalCharge D H
      (ambientSectorProjection F B beta level preimage) = state.val
    rw [← commute, equation,
      ambientSectorProjection_fixed F B H hHG hGH beta level state.val state.property]
  · rintro ⟨preimage, equation⟩
    exact ⟨preimage.val, congrArg Subtype.val equation⟩

private theorem B0_preserves_fixedSector (v : State D) (hv : v ∈ E) :
    ghostB0 v ∈ E := by
  have chargeCommute : chargeProject beta * ghostB0 = ghostB0 * chargeProject beta := by
    apply TensorProduct.ext'
    intro x w
    simp only [chargeProject, ghostB0, tp, Module.End.mul_apply,
      TensorProduct.map_tmul, Module.End.one_apply, LinearMap.id_apply]
  constructor
  · have eq := LinearMap.congr_fun chargeCommute v
    simpa only [Module.End.mul_apply, hv.1] using eq
  · have eq := LinearMap.congr_fun
      (sub_eq_zero.mp (LatticeBRSTRelativeZeroMode.totalL0_b_zero D H)) v
    change totalL0 H (ghostB0 v) = ghostB0 (totalL0 H v) at eq
    rw [eq, hv.2, map_smul]

def sectorB0 : Module.End ℂ E :=
  ghostB0.restrict (B0_preserves_fixedSector H beta level)

@[simp] theorem sectorB0_coe (v : E) :
    (sectorB0 H beta level v : State D) = ghostB0 v.val := rfl

local notation "bE" => sectorB0 H beta level

theorem sector_B0_original_ward :
    qE * bE + bE * qE = (groundEnergy beta + (level : ℂ) - 1) • 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have eq := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) v.val
  change LatticeBRST.totalCharge D H (ghostB0 v.val) +
    ghostB0 (LatticeBRST.totalCharge D H v.val) = totalL0 H v.val at eq
  change LatticeBRST.totalCharge D H (ghostB0 v.val) +
    ghostB0 (LatticeBRST.totalCharge D H v.val) =
      (groundEnergy beta + (level : ℂ) - 1) • v.val
  exact eq.trans v.property.2

private theorem sector_B0_d0 : bE * dE + dE * bE = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (b0_d0 F beta) v.val

private theorem sector_B0_h : bE * hE + hE * bE = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (b0_h F B beta) v.val

include F B hHG hGH in
private theorem N_preserves_fixedSector (v : State D) (hv : v ∈ E) :
    N D v ∈ E := by
  apply (mem_fixedSector_iff F B H hHG hGH beta level _).mpr
  intro i hi
  apply (mem_fixedSector_iff F B H hHG hGH beta level v).mp hv i
  intro hz
  exact hi (by rw [N_actual_coefficient F B, hz, mul_zero])

def sectorN : Module.End ℂ E :=
  (N D).restrict (N_preserves_fixedSector F B H hHG hGH beta level)

@[simp] theorem sectorN_coe (v : E) :
    (sectorN F B H hHG hGH beta level v : State D) = N D v.val := rfl

local notation "nE" => sectorN F B H hHG hGH beta level

private theorem sector_N_Q : nE * qE - qE * nE = qE := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (N_totalCharge H) v.val

private theorem sector_N_d0 : nE * dE - dE * nE = dE := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (N_d0 F beta) v.val

private theorem sector_N_h : nE * hE - hE * nE = -hE := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact LinearMap.congr_fun (N_h F B beta) v.val

private theorem sector_N_delta :
    nE * (qE - dE) - (qE - dE) * nE = qE - dE := by
  rw [comm_sub, sector_N_Q, sector_N_d0]

private theorem sector_N_hdelta :
    nE * (hE * (qE - dE)) = (hE * (qE - dE)) * nE := by
  apply sub_eq_zero.mp
  rw [comm_mul, sector_N_h, sector_N_delta, neg_mul, neg_add_cancel]

variable (hp : F.pPlus beta ≠ 0) (critical : D.rank = 26)

local notation "c" => finiteInput F B H hHG hGH beta level hp critical
local notation "cutoff" => (2 * level.toNat + 2)
local notation "homotopy" => FinitePerturbation.Input.H c cutoff
local notation "projection" => FinitePerturbation.Input.P c cutoff
local notation "inclusion" => FinitePerturbation.Input.I c cutoff
local notation "transferred" => FinitePerturbation.Input.transferred c cutoff
local notation "U" => LatticeBRSTFiniteTransfer.quartetGround F B H hHG hGH beta level

private theorem input_D : FinitePerturbation.Input.D c = qE := by
  change dE + (qE - dE) = qE
  abel

/-- Actual finite-inverse antighost compatibility, derived from the original
Ward identity on the actual shell. Neither commutation nor an SDR is input. -/
theorem B0_corrected_homotopy_compatibility
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    bE * homotopy + homotopy * bE = 0 := by
  have hBQ : bE * qE + qE * bE = 0 := by
    rw [add_comm, sector_B0_original_ward, shell, zero_smul]
  have hBh : bE * hE + hE * bE = 0 :=
    sector_B0_h F B H hHG hGH beta level
  have hBdelta : bE * (qE - dE) + (qE - dE) * bE = 0 := by
    calc
      _ = (bE * qE + qE * bE) - (bE * dE + dE * bE) := by
        rw [mul_sub, sub_mul]
        abel
      _ = 0 := by rw [hBQ, sector_B0_d0, sub_self]
  have swapH : bE * hE = -(hE * bE) := eq_neg_iff_add_eq_zero.mpr hBh
  have swapDelta : bE * (qE - dE) = -((qE - dE) * bE) :=
    eq_neg_iff_add_eq_zero.mpr hBdelta
  have factorCommute : bE * (hE * (qE - dE)) = (hE * (qE - dE)) * bE := by
    calc
      _ = (bE * hE) * (qE - dE) := (mul_assoc _ _ _).symm
      _ = -(hE * bE) * (qE - dE) := by rw [swapH]
      _ = -hE * (bE * (qE - dE)) := by rw [neg_mul, mul_assoc, neg_mul]
      _ = _ := by rw [swapDelta, neg_mul, mul_neg, neg_neg, mul_assoc]
  have inverseCommute : bE * FinitePerturbation.Input.K c cutoff = FinitePerturbation.Input.K c cutoff * bE :=
    commutes_inversePolynomial bE (hE * (qE - dE)) factorCommute cutoff
  change bE * (FinitePerturbation.Input.K c cutoff * hE) + (FinitePerturbation.Input.K c cutoff * hE) * bE = 0
  calc
    _ = FinitePerturbation.Input.K c cutoff * (bE * hE + hE * bE) := by
      rw [← mul_assoc, inverseCommute]
      simp only [mul_assoc, mul_add]
    _ = 0 := by rw [hBh, mul_zero]

private theorem corrected_homotopy_N :
    nE * homotopy - homotopy * nE = -homotopy := by
  have inverseCommute : nE * FinitePerturbation.Input.K c cutoff = FinitePerturbation.Input.K c cutoff * nE :=
    commutes_inversePolynomial nE (hE * (qE - dE))
      (sector_N_hdelta F B H hHG hGH beta level) cutoff
  change nE * (FinitePerturbation.Input.K c cutoff * hE) - (FinitePerturbation.Input.K c cutoff * hE) * nE = -(FinitePerturbation.Input.K c cutoff * hE)
  rw [comm_mul, sub_eq_zero.mpr inverseCommute, sector_N_h, zero_mul, zero_add, mul_neg]

/-- Every integral ghost degree is retained; corrected H lowers the native
number eigenvalue by one. This uses the existing number laws for h and Q. -/
theorem corrected_homotopy_ghost_degree (degree : ℤ) (state : E)
    (homogeneous : N D state.val = (degree : ℂ) • state.val) :
    N D (homotopy state).val = ((degree - 1 : ℤ) : ℂ) • (homotopy state).val := by
  have number : nE state = (degree : ℂ) • state := Subtype.ext homogeneous
  have eq := LinearMap.congr_fun
    (corrected_homotopy_N F B H hHG hGH beta level hp critical) state
  change nE (homotopy state) - homotopy (nE state) = -homotopy state at eq
  rw [number, map_smul] at eq
  have lowered : nE (homotopy state) = ((degree - 1 : ℤ) : ℂ) • homotopy state := by
    calc
      _ = -homotopy state + (degree : ℂ) • homotopy state := sub_eq_iff_eq_add.mp eq
      _ = _ := by simp only [Int.cast_sub, Int.cast_one, sub_smul, one_smul]; abel
  exact congrArg Subtype.val lowered

private theorem sector_inversePolynomial_coe (n : ℕ) (v : E) :
    (FinitePerturbation.inversePolynomial (hE * (qE - dE)) n v : State D) =
      FinitePerturbation.inversePolynomial
        (h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)) n v.val := by
  have powers (j : ℕ) (w : E) :
      (((-(hE * (qE - dE))) ^ j) w : State D) =
        ((-(h F B beta * (LatticeBRST.totalCharge D H - d0 F beta))) ^ j) w.val := by
    induction j generalizing w with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, pow_succ]
      change (((-(hE * (qE - dE))) ^ j) ((-(hE * (qE - dE))) w) : State D) = _
      rw [ih]
      rfl
  simp only [FinitePerturbation.inversePolynomial, LinearMap.sum_apply,
    Submodule.coe_sum, powers]

private theorem ground_fixed (u : U) : pE u.val = u.val := by
  obtain ⟨v, hv⟩ := u.property
  rw [← hv]
  apply Subtype.ext
  exact LinearMap.congr_fun (spectral_projection_inverse F B).2.2.1 v.val

/-- The same actual compression as the native full-momentum transfer,
restricted to the actual finite energy sector. Both zero modes are retained. -/
theorem actual_sector_transferred_compression (u : U) :
    ((transferred u : E) : State D) =
      (P0 F B * LatticeMatterGhostCoupling.ghostC D 0 * totalL0 H * P0 F B)
        (u.val : State D) := by
  have hP : P0 F B (u.val : State D) = (u.val : State D) :=
    congrArg Subtype.val (ground_fixed F B H hHG hGH beta level u)
  have hcharge : chargeProject beta (u.val : State D) = (u.val : State D) :=
    u.val.property.1
  have hI : ((inclusion u : E) : State D) =
      FinitePerturbation.inversePolynomial
        (h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)) cutoff
          (u.val : State D) :=
    sector_inversePolynomial_coe F B H hHG hGH beta level cutoff u.val
  have tail := LinearMap.congr_fun
    (LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression
      F B H hHG hGH beta cutoff (by omega)) (u.val : State D)
  simp only [Module.End.mul_apply] at tail
  rw [hcharge, hP] at tail
  have hd0 : d0 F beta (u.val : State D) = 0 := by
    rw [← hP]
    exact LinearMap.congr_fun (d0_mul_P0 F B beta) (u.val : State D)
  have compress := LinearMap.congr_fun
    (LatticeBRSTQuartetGroundCompression.original_Q_ground_compression F B H hHG hGH)
      (u.val : State D)
  change P0 F B ((LatticeBRST.totalCharge D H - d0 F beta)
      ((inclusion u : E) : State D)) = _
  rw [hI, tail]
  simp only [LinearMap.sub_apply, hd0, sub_zero]
  simpa only [Module.End.mul_apply, hP] using compress

private theorem on_shell_transferred_zero
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0) : transferred = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  change ((transferred u : E) : State D) = 0
  rw [actual_sector_transferred_compression F B H hHG hGH beta level hp critical]
  have hP : P0 F B (u.val : State D) = (u.val : State D) :=
    congrArg Subtype.val (ground_fixed F B H hHG hGH beta level u)
  have energyZero : totalL0 H (u.val : State D) = 0 := by
    rw [u.val.property.2, shell, zero_smul]
  simp only [Module.End.mul_apply, hP, energyZero, map_zero]

/-- The saved simultaneous relative-preimage mechanism for CURRENT ORIGINAL Q.
The incoming primitive ranges over ALL original State D. The output is the
actual corrected H applied to the cycle in the same literal fixed sector.
All critical, Gram, chart, shell and integer-grading conditions remain explicit. -/
theorem relative_ambient_boundary_homotopy_preimage
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0)
    (degree : ℤ) (state : E)
    (relative : ghostB0 state.val = 0)
    (cycle : LatticeBRST.totalCharge D H state.val = 0)
    (homogeneous : N D state.val = (degree : ℂ) • state.val)
    (ambientBoundary : ∃ preimage : State D,
      LatticeBRST.totalCharge D H preimage = state.val) :
    let preimage := homotopy state
    ghostB0 preimage.val = 0 ∧
      N D preimage.val = ((degree - 1 : ℤ) : ℂ) • preimage.val ∧
      LatticeBRST.totalCharge D H preimage.val = state.val := by
  dsimp only
  have laws := actual_nonzero_charge_original_q_transfer
    F B H hHG hGH beta level hp critical
  have differentialZero := on_shell_transferred_zero
    F B H hHG hGH beta level hp critical shell
  obtain ⟨sectorPreimage, sectorEquation⟩ :=
    (ambient_boundary_sector_preimage F B H hHG hGH beta level state).mp ambientBoundary
  have projectionZero : projection state = 0 := by
    have chain := LinearMap.congr_fun laws.projection_chain sectorPreimage
    have equation : FinitePerturbation.Input.D c sectorPreimage = state := by
      rw [input_D]
      exact sectorEquation
    simpa only [LinearMap.comp_apply, equation, differentialZero, LinearMap.zero_apply]
      using chain
  have cycleZero : qE state = 0 := Subtype.ext cycle
  have preimageEquation : qE (homotopy state) = state := by
    have contraction := LinearMap.congr_fun laws.homotopy state
    rw [input_D] at contraction
    simpa only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.one_apply, LinearMap.comp_apply, cycleZero, projectionZero,
      map_zero, add_zero, sub_zero] using contraction
  have antighostZero : bE state = 0 := Subtype.ext relative
  have relativePreimage : bE (homotopy state) = 0 := by
    have compatibility := LinearMap.congr_fun
      (B0_corrected_homotopy_compatibility
        F B H hHG hGH beta level hp critical shell) state
    simpa only [LinearMap.add_apply, Module.End.mul_apply, antighostZero,
      map_zero, add_zero, LinearMap.zero_apply] using compatibility
  exact ⟨congrArg Subtype.val relativePreimage,
    corrected_homotopy_ghost_degree F B H hHG hGH beta level hp critical
      degree state homogeneous,
    congrArg Subtype.val preimageEquation⟩

/-- Equality of two degree-one relative cycles in the LITERAL GLOBAL original
kernel/range quotient is equivalent to a same-sector degree-zero relative
primitive of their difference. The quotient and unrestricted incoming range
are precisely the existing `LatticeBRSTCohomologyField` ones. -/
theorem literal_physical_equality_iff_relative_preimage
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0)
    (first second : E)
    (firstCycle : LatticeBRST.totalCharge D H first.val = 0)
    (secondCycle : LatticeBRST.totalCharge D H second.val = 0)
    (firstRelative : ghostB0 first.val = 0) (secondRelative : ghostB0 second.val = 0)
    (firstDegree : N D first.val = first.val) (secondDegree : N D second.val = second.val) :
    (LatticeBRSTCohomologyField.classOf D H critical hHG hGH
        (⟨first.val, firstCycle⟩ : LatticeBRSTCohomologyField.cycles D H) =
      LatticeBRSTCohomologyField.classOf D H critical hHG hGH
        (⟨second.val, secondCycle⟩ : LatticeBRSTCohomologyField.cycles D H)) ↔
      ∃ preimage : E, ghostB0 preimage.val = 0 ∧ N D preimage.val = 0 ∧
        LatticeBRST.totalCharge D H preimage.val = first.val - second.val := by
  constructor
  · intro equality
    have member := (Submodule.Quotient.eq
      (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mp equality
    have ambient := (LatticeBRSTCohomologyField.mem_boundaries
      D H critical hHG hGH _).mp member
    change ∃ preimage : State D,
      LatticeBRST.totalCharge D H preimage = first.val - second.val at ambient
    have relativeDifference : ghostB0 (first - second).val = 0 := by
      simp only [Submodule.coe_sub, map_sub, firstRelative, secondRelative, sub_self]
    have cycleDifference : LatticeBRST.totalCharge D H (first - second).val = 0 := by
      simp only [Submodule.coe_sub, map_sub, firstCycle, secondCycle, sub_self]
    have degreeDifference : N D (first - second).val = (1 : ℂ) • (first - second).val := by
      simp only [Submodule.coe_sub, map_sub, firstDegree, secondDegree, one_smul]
    have repaired := relative_ambient_boundary_homotopy_preimage
      F B H hHG hGH beta level hp critical shell 1 (first - second)
        relativeDifference cycleDifference degreeDifference ambient
    refine ⟨homotopy (first - second), repaired.1, ?_, repaired.2.2⟩
    simpa only [sub_self, Int.cast_zero, zero_smul] using repaired.2.1
  · rintro ⟨preimage, _relative, _homogeneous, equation⟩
    apply (Submodule.Quotient.eq
      (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mpr
    apply (LatticeBRSTCohomologyField.mem_boundaries D H critical hHG hGH _).mpr
    exact ⟨preimage.val, equation⟩

end D5.S3.VertexAlgebra.LatticeBRSTRelativeAmbientPreimage
