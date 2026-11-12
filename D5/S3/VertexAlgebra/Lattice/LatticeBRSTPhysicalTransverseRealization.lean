import D5.S3.VertexAlgebra.Lattice.LatticeBRSTPhysicalPairing
import D5.S3.VertexAlgebra.Lattice.LatticeRealNullFrame
import D5.S3.VertexAlgebra.SourceBPZ.TransverseHermitian
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTInsertedTailOrthogonality
import Batteries.Tactic.OpenPrivate

/-!
SOURCE ONLY: no parser, elaborator, compiler or kernel has checked this file.

Actual finite-HPL realization in the literal current physicalImage. The
incoming boundaries remain the supplied global comap, hence range(Q) on ALL
State D. The maps below use finiteInput and its existing K/J, with their
proved two-sided inverse laws. No replacement Q, pairing, quotient, transfer
certificate, target assumption or old/new operator equality is introduced.

The saved OriginalQRelativeFiniteHpl, OriginalQEnergyInclusionPairing and
RelativePairing.Native{TransverseCoordinates,PhysicalRealization} are argument
sources only. Their operators and rotated form are not imported. The actual
absolute ghost-number classifications are already supplied by
LatticeBRSTFullGhostNumberCohomology; this file does not reproduce them.

Attribution: BRST (Becchi--Rouet--Stora--Tyutin), Kato--Ogawa,
Lian--Zuckerman; finite HPL of Gugenheim--Lambe--Stasheff. Current lattice,
real-geometry, ordinary ghost Hermitian and factorial-Fock suppliers retain
their Bakalov--Kac, Carnahan, Kytölä, Mathlib and Batteries attribution and
license notices. This is an unaccepted intermediate, not full string theory.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private sector_B0_d0 sector_B0_h sector_N_hdelta sector_N_delta
  input_D ground_fixed on_shell_transferred_zero
  from D5.S3.VertexAlgebra.Lattice.LatticeBRSTRelativeAmbientPreimage
open private N_P0 N_h
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
open private native_groundMap
  from D5.S3.VertexAlgebra.Lattice.LatticeBRSTFullGhostNumberCohomology
open private groundMap_mem_shell_iff
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
open private normalizedPerturbation_raises
  from D5.S3.VertexAlgebra.Lattice.LatticeBRSTFiniteTransfer
open private projected_input_support
  from D5.S3.VertexAlgebra.Lattice.LatticeBRSTQuartetTransferTail

namespace D5.S3.VertexAlgebra.LatticeBRSTPhysicalTransverseRealization

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeBRSTPerturbationFiltration
open LatticeBRSTFiniteTransfer LatticeBRSTRelativeAmbientPreimage
open LatticeMatterGhostCoupling (ghostB ghostC)
open LatticeMatterGhostHermitian LatticeBRSTPhysicalPairing
open LatticeRelativeBRSTCohomology.Number (N)
open LatticeRelativeBRSTCohomology.Ground (energyTarget)
open D5.S3.HomologicalAlgebra
open LatticeBRSTInsertedTailOrthogonality

variable {D : LatticeData}

private theorem inverse_naturality {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Z A K : Module.End ℂ W) (hZA : Z * A = A * Z)
    (hKA : K * A = 1) (hAK : A * K = 1) : Z * K = K * Z := by
  calc
    Z * K = (K * A) * (Z * K) := by rw [hKA, one_mul]
    _ = K * (A * Z) * K := by noncomm_ring
    _ = K * (Z * A) * K := by rw [← hZA]
    _ = (K * Z) * (A * K) := by noncomm_ring
    _ = K * Z := by rw [hAK, mul_one]

section FiniteRealization

variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ) (hp : F.pPlus beta ≠ 0)
variable (critical : D.rank = 26)

local notation "E" => fixedSector H beta level
local notation "U" => LatticeBRSTFiniteTransfer.quartetGround F B H hHG hGH beta level
local notation "qE" => sectorQ F B H hHG hGH beta level
local notation "dE" => sectorD0 F B H hHG hGH beta level
local notation "hE" => sectorH F B H hHG hGH beta level
local notation "pE" => sectorP0 F B H hHG hGH beta level
local notation "bE" => sectorB0 H beta level
local notation "nE" => sectorN F B H hHG hGH beta level
local notation "c" => finiteInput F B H hHG hGH beta level hp critical
local notation "cutoff" => (2 * level.toNat + 2)
local notation "inc" => c.I cutoff
local notation "proj" => c.P cutoff
local notation "hom" => c.H cutoff
local notation "laws" => actual_nonzero_charge_original_q_transfer
  F B H hHG hGH beta level hp critical

private theorem sector_B0_P0 : bE * pE = pE * bE := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (LinearMap.congr_fun (P0_commutes_b0 F B) x.val).symm

/-- Actual antighost restricted to the actual range of the sector projector. -/
def groundB0 : Module.End ℂ U where
  toFun u := ⟨bE u.val, by
    obtain ⟨x, hx⟩ := u.property
    refine ⟨bE x, ?_⟩
    rw [← hx]
    exact (LinearMap.congr_fun (sector_B0_P0 F B H hHG hGH beta level) x).symm⟩
  map_add' _ _ := Subtype.ext (map_add bE _ _)
  map_smul' _ _ := Subtype.ext (map_smul bE _ _)

private theorem sector_N_P0 : nE * pE = pE * nE := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (sub_eq_zero.mp (N_P0 F B)) x.val

/-- Native N on the same literal projector range, before selecting a branch. -/
def groundN : Module.End ℂ U where
  toFun u := ⟨nE u.val, by
    obtain ⟨x, hx⟩ := u.property
    refine ⟨nE x, ?_⟩
    rw [← hx]
    exact (LinearMap.congr_fun (sector_N_P0 F B H hHG hGH beta level) x).symm⟩
  map_add' _ _ := Subtype.ext (map_add nE _ _)
  map_smul' _ _ := Subtype.ext (map_smul nE _ _)

private theorem sector_B0_delta
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    bE * c.delta + c.delta * bE = 0 := by
  change bE * (qE - dE) + (qE - dE) * bE = 0
  have hq : bE * qE + qE * bE = 0 := by
    rw [add_comm, sector_B0_original_ward, shell, zero_smul]
  calc
    _ = (bE * qE + qE * bE) - (bE * dE + dE * bE) := by noncomm_ring
    _ = 0 := by rw [hq, sector_B0_d0, sub_self]

/-- B0 commutes with BOTH genuine finite inverse operators on the shell.
The naturality calculation consumes the actual K/J two-sided inverse laws. -/
theorem finite_B0_inverses
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    bE * c.K cutoff = c.K cutoff * bE ∧
      bE * c.J cutoff = c.J cutoff * bE := by
  have hb : bE * c.h = -(c.h * bE) :=
    eq_neg_iff_add_eq_zero.mpr (sector_B0_h F B H hHG hGH beta level)
  have hd : bE * c.delta = -(c.delta * bE) :=
    eq_neg_iff_add_eq_zero.mpr
      (sector_B0_delta F B H hHG hGH beta level hp critical shell)
  have hk : bE * (c.h * c.delta) = (c.h * c.delta) * bE := by
    calc
      _ = (bE * c.h) * c.delta := by noncomm_ring
      _ = -(c.h * bE) * c.delta := by rw [hb]
      _ = -c.h * (bE * c.delta) := by noncomm_ring
      _ = _ := by rw [hd]; noncomm_ring
  have hj : bE * (c.delta * c.h) = (c.delta * c.h) * bE := by
    calc
      _ = (bE * c.delta) * c.h := by noncomm_ring
      _ = -(c.delta * bE) * c.h := by rw [hd]
      _ = -c.delta * (bE * c.h) := by noncomm_ring
      _ = _ := by rw [hb]; noncomm_ring
  constructor
  · exact inverse_naturality bE (1 + c.h * c.delta) (c.K cutoff)
      (by simpa only [mul_add, add_mul, mul_one, one_mul] using
        congrArg (fun x => bE + x) hk) laws.K_left laws.K_right
  · exact inverse_naturality bE (1 + c.delta * c.h) (c.J cutoff)
      (by simpa only [mul_add, add_mul, mul_one, one_mul] using
        congrArg (fun x => bE + x) hj) laws.J_left laws.J_right

/-- Actual corrected inclusion AND projection are compatible with actual B0. -/
theorem finite_B0_inclusion_projection
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    bE.comp inc = inc.comp (groundB0 F B H hHG hGH beta level) ∧
      proj.comp bE = (groundB0 F B H hHG hGH beta level).comp proj := by
  have hi := finite_B0_inverses F B H hHG hGH beta level hp critical shell
  constructor
  · apply LinearMap.ext
    intro u
    exact LinearMap.congr_fun hi.1 u.val
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change pE (c.J cutoff (bE x)) = bE (pE (c.J cutoff x))
    rw [← show bE (c.J cutoff x) = c.J cutoff (bE x) from
      LinearMap.congr_fun hi.2 x]
    exact (LinearMap.congr_fun (sector_B0_P0 F B H hHG hGH beta level)
      (c.J cutoff x)).symm

/-- Native ghost number commutes with the actual finite K, independently of shell. -/
theorem finite_N_K : nE * c.K cutoff = c.K cutoff * nE := by
  exact inverse_naturality nE (1 + c.h * c.delta) (c.K cutoff)
    (by simpa only [mul_add, add_mul, mul_one, one_mul] using
      congrArg (fun x => nE + x)
        (sector_N_hdelta F B H hHG hGH beta level)) laws.K_left laws.K_right

private theorem sector_N_deltah :
    nE * (c.delta * c.h) = (c.delta * c.h) * nE := by
  have nd := sector_N_delta F B H hHG hGH beta level
  have nh : nE * c.h - c.h * nE = -c.h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (N_h F B beta) x.val
  change nE * c.delta - c.delta * nE = c.delta at nd
  linear_combination (norm := noncomm_ring) nd * c.h + c.delta * nh

/-- Native ghost number commutes with the actual finite J too. -/
theorem finite_N_J : nE * c.J cutoff = c.J cutoff * nE := by
  exact inverse_naturality nE (1 + c.delta * c.h) (c.J cutoff)
    (by simpa only [mul_add, add_mul, mul_one, one_mul] using
      congrArg (fun x => nE + x)
        (sector_N_deltah F B H hHG hGH beta level hp critical))
    laws.J_left laws.J_right

theorem finite_N_inclusion_projection :
    nE.comp inc = inc.comp (groundN F B H hHG hGH beta level) ∧
      proj.comp nE = (groundN F B H hHG hGH beta level).comp proj := by
  constructor
  · apply LinearMap.ext
    intro u
    exact LinearMap.congr_fun
      (finite_N_K F B H hHG hGH beta level hp critical) u.val
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change pE (c.J cutoff (nE x)) = nE (pE (c.J cutoff x))
    rw [← show nE (c.J cutoff x) = c.J cutoff (nE x) from
      LinearMap.congr_fun (finite_N_J F B H hHG hGH beta level hp critical) x]
    exact (LinearMap.congr_fun (sector_N_P0 F B H hHG hGH beta level)
      (c.J cutoff x)).symm

/-- Actual zero-count range in this sector maps into current absoluteGround. -/
def groundToAbsolute : U →ₗ[ℂ]
    LatticeBRSTAbsoluteQuartetGround.absoluteGround F B beta where
  toFun u := ⟨u.val.val,
    congrArg Subtype.val (ground_fixed F B H hHG hGH beta level u),
    u.val.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- These are current actual polynomial coordinates, not coordinates defined
by choosing preimages of the desired physical realization. -/
def groundCoordinates : U →ₗ[ℂ]
    (MvPolynomial (Fin t × ℕ) ℂ × MvPolynomial (Fin t × ℕ) ℂ) :=
  (LatticeBRSTAbsoluteGroundCohomology.coordinates F B beta).toLinearMap.comp
    (groundToAbsolute F B H hHG hGH beta level)

private theorem ground_coordinate_state (u : U) :
    LatticeBRSTAbsoluteQuartetGround.G F B beta
        (groundCoordinates F B H hHG hGH beta level u) = u.val.val := by
  exact congrArg Subtype.val
    (LatticeBRSTAbsoluteGroundCohomology.groundState_coordinates F B beta
      (groundToAbsolute F B H hHG hGH beta level u))

open private b0_G from D5.S3.VertexAlgebra.Lattice.LatticeBRSTAbsoluteQuartetGround in
/-- Literal b0 removes the second actual absolute-ground coordinate. -/
theorem relative_ground_coordinate_recovery (u : U) (hu : ghostB0 u.val.val = 0) :
    (groundCoordinates F B H hHG hGH beta level u).2 = 0 ∧
      groundMap F B beta (groundCoordinates F B H hHG hGH beta level u).1 = u.val.val := by
  have eq := ground_coordinate_state F B H hHG hGH beta level u
  have hg : groundMap F B beta (groundCoordinates F B H hHG hGH beta level u).2 = 0 := by
    rw [← b0_G, eq]
    exact hu
  have hz := (LatticeRelativeBRSTCohomology.Ground.groundMap_injective F B beta)
    (hg.trans (map_zero (groundMap F B beta)).symm)
  refine ⟨hz, ?_⟩
  simpa only [LatticeBRSTAbsoluteQuartetGround.G, hz, map_zero, add_zero] using eq

variable (shell : groundEnergy beta + (level : ℂ) - 1 = 0)

/-- The uncorrected transverse input in the literal finiteInput retract. -/
def transverseInput : energyTarget D t beta →ₗ[ℂ] U where
  toFun f := by
    have hm := (groundMap_mem_shell_iff F B H hHG hGH beta f.val).mpr f.property
    let v : E := ⟨groundMap F B beta f.val,
      LinearMap.congr_fun (groundMap_identities F B beta).2.2 f.val,
      by simpa only [shell, zero_smul] using hm.2⟩
    have fix : pE v = v := by
      apply Subtype.ext
      exact LatticeRelativeBRSTCohomology.Ground.target_projection_fix F B beta
        ⟨groundMap F B beta f.val, ⟨f.val, f.property, rfl⟩⟩
    exact ⟨v, v, fix⟩
  map_add' f g := by apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
  map_smul' a f := by apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem transverseInput_state (f : energyTarget D t beta) :
    (transverseInput F B H hHG hGH beta level shell f).val.val =
      groundMap F B beta f.val := rfl

private theorem transverseInput_coordinates (f : energyTarget D t beta) :
    groundCoordinates F B H hHG hGH beta level
      (transverseInput F B H hHG hGH beta level shell f) = (f.val, 0) := by
  have eq : groundToAbsolute F B H hHG hGH beta level
      (transverseInput F B H hHG hGH beta level shell f) =
      LatticeBRSTAbsoluteGroundCohomology.groundState F B beta (f.val, 0) := by
    apply Subtype.ext
    simp only [groundToAbsolute, transverseInput_state,
      LatticeBRSTAbsoluteGroundCohomology.groundState,
      LatticeBRSTAbsoluteQuartetGround.G, map_zero, add_zero]
  change LatticeBRSTAbsoluteGroundCohomology.coordinates F B beta _ = _
  rw [eq, LatticeBRSTAbsoluteGroundCohomology.coordinates_groundState]

/-- The corrected finite inclusion really is Q-closed, literal-b0 relative,
and native ghost one. All three properties are derived from current operators. -/
theorem corrected_transverse_physical (f : energyTarget D t beta) :
    let x := inc (transverseInput F B H hHG hGH beta level shell f)
    LatticeBRST.totalCharge D H x.val = 0 ∧ ghostB D 0 x.val = 0 ∧ N D x.val = x.val := by
  dsimp only
  let u := transverseInput F B H hHG hGH beta level shell f
  have hz := on_shell_transferred_zero F B H hHG hGH beta level hp critical shell
  have hq : qE (inc u) = 0 := by
    have eq := LinearMap.congr_fun laws.inclusion_chain u
    rw [input_D] at eq
    simpa only [LinearMap.comp_apply, hz, LinearMap.zero_apply, map_zero] using eq
  have hb : bE u.val = 0 := by
    apply Subtype.ext
    exact LinearMap.congr_fun (groundMap_identities F B beta).2.1 f.val
  have hiB := LinearMap.congr_fun
    (finite_B0_inclusion_projection F B H hHG hGH beta level hp critical shell).1 u
  have hb' : bE (inc u) = 0 := by
    change bE (inc u) = inc (groundB0 F B H hHG hGH beta level u) at hiB
    have hu : groundB0 F B H hHG hGH beta level u = 0 := Subtype.ext hb
    simpa only [hu, map_zero] using hiB
  have hn : nE u.val = u.val := by
    apply Subtype.ext
    exact LinearMap.congr_fun (native_groundMap F B beta) f.val
  have hiN := LinearMap.congr_fun
    (finite_N_K F B H hHG hGH beta level hp critical) u.val
  have hn' : nE (inc u) = inc u := by
    change nE (c.K cutoff u.val) = c.K cutoff (nE u.val) at hiN
    simpa only [hn] using hiN
  exact ⟨congrArg Subtype.val hq, congrArg Subtype.val hb', congrArg Subtype.val hn'⟩

/-- Physical representatives in exactly the supplied physicalCycles. -/
def physicalLift : energyTarget D t beta →ₗ[ℂ] physicalCycles H beta level where
  toFun f := ⟨inc (transverseInput F B H hHG hGH beta level shell f),
    corrected_transverse_physical F B H hHG hGH beta level hp critical shell f⟩
  map_add' f g := by apply Subtype.ext; simp only [map_add]
  map_smul' a f := by apply Subtype.ext; simp only [map_smul]

private theorem projected_relative (a : physicalCycles H beta level) :
    ghostB0 (proj a.val).val.val = 0 := by
  have hb : bE a.val = 0 := Subtype.ext a.property.2.1
  have eq := LinearMap.congr_fun
    (finite_B0_inclusion_projection F B H hHG hGH beta level hp critical shell).2 a.val
  have hz : groundB0 F B H hHG hGH beta level (proj a.val) = 0 := by
    simpa only [LinearMap.comp_apply, hb, map_zero] using eq.symm
  exact congrArg (fun u : U => u.val.val) hz

private theorem projected_polynomial_mem (a : physicalCycles H beta level) :
    (groundCoordinates F B H hHG hGH beta level (proj a.val)).1 ∈ energyTarget D t beta := by
  have recover := (relative_ground_coordinate_recovery F B H hHG hGH beta level
    (proj a.val) (projected_relative F B H hHG hGH beta level hp critical shell a)).2
  apply (groundMap_mem_shell_iff F B H hHG hGH beta _).mp
  rw [recover]
  refine ⟨⟨fixedSector_mem_fixedMomentum F B H hHG hGH beta level (proj a.val).val,
    projected_relative F B H hHG hGH beta level hp critical shell a⟩, ?_⟩
  simpa only [shell, zero_smul] using (proj a.val).val.property.2

/-- Actual finite projection followed by the existing transverse polynomial
coordinate inverse. The polynomial energy condition is proved, not assumed. -/
def physicalProjection : physicalCycles H beta level →ₗ[ℂ] energyTarget D t beta :=
  (((LinearMap.fst ℂ (MvPolynomial (Fin t × ℕ) ℂ) (MvPolynomial (Fin t × ℕ) ℂ)).comp
    (groundCoordinates F B H hHG hGH beta level)).comp
      (proj.comp (physicalCycles H beta level).subtype)).codRestrict _
        (projected_polynomial_mem F B H hHG hGH beta level hp critical shell)

/-- Exact recovery of the projected CURRENT state from transverse coordinates. -/
theorem projected_state_recovery (a : physicalCycles H beta level) :
    groundMap F B beta
      (physicalProjection F B H hHG hGH beta level hp critical shell a).val =
      (proj a.val).val.val :=
  (relative_ground_coordinate_recovery F B H hHG hGH beta level (proj a.val)
    (projected_relative F B H hHG hGH beta level hp critical shell a)).2

theorem physicalProjection_lift (f : energyTarget D t beta) :
    physicalProjection F B H hHG hGH beta level hp critical shell
      (physicalLift F B H hHG hGH beta level hp critical shell f) = f := by
  apply Subtype.ext
  have ret := LinearMap.congr_fun laws.retract
    (transverseInput F B H hHG hGH beta level shell f)
  change (groundCoordinates F B H hHG hGH beta level (proj (inc _))).1 = f.val
  rw [show proj (inc (transverseInput F B H hHG hGH beta level shell f)) =
    transverseInput F B H hHG hGH beta level shell f from ret,
    transverseInput_coordinates]

/-- An unrestricted incoming global boundary has zero actual coordinates. -/
theorem physicalProjection_boundary (a : physicalCycles H beta level)
    (ha : a ∈ physicalBoundaries H beta level critical hHG hGH) :
    physicalProjection F B H hHG hGH beta level hp critical shell a = 0 := by
  obtain ⟨y, hy⟩ := (ambient_boundary_sector_preimage F B H hHG hGH beta level a.val).mp
    ((mem_physicalBoundaries H beta level critical hHG hGH a).mp ha)
  have eq := LinearMap.congr_fun laws.projection_chain y
  rw [input_D] at eq
  have hz : proj a.val = 0 := by
    simpa only [LinearMap.comp_apply, hy,
      on_shell_transferred_zero F B H hHG hGH beta level hp critical shell,
      LinearMap.zero_apply] using eq
  apply Subtype.ext
  change (groundCoordinates F B H hHG hGH beta level (proj a.val)).1 = 0
  rw [hz, map_zero]
  rfl

def quotientProjection : PhysicalQuotient H beta level critical hHG hGH →ₗ[ℂ]
    energyTarget D t beta :=
  (physicalBoundaries H beta level critical hHG hGH).liftQ
    (physicalProjection F B H hHG hGH beta level hp critical shell)
    (by intro a ha; exact physicalProjection_boundary
      F B H hHG hGH beta level hp critical shell a ha)

/-- Actual coordinate inverse on the LITERAL physicalImage in global cohomology. -/
def imageProjection : physicalImage H beta level critical hHG hGH →ₗ[ℂ]
    energyTarget D t beta :=
  (quotientProjection F B H hHG hGH beta level hp critical shell).comp
    (physicalImageEquiv H beta level critical hHG hGH).symm.toLinearMap

def transverseRealization : energyTarget D t beta →ₗ[ℂ]
    physicalImage H beta level critical hHG hGH :=
  (imageClass H beta level critical hHG hGH).comp
    (physicalLift F B H hHG hGH beta level hp critical shell)

@[simp] theorem imageProjection_imageClass (a : physicalCycles H beta level) :
    imageProjection F B H hHG hGH beta level hp critical shell
      (imageClass H beta level critical hHG hGH a) =
      physicalProjection F B H hHG hGH beta level hp critical shell a := by
  rw [← physicalImageEquiv_mk H beta level critical hHG hGH a]
  change quotientProjection F B H hHG hGH beta level hp critical shell
    ((physicalImageEquiv H beta level critical hHG hGH).symm
      (physicalImageEquiv H beta level critical hHG hGH _)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

@[simp] theorem imageProjection_realization (f : energyTarget D t beta) :
    imageProjection F B H hHG hGH beta level hp critical shell
      (transverseRealization F B H hHG hGH beta level hp critical shell f) = f := by
  change imageProjection F B H hHG hGH beta level hp critical shell
    (imageClass H beta level critical hHG hGH
      (physicalLift F B H hHG hGH beta level hp critical shell f)) = f
  rw [imageProjection_imageClass, physicalProjection_lift]

/-- The actual homotopy supplies a primitive of the difference from the
corrected transverse representative. This is an equation for the original Q. -/
theorem actual_class_recovery (a : physicalCycles H beta level) :
    LatticeBRST.totalCharge D H (hom a.val).val =
      a.val.val -
        (physicalLift F B H hHG hGH beta level hp critical shell
          (physicalProjection F B H hHG hGH beta level hp critical shell a)).val.val := by
  have hq : qE a.val = 0 := Subtype.ext a.property.1
  have eq := LinearMap.congr_fun laws.homotopy a.val
  rw [input_D] at eq
  have hu : transverseInput F B H hHG hGH beta level shell
      (physicalProjection F B H hHG hGH beta level hp critical shell a) = proj a.val := by
    apply Subtype.ext
    apply Subtype.ext
    exact projected_state_recovery F B H hHG hGH beta level hp critical shell a
  have he : qE (hom a.val) = a.val - inc (proj a.val) := by
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hq, map_zero, add_zero,
      LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply] using eq
  change LatticeBRST.totalCharge D H (hom a.val).val =
    a.val.val - (inc (transverseInput F B H hHG hGH beta level shell
      (physicalProjection F B H hHG hGH beta level hp critical shell a))).val
  rw [hu]
  exact congrArg Subtype.val he

theorem realization_physicalClass (a : physicalCycles H beta level) :
    transverseRealization F B H hHG hGH beta level hp critical shell
      (physicalProjection F B H hHG hGH beta level hp critical shell a) =
      imageClass H beta level critical hHG hGH a := by
  apply Subtype.ext
  apply (Submodule.Quotient.eq
    (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mpr
  apply (LatticeBRSTCohomologyField.mem_boundaries D H critical hHG hGH _).mpr
  refine ⟨-(hom a.val).val, ?_⟩
  rw [map_neg, actual_class_recovery F B H hHG hGH beta level hp critical shell a]
  change -(a.val.val - _) = _ - a.val.val
  abel

@[simp] theorem realization_imageProjection
    (x : physicalImage H beta level critical hHG hGH) :
    transverseRealization F B H hHG hGH beta level hp critical shell
      (imageProjection F B H hHG hGH beta level hp critical shell x) = x := by
  obtain ⟨a, ha⟩ := x.property
  have hx : x = imageClass H beta level critical hHG hGH a := Subtype.ext ha.symm
  rw [hx, imageProjection_imageClass, realization_physicalClass]

/-- A genuine inverse pair on the literal current physicalImage. -/
def physicalTransverseEquiv : energyTarget D t beta ≃ₗ[ℂ]
    physicalImage H beta level critical hHG hGH :=
  { transverseRealization F B H hHG hGH beta level hp critical shell,
    { toFun := transverseRealization F B H hHG hGH beta level hp critical shell
      invFun := imageProjection F B H hHG hGH beta level hp critical shell
      left_inv := imageProjection_realization F B H hHG hGH beta level hp critical shell
      right_inv := realization_imageProjection F B H hHG hGH beta level hp critical shell } with }

/-- The finite positive-power part of the GENUINE inclusion polynomial.
The sum is sectorwise finite for every INTEGER level, including negative. -/
def inclusionTail (f : energyTarget D t beta) : E :=
  ∑ r ∈ (Finset.range cutoff).erase 0,
    ((-(c.h * c.delta)) ^ r)
      (transverseInput F B H hHG hGH beta level shell f).val

private theorem inclusion_expansion (f : energyTarget D t beta) :
    (physicalLift F B H hHG hGH beta level hp critical shell f).val =
      (transverseInput F B H hHG hGH beta level shell f).val +
        inclusionTail F B H hHG hGH beta level hp critical shell f := by
  classical
  change c.K cutoff (transverseInput F B H hHG hGH beta level shell f).val = _
  simp only [FinitePerturbation.Input.K, FinitePerturbation.inversePolynomial,
    LinearMap.sum_apply]
  have h0 : 0 ∈ Finset.range cutoff := Finset.mem_range.mpr (by omega)
  simpa only [pow_zero, Module.End.one_apply, inclusionTail] using
    (Finset.add_sum_erase (Finset.range cutoff)
    (fun r => ((-(c.h * c.delta)) ^ r)
      (transverseInput F B H hHG hGH beta level shell f).val) h0).symm

private theorem input_lower_zero (f : energyTarget D t beta) :
    groundMap F B beta f.val ∈ signedFiltration F B beta level 0 := by
  let u := transverseInput F B H hHG hGH beta level shell f
  have hfix : P0 F B u.val.val = u.val.val :=
    congrArg Subtype.val (ground_fixed F B H hHG hGH beta level u)
  have hs := (projected_input_support F B beta u.val.val).2
  rw [u.val.property.1, hfix] at hs
  apply (mem_signedFiltration_iff F B beta level 0 _).mpr
  intro i hi
  have sector := (mem_fixedSector_iff F B H hHG hGH beta level u.val.val).mp
    u.val.property i hi
  exact ⟨sector.1, sector.2, hs i hi⟩

/-- Actual inclusion tail: signed degree at least one, native ghost one,
and an exact original-state expansion. No orthogonality is assumed here. -/
theorem actual_inclusion_positive_tail (f : energyTarget D t beta) :
    let tail := inclusionTail F B H hHG hGH beta level hp critical shell f
    tail.val ∈ signedFiltration F B beta level 1 ∧
      N D tail.val = tail.val ∧
      (physicalLift F B H hHG hGH beta level hp critical shell f).val.val =
        groundMap F B beta f.val + tail.val := by
  classical
  dsimp only
  let u := transverseInput F B H hHG hGH beta level shell f
  let A := h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)
  have powers (r : ℕ) : (A ^ r) u.val.val ∈
      signedFiltration F B beta level (r : ℤ) := by
    induction r with
    | zero =>
        simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero] using
          input_lower_zero F B H hHG hGH beta level shell f
    | succ r ih =>
        have step := normalizedPerturbation_raises F B H hHG hGH beta level
          (r : ℤ) ((A ^ r) u.val.val) ih
        simpa only [LatticeBRSTFiniteTransfer.normalizedPerturbation,
          pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one] using step
  have signedPower (r : ℕ) :
      (((( -(c.h * c.delta)) ^ r) u.val) : State D) ∈
        signedFiltration F B beta level (r : ℤ) := by
    have hsign : (-(c.h * c.delta)) ^ r =
        ((-1 : ℂ) ^ r) • (c.h * c.delta) ^ r := by
      simpa only [neg_one_smul] using (smul_pow (-1 : ℂ) (c.h * c.delta) r)
    rw [hsign]
    change ((-1 : ℂ) ^ r) • (((c.h * c.delta) ^ r) u.val : State D) ∈ _
    rw [sector_correction_power_coe F B H hHG hGH beta level]
    exact Submodule.smul_mem _ _ (powers r)
  have lower : (inclusionTail F B H hHG hGH beta level hp critical shell f).val ∈
      signedFiltration F B beta level 1 := by
    change (↑(∑ r ∈ (Finset.range cutoff).erase 0,
      ((-(c.h * c.delta)) ^ r) u.val) : State D) ∈ _
    rw [Submodule.coe_sum]
    apply Submodule.sum_mem
    intro r hr
    have hpos : (1 : ℤ) ≤ (r : ℤ) := by
      have hn := (Finset.mem_erase.mp hr).1
      omega
    apply (mem_signedFiltration_iff F B beta level 1 _).mpr
    intro i hi
    have hd := (mem_signedFiltration_iff F B beta level (r : ℤ) _).mp
      (signedPower r) i hi
    exact ⟨hd.1, hd.2.1, le_trans hpos hd.2.2⟩
  have expand := congrArg Subtype.val
    (inclusion_expansion F B H hHG hGH beta level hp critical shell f)
  have expand' : (physicalLift F B H hHG hGH beta level hp critical shell f).val.val =
      groundMap F B beta f.val +
        (inclusionTail F B H hHG hGH beta level hp critical shell f).val := expand
  have ht : (inclusionTail F B H hHG hGH beta level hp critical shell f).val =
      (physicalLift F B H hHG hGH beta level hp critical shell f).val.val -
        groundMap F B beta f.val := by rw [expand']; abel
  refine ⟨lower, ?_, expand'⟩
  rw [ht, map_sub,
    (physicalLift F B H hHG hGH beta level hp critical shell f).property.2.2,
    LinearMap.congr_fun (native_groundMap F B beta) f.val]

variable (plusReal : ∀ i, star (F.ePlus i) = F.ePlus i)
variable (minusReal : ∀ i, star (F.eMinus i) = F.eMinus i)

/-- Both ordinary inserted-c0 slots of the ACTUAL corrected inclusion.
The two mixed terms and the tail-tail term vanish by the current-coordinate
selection theorem; the conclusion is not an HPL or positivity input. -/
theorem actual_corrected_inserted_recovery (f g : energyTarget D t beta) :
    inserted
      (physicalLift F B H hHG hGH beta level hp critical shell f).val.val
      (physicalLift F B H hHG hGH beta level hp critical shell g).val.val =
      inserted (groundMap F B beta f.val) (groundMap F B beta g.val) := by
  let tf := (inclusionTail F B H hHG hGH beta level hp critical shell f).val
  let tg := (inclusionTail F B H hHG hGH beta level hp critical shell g).val
  have ef := actual_inclusion_positive_tail F B H hHG hGH beta level hp critical shell f
  have eg := actual_inclusion_positive_tail F B H hHG hGH beta level hp critical shell g
  have lf : ∀ i, (actualBasis F B).repr tf i ≠ 0 → 1 ≤ degree i :=
    fun i hi => ((mem_signedFiltration_iff F B beta level 1 _).mp ef.1 i hi).2.2
  have lg : ∀ i, (actualBasis F B).repr tg i ≠ 0 → 1 ≤ degree i :=
    fun i hi => ((mem_signedFiltration_iff F B beta level 1 _).mp eg.1 i hi).2.2
  have bf : ∀ i, (actualBasis F B).repr (groundMap F B beta f.val) i ≠ 0 → 0 ≤ degree i :=
    fun i hi => ((mem_signedFiltration_iff F B beta level 0 _).mp
      (input_lower_zero F B H hHG hGH beta level shell f) i hi).2.2
  have bg : ∀ i, (actualBasis F B).repr (groundMap F B beta g.val) i ≠ 0 → 0 ≤ degree i :=
    fun i hi => ((mem_signedFiltration_iff F B beta level 0 _).mp
      (input_lower_zero F B H hHG hGH beta level shell g) i hi).2.2
  have nf := LinearMap.congr_fun (native_groundMap F B beta) f.val
  have ng := LinearMap.congr_fun (native_groundMap F B beta) g.val
  have tl := inserted_positive_tail_left F B plusReal minusReal tf
    (groundMap F B beta g.val) ef.2.1 ng lf bg
  have tr := inserted_positive_tail_right F B plusReal minusReal
    (groundMap F B beta f.val) tg nf eg.2.1 bf lg
  have tt := inserted_degree_orthogonal F B plusReal minusReal tf tg
    ef.2.1 eg.2.1 1 1 (by norm_num) lf lg
  rw [ef.2.2, eg.2.2, inserted_add_left, inserted_add_right, inserted_add_right,
    tl, tr, tt, add_zero, add_zero, add_zero]

/-- Ordinary inserted form on literal physicalImage, recovered from the
genuine coordinate inverse and the ACTUAL corrected representatives. -/
theorem physicalImageForm_transverse_recovery
    (x y : physicalImage H beta level critical hHG hGH) :
    physicalImageForm F B H hHG hGH beta level hp critical shell x y =
      SourceBPZ.OriginalMatterHermitian.Hm
        (Finsupp.single beta (transverseOriginal F B
          (imageProjection F B H hHG hGH beta level hp critical shell x).val))
        (Finsupp.single beta (transverseOriginal F B
          (imageProjection F B H hHG hGH beta level hp critical shell y).val)) := by
  let f := imageProjection F B H hHG hGH beta level hp critical shell x
  let g := imageProjection F B H hHG hGH beta level hp critical shell y
  have recover := physicalImageForm_recovery F B H hHG hGH beta level hp critical shell x y
    (physicalLift F B H hHG hGH beta level hp critical shell f)
    (physicalLift F B H hHG hGH beta level hp critical shell g)
    (congrArg Subtype.val (realization_imageProjection
      F B H hHG hGH beta level hp critical shell x))
    (congrArg Subtype.val (realization_imageProjection
      F B H hHG hGH beta level hp critical shell y))
  change physicalImageForm F B H hHG hGH beta level hp critical shell x y = _
  change physicalImageForm F B H hHG hGH beta level hp critical shell x y =
    inserted (physicalLift F B H hHG hGH beta level hp critical shell f).val.val
      (physicalLift F B H hHG hGH beta level hp critical shell g).val.val at recover
  rw [recover, actual_corrected_inserted_recovery F B H hHG hGH beta level hp critical
    shell plusReal minusReal f g, inserted_groundMap]

end FiniteRealization

section ConstructedRealGeometry

open LatticeRealNullFrame
open SourceBPZ.OriginalMatterHermitian
open SourceBPZ

/-- The current positive, conjugation-fixed complexBasis supplies the exact
frame expected by the CURRENT factorial/frequency norm supplier. -/
def positiveOrthonormalFrame (P : PositivePlane D) :
    TransverseHermitian.RealOrthonormalFrame D (D.rank - 2) where
  B j := (P.complexBasis j : E D)
  real_B j i := congrFun (P.complexBasis_conjugation_fixed j) i
  orthonormal i j := P.complexBasis_gram i j

open private polynomialEquiv_symm_X completeBasis_transverse from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates in
/-- Equality of the actual transverse substitution with the exact current
norm supplier, proved on generators. This is not equality of BRST operators. -/
theorem positive_transverseOriginal_eq_phi (P : PositivePlane D) :
    transverseOriginal P.complexFrame P.complexBasis = TransverseHermitian.phi (positiveOrthonormalFrame P) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨j,r⟩
  change (P.complexFrame.coordinateEquiv P.complexBasis).symm
      (MvPolynomial.rename transverseVariable (MvPolynomial.X (j,r))) =
    TransverseHermitian.phi (positiveOrthonormalFrame P) (MvPolynomial.X (j,r))
  rw [MvPolynomial.rename_X, polynomialEquiv_symm_X, completeBasis_transverse]
  simpa only [TransverseHermitian.phi, MvPolynomial.aeval_X]

private theorem positive_plus_real (P : PositivePlane D) :
    ∀ i, star (P.complexFrame.ePlus i) = P.complexFrame.ePlus i := by
  intro i
  simp [PositivePlane.complexFrame, complexify]

private theorem positive_minus_real (P : PositivePlane D) :
    ∀ i, star (P.complexFrame.eMinus i) = P.complexFrame.eMinus i := by
  intro i
  simp [PositivePlane.complexFrame, complexify]

variable (P : PositivePlane D)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (beta : Charge D) (level : ℤ) (hp : P.complexFrame.pPlus beta ≠ 0)
variable (critical : D.rank = 26)
variable (shell : groundEnergy beta + (level : ℂ) - 1 = 0)

local notation "image" => physicalImage H beta level critical hHG hGH
local notation "coordinates" => imageProjection P.complexFrame P.complexBasis
  H hHG hGH beta level hp critical shell
local notation "form" => physicalImageForm P.complexFrame P.complexBasis
  H hHG hGH beta level hp critical shell

/-- Exact ordinary inserted-c0 recovery, including its directly computed
positive ghost scalar, in the constructed real transverse coordinates. -/
theorem physicalImageForm_eq_factorial (x y : image) :
    form x y = FactorialFockMetric.inner
      (TransverseHermitian.rescale (D.rank - 2) (coordinates x).val)
      (TransverseHermitian.rescale (D.rank - 2) (coordinates y).val) := by
  rw [physicalImageForm_transverse_recovery P.complexFrame P.complexBasis
    H hHG hGH beta level hp critical shell (positive_plus_real P) (positive_minus_real P),
    positive_transverseOriginal_eq_phi P]
  exact (TransverseHermitian.source_delta_delta_eq_factorial (positiveOrthonormalFrame P)
    beta beta (coordinates x).val (coordinates y).val).trans (if_pos rfl)

/-- The actual physical-image norm is the exact finite factorial/frequency
sum. Its coefficient set is the support of the genuine inverse coordinate. -/
theorem physicalImageForm_eq_exact_finite_sum (x : image) :
    form x x = ∑ nu ∈ (coordinates x).val.support,
      (TransverseHermitian.exactWeight nu : ℂ) *
        (Complex.normSq ((coordinates x).val.coeff nu) : ℂ) := by
  rw [physicalImageForm_eq_factorial P H hHG hGH beta level hp critical shell,
    TransverseHermitian.rescaled_inner_coeff_sum]

/-- Nonzero literal physical classes have nonzero actual transverse coordinates. -/
theorem imageProjection_ne_zero (x : image) (hx : x ≠ 0) : coordinates x ≠ 0 := by
  intro hz
  apply hx
  rw [← realization_imageProjection P.complexFrame P.complexBasis
    H hHG hGH beta level hp critical shell x, hz, map_zero]

/-- Genuine no-ghost positivity for this nonzero-charge chart, arbitrary
integer level and the ACTUAL shell. Reuses the current strict Fock norm. -/
theorem physicalImageForm_strict_positive (x : image) (hx : x ≠ 0) :
    (form x x).im = 0 ∧ 0 < (form x x).re := by
  have hf : (coordinates x).val ≠ 0 := by
    intro hz
    exact imageProjection_ne_zero P H hHG hGH beta level hp critical shell x hx
      (Subtype.ext hz)
  have hs : (Finsupp.single beta (coordinates x).val :
      Charge D →₀ TransverseHermitian.Polynomial (D.rank - 2)) ≠ 0 := by
    simpa only [ne_eq, Finsupp.single_eq_zero] using hf
  have pos := TransverseHermitian.Hm_self_strict_positive (positiveOrthonormalFrame P) hs
  have he : TransverseHermitian.transverseEmbed (positiveOrthonormalFrame P)
      (Finsupp.single beta (coordinates x).val) =
      TransverseHermitian.delta (positiveOrthonormalFrame P) beta (coordinates x).val := by
    simp [TransverseHermitian.transverseEmbed, TransverseHermitian.delta]
  rw [he] at pos
  have eq := TransverseHermitian.source_delta_delta_eq_factorial (positiveOrthonormalFrame P)
    beta beta (coordinates x).val (coordinates x).val
  rw [if_pos rfl] at eq
  rw [eq] at pos
  rwa [physicalImageForm_eq_factorial P H hHG hGH beta level hp critical shell]

theorem physicalImageForm_nonnegative (x : image) :
    (form x x).im = 0 ∧ 0 ≤ (form x x).re := by
  by_cases hx : x = 0
  · subst x
    simp only [map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.zero_re, le_refl,
      and_self]
  · have h := physicalImageForm_strict_positive P H hHG hGH beta level hp critical shell x hx
    exact ⟨h.1, le_of_lt h.2⟩

theorem physicalImageForm_zero_norm_iff (x : image) : form x x = 0 ↔ x = 0 := by
  constructor
  · intro hz
    by_contra hx
    have pos := (physicalImageForm_strict_positive P H hHG hGH beta level hp critical shell x hx).2
    rw [hz] at pos
    exact (lt_irrefl 0) pos
  · intro hx
    subst x
    simp only [map_zero, LinearMap.zero_apply]

/-- The LEFT radical on literal physicalImage is zero. -/
theorem physicalImageForm_left_radical_iff (x : image) :
    (∀ y : image, form x y = 0) ↔ x = 0 := by
  constructor
  · intro hx
    exact (physicalImageForm_zero_norm_iff P H hHG hGH beta level hp critical shell x).mp (hx x)
  · rintro rfl y
    simp only [map_zero, LinearMap.zero_apply]

/-- The RIGHT radical on literal physicalImage is zero. -/
theorem physicalImageForm_right_radical_iff (y : image) :
    (∀ x : image, form x y = 0) ↔ y = 0 := by
  constructor
  · intro hy
    exact (physicalImageForm_zero_norm_iff P H hHG hGH beta level hp critical shell y).mp (hy y)
  · rintro rfl x
    exact map_zero (form x)

private theorem imageClass_zero_iff (a : physicalCycles H beta level) :
    imageClass H beta level critical hHG hGH a = 0 ↔
      a ∈ physicalBoundaries H beta level critical hHG hGH := by
  constructor
  · intro hz
    have he := congrArg Subtype.val hz
    exact (Submodule.Quotient.mk_eq_zero
      (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mp he
  · intro ha
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero
      (LatticeBRSTCohomologyField.boundaries D H critical hHG hGH)).mpr ha

/-- On actual physicalCycles, zero norm is EXACTLY the global-comap
boundaries. The incoming primitive continues to range over ALL State D. -/
theorem physicalCycle_zero_norm_iff (a : physicalCycles H beta level) :
    inserted a.val.val a.val.val = 0 ↔
      a ∈ physicalBoundaries H beta level critical hHG hGH := by
  rw [← show form (imageClass H beta level critical hHG hGH a)
      (imageClass H beta level critical hHG hGH a) = inserted a.val.val a.val.val from
      physicalImageForm_imageClass P.complexFrame P.complexBasis
        H hHG hGH beta level hp critical shell a a,
    physicalImageForm_zero_norm_iff P H hHG hGH beta level hp critical shell,
    imageClass_zero_iff H hHG hGH beta level critical]

theorem physicalCycle_left_radical_iff (a : physicalCycles H beta level) :
    (∀ b : physicalCycles H beta level, inserted a.val.val b.val.val = 0) ↔
      a ∈ physicalBoundaries H beta level critical hHG hGH := by
  constructor
  · intro h
    exact (physicalCycle_zero_norm_iff P H hHG hGH beta level hp critical shell a).mp (h a)
  · intro ha b
    have hz := (imageClass_zero_iff H hHG hGH beta level critical a).mpr ha
    have eq := physicalImageForm_imageClass P.complexFrame P.complexBasis
      H hHG hGH beta level hp critical shell a b
    change form _ _ = inserted a.val.val b.val.val at eq
    rw [hz] at eq
    simpa only [map_zero, LinearMap.zero_apply] using eq.symm

theorem physicalCycle_right_radical_iff (b : physicalCycles H beta level) :
    (∀ a : physicalCycles H beta level, inserted a.val.val b.val.val = 0) ↔
      b ∈ physicalBoundaries H beta level critical hHG hGH := by
  constructor
  · intro h
    exact (physicalCycle_zero_norm_iff P H hHG hGH beta level hp critical shell b).mp (h b)
  · intro hb a
    have hz := (imageClass_zero_iff H hHG hGH beta level critical b).mpr hb
    have eq := physicalImageForm_imageClass P.complexFrame P.complexBasis
      H hHG hGH beta level hp critical shell a b
    change form _ _ = inserted a.val.val b.val.val at eq
    rw [hz, map_zero] at eq
    exact eq.symm

end ConstructedRealGeometry

/-- Original Lorentzian signature, rank 26, BOTH Gram inverses, nonzero
original charge and actual shell give a CONSTRUCTED chart with genuine
physicalImage positivity and both global-comap cycle radicals. No neutral
or all-charge positivity statement is made. The integer level is arbitrary. -/
theorem nonzero_charge_lorentzian_physical_no_ghost
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (critical : D.rank = 26)
    (hneg : sigNeg (LatticeRealNullFrame.Q_R D) = 1)
    (hpos : sigPos (LatticeRealNullFrame.Q_R D) = D.rank - 1)
    (beta : Charge D) (hb : beta ≠ 0) (level : ℤ)
    (shell : groundEnergy beta + (level : ℂ) - 1 = 0) :
    ∃ P : LatticeRealNullFrame.PositivePlane D,
      ∃ hp : P.complexFrame.pPlus beta ≠ 0,
        (∀ x : physicalImage H beta level critical hHG hGH, x ≠ 0 →
          let value := physicalImageForm P.complexFrame P.complexBasis
            H hHG hGH beta level hp critical shell x x
          value.im = 0 ∧ 0 < value.re) ∧
        (∀ a : physicalCycles H beta level,
          (∀ b : physicalCycles H beta level, inserted a.val.val b.val.val = 0) ↔
            a ∈ physicalBoundaries H beta level critical hHG hGH) ∧
        (∀ b : physicalCycles H beta level,
          (∀ a : physicalCycles H beta level, inserted a.val.val b.val.val = 0) ↔
            b ∈ physicalBoundaries H beta level critical hHG hGH) := by
  obtain ⟨P, _hPlus, _hMinus, _hPair, _hReal, hp, _rest⟩ :=
    LatticeRealNullFrame.exists_original_real_geometry D (by omega) hneg hpos beta hb
  exact ⟨P, hp,
    physicalImageForm_strict_positive P H hHG hGH beta level hp critical shell,
    physicalCycle_left_radical_iff P H hHG hGH beta level hp critical shell,
    physicalCycle_right_radical_iff P H hHG hGH beta level hp critical shell⟩

end D5.S3.VertexAlgebra.LatticeBRSTPhysicalTransverseRealization
