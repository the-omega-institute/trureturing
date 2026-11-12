import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFullNonzeroAbsoluteCohomology
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
import Batteries.Tactic.OpenPrivate

/-!
Native ghost number on the literal ENTIRE fixed-momentum original-Q quotient.

The number operator is restricted from id tensor the ORIGINAL ghostNumber,
then descended through the existing kernel/image quotient. In particular the
primitive of N(Q y) is N y + y, with y in the entire fixedMomentum module.
The quotient number operator is defined before, and independently of, the
full-Q cohomology equivalence. Both occupations {1} and {1,3} are retained.

We consume the global N identities of LatticeRelativeBRSTCohomology.Number
through Batteries.OpenPrivate; none of its relative-shell N_K, N_J,
correctedI_N, correctedP_N, inclusion_N or shell simplifications is used.
The actual locally nilpotent K/J inverse equations give naturality of the
actual corrected I/P. No nilpotence, compression, operator equality or
cohomology equivalence is added as a hypothesis of the physical statements.

Attribution: BRST (Becchi--Rouet--Stora--Tyutin), Kato--Ogawa and
Lian--Zuckerman; algebraic HPL of Gugenheim--Lambe--Stasheff. Original
lattice/current/occupation suppliers retain their Bakalov--Kac, Scott
Carnahan and Kalle Kytölä attribution. Mathlib quotient, basis and linear
algebra machinery retains its Apache 2.0 attribution (Johannes Hölzl,
Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Kenny Lau and Joël Riou).
Batteries.OpenPrivate: Mario Carneiro; Microsoft Corporation; Apache 2.0.
Imported supplier license notices are preserved in the immutable inputs.

UNPARSED SOURCE CANDIDATE. The full-Q suppliers are themselves uncompiled
candidates; acceptance of the transfer tail does not accept this endpoint.
No native/kernel/official acceptance, positivity or no-ghost claim is made.
This is one pPlus != 0 chart, without a frame-choice theorem for all nonzero
charges. The full string/AdS-CFT objective remains active and incomplete.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true

noncomputable section
open scoped BigOperators TensorProduct

open private N_totalCharge N_d0 N_h N_P0 N_preserves_fixedMomentum
  N_actualBasis comm_sub comm_mul
  from D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTCohomology
open private K_inverse J_inverse
  from D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation
open private c0_basis
  from D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteQuartetGround

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFullGhostNumberCohomology

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open LatticeRelativeMassShell (fixedMomentum)
open LatticeMatterGhostCoupling (ghostC)
open LatticeRelativeBRSTCohomology.Ground (energyTarget)
open LatticeRelativeBRSTCohomology.Number (N)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteQuartetGround (Poly G absoluteGround)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFullNonzeroAbsoluteCohomology
open D5.S3.Quantum.Fermionic.BcGhostCharge (charge)


variable {D : LatticeData}

local instance : AddCommGroup (Carrier D) := inferInstance
local instance : AddCommGroup (State D) := inferInstance

/-- Restriction of the existing native number operator to ENTIRE momentum. -/
def momentumN (p : Charge D) : Module.End ℂ (fixedMomentum D p) :=
  (N D).restrict (N_preserves_fixedMomentum p)

@[simp] theorem momentumN_coe (p : Charge D) (x : fixedMomentum D p) :
    (momentumN p x : State D) = N D (x : State D) := rfl

variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (p : Charge D)

local instance : AddCommGroup (fixedMomentum D p) := inferInstance
local instance : AddCommGroup (quartetGround F B p) := inferInstance
local instance : AddCommGroup (absoluteGround F B p) := inferInstance
local instance : AddCommGroup (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p) := inferInstance
local instance : AddCommGroup (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH) :=
  inferInstance

local notation "V" => fixedMomentum D p
local notation "U" => quartetGround F B p
local notation "nV" => momentumN p
local notation "qV" => D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorQ D H p
local notation "pV" => momentumP0 F B p

private theorem momentum_N_Q : nV * qV - qV * nV = qV := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (N_totalCharge H) (x : State D)

/-- The unrestricted incoming primitive has the essential extra +y. -/
theorem native_boundary_primitive (y : V) :
    nV (qV y) = qV (nV y + y) := by
  have eq := LinearMap.congr_fun (momentum_N_Q H p) y
  change nV (qV y) - qV (nV y) = qV y at eq
  calc
    nV (qV y) = qV y + qV (nV y) := sub_eq_iff_eq_add.mp eq
    _ = qV (nV y + y) := by rw [map_add, add_comm]

private theorem native_cycle_preserved (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p) :
    qV (nV x.val) = 0 := by
  have eq := LinearMap.congr_fun (momentum_N_Q H p) x.val
  have hx : qV x.val = 0 := x.property
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, hx, map_zero,
    zero_sub, neg_eq_zero] using eq

/-- Actual native N on literal original-Q cycles. -/
def cycleN : Module.End ℂ (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p) :=
  ((nV).comp (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p).subtype).codRestrict _
    (native_cycle_preserved H p)

variable (h26 : D.rank = 26)

private theorem native_boundary_preserved
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p)
    (hx : x ∈ D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p) :
    cycleN H p x ∈ D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p := by
  obtain ⟨y, hy⟩ := (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.mem_sectorBoundaries D H h26 hHG hGH p x).mp hx
  apply (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.mem_sectorBoundaries D H h26 hHG hGH p _).mpr
  refine ⟨nV y + y, ?_⟩
  change qV (nV y + y) = nV x.val
  rw [← native_boundary_primitive H p y, hy]

/-- Descent of ACTUAL N through literal sectorCycles/sectorBoundaries.
This definition neither mentions nor conjugates any target equivalence. -/
def quotientN : Module.End ℂ (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p) :=
  (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p).mapQ
    (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p) (cycleN H p)
    (by intro x hx; exact native_boundary_preserved H hHG hGH p h26 x hx)

@[simp] theorem quotientN_classOf (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p) :
    quotientN H hHG hGH p h26 (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p x) =
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p (cycleN H p x) := rfl

private theorem momentum_N_P0 : nV * pV = pV * nV := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (sub_eq_zero.mp (N_P0 F B)) (x : State D)

/-- Native N on the literal range of the restricted actual P0. -/
def rangeN : Module.End ℂ U where
  toFun u := ⟨nV u.val, by
    obtain ⟨v, hv⟩ := u.property
    refine ⟨nV v, ?_⟩
    rw [← hv]
    exact (LinearMap.congr_fun (momentum_N_P0 F B p) v).symm⟩
  map_add' _ _ := Subtype.ext (map_add nV _ _)
  map_smul' _ _ := Subtype.ext (map_smul nV _ _)

variable (hp : F.pPlus p ≠ 0)
local notation "c" => fullInput F B H hHG hGH p hp h26
local notation "ln" => actual_local_nilpotence F B H hHG hGH p hp h26

private theorem input_N_d0 : nV * (c).d0 - (c).d0 * nV = (c).d0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (N_d0 F p) (x : State D)

private theorem input_N_h : nV * (c).h - (c).h * nV = -(c).h := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (N_h F B p) (x : State D)

private theorem input_N_delta : nV * (c).delta - (c).delta * nV = (c).delta := by
  change nV * (qV - (c).d0) - (qV - (c).d0) * nV = qV - (c).d0
  rw [comm_sub, momentum_N_Q H p, input_N_d0 F B H hHG hGH p h26 hp]

private theorem input_N_hdelta : nV * ((c).h * (c).delta) = ((c).h * (c).delta) * nV := by
  apply sub_eq_zero.mp
  rw [comm_mul, input_N_h F B H hHG hGH p h26 hp,
    input_N_delta F B H hHG hGH p h26 hp]
  noncomm_ring

private theorem input_N_deltah : nV * ((c).delta * (c).h) = ((c).delta * (c).h) * nV := by
  apply sub_eq_zero.mp
  rw [comm_mul, input_N_delta F B H hHG hGH p h26 hp,
    input_N_h F B H hHG hGH p h26 hp]
  noncomm_ring

-- This ten-line inverse-naturality calculation is consumed for BOTH genuine
-- global inverses. It does not define another inverse or perturbation theory.
private theorem inverse_commutes {W : Type*} [AddCommGroup W] [Module ℂ W]
    (Z A K : Module.End ℂ W) (hZA : Z * A = A * Z)
    (hKA : K * A = 1) (hAK : A * K = 1) : Z * K = K * Z := by
  calc
    Z * K = (K * A) * (Z * K) := by rw [hKA, one_mul]
    _ = K * (A * Z) * K := by noncomm_ring
    _ = K * (Z * A) * K := by rw [← hZA]
    _ = (K * Z) * (A * K) := by noncomm_ring
    _ = K * Z := by rw [hAK, mul_one]

/-- N commutes with the genuine globally locally-nilpotent inverse K. -/
theorem actual_N_K : nV * D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K c ln = D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K c ln * nV := by
  apply inverse_commutes nV (1 + (c).h * (c).delta) (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K c ln)
  · simpa only [mul_add, add_mul, mul_one, one_mul] using
      congrArg (fun a => nV + a) (input_N_hdelta F B H hHG hGH p h26 hp)
  · exact (K_inverse c ln).1
  · exact (K_inverse c ln).2

/-- The actual global J is natural too, using its own two inverse laws. -/
theorem actual_N_J : nV * D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln = D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln * nV := by
  apply inverse_commutes nV (1 + (c).delta * (c).h) (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln)
  · simpa only [mul_add, add_mul, mul_one, one_mul] using
      congrArg (fun a => nV + a) (input_N_deltah F B H hHG hGH p h26 hp)
  · exact (J_inverse c ln).1
  · exact (J_inverse c ln).2

/-- Actual corrected inclusion, with native range N and no shell premise. -/
theorem actual_I_N : (nV).comp (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln) = (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln).comp (rangeN F B p) := by
  apply LinearMap.ext
  intro u
  exact LinearMap.congr_fun (actual_N_K F B H hHG hGH p h26 hp) u.val

/-- Actual corrected projection, retaining both absolute branches. -/
theorem actual_P_N : (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln).comp nV = (rangeN F B p).comp (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln) := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change pV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln (nV v)) = nV (pV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln v))
  rw [← show nV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln v) = D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln (nV v) from
    LinearMap.congr_fun (actual_N_J F B H hHG hGH p h26 hp) v]
  exact (LinearMap.congr_fun (momentum_N_P0 F B p) (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.J c ln v)).symm

/- Native charges of the actual two occupations, computed on a full
   polynomial basis. No shell or b0 lemma participates. -/
private theorem native_groundMap : (N D).comp (groundMap F B p) = groundMap F B p := by
  classical
  apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
  intro nu
  simp only [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply,
    groundMap_monomial, N_actualBasis]
  norm_num [charge, Finset.filter_insert, Finset.filter_singleton]

private theorem native_c0_groundMap :
    (N D).comp ((ghostC D 0).comp (groundMap F B p)) =
      (2 : ℂ) • ((ghostC D 0).comp (groundMap F B p)) := by
  classical
  apply (MvPolynomial.basisMonomials (Fin t × ℕ) ℂ).ext
  intro nu
  simp only [MvPolynomial.coe_basisMonomials, LinearMap.comp_apply,
    LinearMap.smul_apply, groundMap_monomial, c0_basis, map_neg, N_actualBasis]
  norm_num [charge, Finset.filter_insert, Finset.filter_singleton]

/-- Native ghostNumber on unrestricted ACTUAL G coordinates is diag(1,2). -/
theorem native_N_G (fg : Poly t × Poly t) :
    N D (G F B p fg) = G F B p (fg.1, (2 : ℂ) • fg.2) := by
  have hf := LinearMap.congr_fun (native_groundMap F B p) fg.1
  have hg := LinearMap.congr_fun (native_c0_groundMap F B p) fg.2
  change N D (groundMap F B p fg.1 + ghostC D 0 (groundMap F B p fg.2)) = _
  rw [map_add, show N D (groundMap F B p fg.1) = groundMap F B p fg.1 from hf,
    show N D (ghostC D 0 (groundMap F B p fg.2)) =
      (2 : ℂ) • ghostC D 0 (groundMap F B p fg.2) from hg]
  change groundMap F B p fg.1 + (2 : ℂ) • ghostC D 0 (groundMap F B p fg.2) =
    groundMap F B p fg.1 + ghostC D 0 (groundMap F B p ((2 : ℂ) • fg.2))
  rw [map_smul, map_smul]

private theorem ground_N_mem (x : absoluteGround F B p) :
    N D (x : State D) ∈ absoluteGround F B p := by
  have hx := congrArg Subtype.val (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState_coordinates F B p x)
  rw [← hx]
  change N D (G F B p (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x)) ∈ _
  rw [native_N_G F B p]
  exact (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState F B p
    ((D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x).1, (2 : ℂ) • (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x).2)).property

/-- Literal restriction of native N to the actual absoluteGround submodule. -/
def groundN : Module.End ℂ (absoluteGround F B p) :=
  ((N D).comp (absoluteGround F B p).subtype).codRestrict _ (ground_N_mem F B p)

@[simp] theorem groundN_groundState (fg : Poly t × Poly t) :
    groundN F B p (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState F B p fg) =
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState F B p (fg.1, (2 : ℂ) • fg.2) := by
  apply Subtype.ext
  exact native_N_G F B p fg

private theorem rangeGround_N (u : U) :
    rangeGroundEquiv F B p (rangeN F B p u) =
      groundN F B p (rangeGroundEquiv F B p u) := by
  apply Subtype.ext
  rfl

private theorem ground_N_d :
    groundN F B p * D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH -
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH * groundN F B p = D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH := by
  apply LinearMap.ext
  intro x
  rw [← D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState_coordinates F B p x]
  simp only [LinearMap.sub_apply, Module.End.mul_apply,
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d_groundState, groundN_groundState]
  rw [← map_sub]
  apply congrArg (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState F B p)
  apply Prod.ext
  · simp
  · simp [two_smul]

private theorem ground_cycle_preserved (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH (groundN F B p x.val) = 0 := by
  have hx : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH x.val = 0 := x.property
  have eq := LinearMap.congr_fun (ground_N_d F B H hHG hGH p) x.val
  simpa only [Module.End.mul_apply, LinearMap.sub_apply, hx, map_zero,
    zero_sub, neg_eq_zero] using eq

def groundCycleN : Module.End ℂ (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH) :=
  ((groundN F B p).comp (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH).subtype).codRestrict _
    (ground_cycle_preserved F B H hHG hGH p)

private theorem ground_boundary_preserved (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH)
    (hx : x ∈ D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH) :
    groundCycleN F B H hHG hGH p x ∈ D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨groundN F B p y + y, ?_⟩
  apply Subtype.ext
  have hd : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH y = x.val := congrArg Subtype.val hy
  have eq := LinearMap.congr_fun (ground_N_d F B H hHG hGH p) y
  change groundN F B p (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH y) -
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH (groundN F B p y) = D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH y at eq
  change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH (groundN F B p y + y) = groundN F B p x.val
  rw [map_add, ← hd]
  exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp eq).symm

/-- Actual N descended through the ACTUAL compressed-differential quotient. -/
def groundQuotientN : Module.End ℂ (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cohomology F B p H hHG hGH) :=
  (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH).mapQ (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH)
    (groundCycleN F B H hHG hGH p) (by intro x hx; exact ground_boundary_preserved F B H hHG hGH p x hx)

private theorem ground_coordinates_N (x : absoluteGround F B p) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p (groundN F B p x) =
      ((D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x).1, (2 : ℂ) • (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x).2) := by
  conv_lhs => rw [← D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.groundState_coordinates F B p x]
  rw [groundN_groundState, D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates_groundState]

private theorem ground_classMap_N (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH (groundCycleN F B H hHG hGH p x) =
      ((D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH x).1,
       (2 : ℂ) • (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH x).2) := by
  apply Prod.ext <;> apply Subtype.ext
  · change (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p (groundN F B p x.val)).1 =
      (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x.val).1
    rw [ground_coordinates_N]
  · change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.pi D t p (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p (groundN F B p x.val)).2 =
      (2 : ℂ) • D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.pi D t p (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.coordinates F B p x.val).2
    rw [ground_coordinates_N, map_smul]

/-- Compatibility on the actual absolute-ground cohomology quotient. -/
theorem ground_cohomologyEquiv_N (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Cohomology F B p H hHG hGH) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.cohomologyEquiv F B p H hHG hGH (groundQuotientN F B H hHG hGH p x) =
      ((D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.cohomologyEquiv F B p H hHG hGH x).1,
       (2 : ℂ) • (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.cohomologyEquiv F B p H hHG hGH x).2) := by
  obtain ⟨z, rfl⟩ := (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH).mkQ_surjective x
  change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH (groundCycleN F B H hHG hGH p z) = _
  exact ground_classMap_N F B H hHG hGH p z

private theorem projectedCycle_N (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p) :
    projectedCycle F B H hHG hGH p hp h26 (cycleN H p x) =
      groundCycleN F B H hHG hGH p (projectedCycle F B H hHG hGH p hp h26 x) := by
  apply Subtype.ext
  change rangeGroundEquiv F B p (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln (nV x.val)) =
    groundN F B p (rangeGroundEquiv F B p (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val))
  rw [show D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln (nV x.val) = rangeN F B p (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val) from
    LinearMap.congr_fun (actual_P_N F B H hHG hGH p h26 hp) x.val]
  exact rangeGround_N F B p _

/-- The missing native full-original-Q intertwining, on the LITERAL ENTIRE
fixedMomentum quotient. All critical/chart/Gram hypotheses are explicit. -/
theorem cohomologyEquiv_quotientN
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p) :
    cohomologyEquiv F B H hHG hGH p hp h26 (quotientN H hHG hGH p h26 x) =
      ((cohomologyEquiv F B H hHG hGH p hp h26 x).1,
       (2 : ℂ) • (cohomologyEquiv F B H hHG hGH p hp h26 x).2) := by
  obtain ⟨z, rfl⟩ := D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf_surjective D H h26 hHG hGH p x
  simp only [quotientN_classOf, cohomologyEquiv_mk, projectedCycle_N]
  exact ground_cohomologyEquiv_N F B H hHG hGH p
    ((D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH).mkQ
      (projectedCycle F B H hHG hGH p hp h26 z))

/-- Actual corrected ORIGINAL-Q representatives intertwine native N already
at cycle level; the proof consumes corrected I naturality, not just quotient
injectivity. In particular this retains the second corrected zero-mode branch. -/
theorem correctedRepresentative_N (fg : energyTarget D t p × energyTarget D t p) :
    cycleN H p (correctedRepresentative F B H hHG hGH p hp h26 fg) =
      correctedRepresentative F B H hHG hGH p hp h26 (fg.1, (2 : ℂ) • fg.2) := by
  apply Subtype.ext
  change nV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
      ((rangeGroundEquiv F B p).symm
        (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH fg).val)) =
    D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
      ((rangeGroundEquiv F B p).symm
        (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH
          (fg.1, (2 : ℂ) • fg.2)).val)
  rw [show nV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln _) =
      D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
        (rangeN F B p _) from
    LinearMap.congr_fun (actual_I_N F B H hHG hGH p h26 hp) _]
  apply congrArg (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln)
  apply (rangeGroundEquiv F B p).injective
  rw [rangeGround_N, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact groundN_groundState F B p ((fg.1 : Poly t), (fg.2 : Poly t))

/-- Genuine integer grade: the eigenspace of the independently descended
native number operator on the literal original-Q quotient. -/
def grade (k : ℤ) : Submodule ℂ (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p) :=
  LinearMap.ker (quotientN H hHG hGH p h26 - (k : ℂ) • LinearMap.id)

@[simp] theorem mem_grade (k : ℤ)
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p) :
    x ∈ grade H hHG hGH p h26 k ↔ quotientN H hHG hGH p h26 x = (k : ℂ) • x := by
  change quotientN H hHG hGH p h26 x - (k : ℂ) • x = 0 ↔ _
  exact sub_eq_zero

private theorem grade_equations (k : ℤ) (x : grade H hHG hGH p h26 k) :
    (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 =
      (k : ℂ) • (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 ∧
    (2 : ℂ) • (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 =
      (k : ℂ) • (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 := by
  have hx := (mem_grade H hHG hGH p h26 k x.val).mp x.property
  have eq := congrArg (cohomologyEquiv F B H hHG hGH p hp h26) hx
  rw [cohomologyEquiv_quotientN, map_smul] at eq
  exact ⟨congrArg Prod.fst eq, congrArg Prod.snd eq⟩

private theorem grade_one_second (x : grade H hHG hGH p h26 1) :
    (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 = 0 := by
  have eq := (grade_equations F B H hHG hGH p h26 hp 1 x).2
  simp only [Int.cast_one, one_smul, two_smul] at eq
  have hz : (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 +
      (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 =
      (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 + 0 := by
    simpa only [add_zero] using eq
  exact add_left_cancel hz

private theorem grade_two_first (x : grade H hHG hGH p h26 2) :
    (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 = 0 := by
  have eq := (grade_equations F B H hHG hGH p h26 hp 2 x).1
  simp only [Int.cast_ofNat] at eq
  rw [two_smul] at eq
  have hz : (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 + 0 =
      (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 +
      (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 := by
    simpa only [add_zero] using eq
  exact (add_left_cancel hz).symm

/-- TRUE native grade-one cohomology. Its inverse is the literal class of
actual correctedRepresentative (f,0), whose native homogeneity follows from I. -/
def gradeOneEquiv : grade H hHG hGH p h26 1 ≃ₗ[ℂ] energyTarget D t p where
  toFun x := (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1
  invFun f := ⟨D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
    (correctedRepresentative F B H hHG hGH p hp h26 (f,0)), by
      apply (mem_grade H hHG hGH p h26 1 _).mpr
      rw [quotientN_classOf, correctedRepresentative_N]
      simp only [smul_zero, Int.cast_one, one_smul]⟩
  map_add' x y := congrArg Prod.fst
    (map_add (cohomologyEquiv F B H hHG hGH p hp h26) x.val y.val)
  map_smul' a x := congrArg Prod.fst
    (map_smul (cohomologyEquiv F B H hHG hGH p hp h26) a x.val)
  left_inv x := by
    apply Subtype.ext
    apply (cohomologyEquiv F B H hHG hGH p hp h26).injective
    rw [cohomologyEquiv_correctedRepresentative]
    exact Prod.ext rfl (grade_one_second F B H hHG hGH p h26 hp x).symm
  right_inv f := by
    change (cohomologyEquiv F B H hHG hGH p hp h26
      (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
        (correctedRepresentative F B H hHG hGH p hp h26 (f,0)))).1 = f
    rw [cohomologyEquiv_correctedRepresentative]

/-- TRUE native grade-two cohomology. Its inverse retains the actual second
zero-mode branch: the class of correctedRepresentative (0,g). -/
def gradeTwoEquiv : grade H hHG hGH p h26 2 ≃ₗ[ℂ] energyTarget D t p where
  toFun x := (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2
  invFun g := ⟨D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
    (correctedRepresentative F B H hHG hGH p hp h26 (0,g)), by
      apply (mem_grade H hHG hGH p h26 2 _).mpr
      rw [quotientN_classOf, correctedRepresentative_N]
      change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
          (correctedRepresentative F B H hHG hGH p hp h26 (0, (2 : ℂ) • g)) =
        (2 : ℂ) • D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
          (correctedRepresentative F B H hHG hGH p hp h26 (0,g))
      calc
        _ = D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
            (correctedRepresentative F B H hHG hGH p hp h26 ((2 : ℂ) • (0,g))) := by
          simp only [Prod.smul_mk, smul_zero]
        _ = _ := by rw [map_smul, map_smul]⟩
  map_add' x y := congrArg Prod.snd
    (map_add (cohomologyEquiv F B H hHG hGH p hp h26) x.val y.val)
  map_smul' a x := congrArg Prod.snd
    (map_smul (cohomologyEquiv F B H hHG hGH p hp h26) a x.val)
  left_inv x := by
    apply Subtype.ext
    apply (cohomologyEquiv F B H hHG hGH p hp h26).injective
    rw [cohomologyEquiv_correctedRepresentative]
    exact Prod.ext (grade_two_first F B H hHG hGH p h26 hp x).symm rfl
  right_inv g := by
    change (cohomologyEquiv F B H hHG hGH p hp h26
      (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
        (correctedRepresentative F B H hHG hGH p hp h26 (0,g)))).2 = g
    rw [cohomologyEquiv_correctedRepresentative]

include F B hp in
/-- Native homogeneous classes vanish at EVERY other integer grade. -/
theorem off_grade_eq_zero (k : ℤ) (hk1 : k ≠ 1) (hk2 : k ≠ 2)
    (x : grade H hHG hGH p h26 k) : x.val = 0 := by
  have eq := grade_equations F B H hHG hGH p h26 hp k x
  have hk1c : (1 : ℂ) - (k : ℂ) ≠ 0 := by
    intro h
    have hc : (k : ℂ) = (1 : ℂ) := (sub_eq_zero.mp h).symm
    have hi : k = (1 : ℤ) := by exact_mod_cast hc
    exact hk1 hi
  have hk2c : (2 : ℂ) - (k : ℂ) ≠ 0 := by
    intro h
    have hc : (k : ℂ) = (2 : ℂ) := (sub_eq_zero.mp h).symm
    have hi : k = (2 : ℤ) := by exact_mod_cast hc
    exact hk2 hi
  have hf : ((1 : ℂ) - (k : ℂ)) •
      (cohomologyEquiv F B H hHG hGH p hp h26 x.val).1 = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.mpr eq.1
  have hg : ((2 : ℂ) - (k : ℂ)) •
      (cohomologyEquiv F B H hHG hGH p hp h26 x.val).2 = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr eq.2
  apply (cohomologyEquiv F B H hHG hGH p hp h26).injective
  rw [(cohomologyEquiv F B H hHG hGH p hp h26).map_zero]
  exact Prod.ext ((smul_eq_zero.mp hf).resolve_left hk1c)
    ((smul_eq_zero.mp hg).resolve_left hk2c)

include F B hp in
/-- Vanishing as equality of the genuine native eigenspace with zero. -/
theorem off_grade_eq_bot (k : ℤ) (hk1 : k ≠ 1) (hk2 : k ≠ 2) :
    grade H hHG hGH p h26 k = ⊥ := by
  ext x
  constructor
  · intro hx
    have hz := off_grade_eq_zero F B H hHG hGH p h26 hp k hk1 hk2 ⟨x,hx⟩
    simpa only [Submodule.mem_bot] using hz
  · intro hx
    have hz : x = 0 := by simpa only [Submodule.mem_bot] using hx
    rw [hz]
    exact (grade H hHG hGH p h26 k).zero_mem

include F B hHG hGH h26 hp in
/-- An actual homogeneous original-Q cycle at any other integer grade has
an incoming ORIGINAL-Q primitive in ENTIRE fixedMomentum. No primitive is
required to satisfy a shell or b0 condition. -/
theorem off_grade_cycle_exact (k : ℤ) (hk1 : k ≠ 1) (hk2 : k ≠ 2)
    (x : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p)
    (hx : nV x.val = (k : ℂ) • x.val) :
    ∃ y : V, qV y = x.val := by
  apply (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf_eq_zero D H h26 hHG hGH p x).mp
  apply off_grade_eq_zero F B H hHG hGH p h26 hp k hk1 hk2
    (x := ⟨D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p x, ?_⟩)
  apply (mem_grade H hHG hGH p h26 k _).mpr
  rw [quotientN_classOf]
  have hc : cycleN H p x = (k : ℂ) • x := Subtype.ext hx
  rw [hc, map_smul]

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFullGhostNumberCohomology
