import D5.S3.VertexAlgebra.Lattice.LatticeBRSTFiniteTransfer
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTQuartetTransferTail
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTQuartetGroundCompression
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTAbsoluteGroundCohomology
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTChargeCohomology
import D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbationCohomology
import Batteries.Tactic.OpenPrivate

/-!
Full original-Q absolute cohomology in one nonzero light-cone chart.

The carrier is literally fixedMomentum D p, with every energy and both ghost
zero modes. The cutoff is computed from the finite support of each original
state, never chosen for the whole carrier. The transferred differential is
P0*c0*L0*P0; it is not set to zero. Only after computing its cohomology does an
energy-one target appear. Representatives are corrected by the actual HPL I.

Attribution: original BRST (Becchi--Rouet--Stora--Tyutin), Kato--Ogawa and
Lian--Zuckerman; algebraic HPL of Gugenheim--Lambe--Stasheff. The lattice,
current and occupation suppliers retain their Bakalov--Kac, Scott Carnahan
and Kalle Kytölä attribution. The fixed-sector Input proof below adapts the
supplied LatticeBRSTFiniteTransfer.finiteInput, rather than reimplementing HPL.
The inverse and cohomology are the repaired locally nilpotent suppliers'.
The generic quotient descent is reused through Batteries.OpenPrivate.
Mathlib quotient, basis and finite-support machinery (Johannes Hölzl,
Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Kenny Lau and Joël Riou),
and Batteries.OpenPrivate (Mario Carneiro; Microsoft Corporation), retain
Apache 2.0 notices. Imported supplier license notices remain in their files.

UNPARSED SOURCE CANDIDATE. No native, kernel or official acceptance. The tail
API is the frozen pre-native 8afed3ae candidate; its final native replacement
must be reconciled after its owner terminates. No positivity, Lorentzian
no-ghost, sewing, interacting string, spacetime or AdS/CFT completion claim.
A fixed frame with pPlus p = 0 is deliberately outside this chart theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

open private cycleMap cohomologyMap cohomologyMap_mk
  from D5.S3.HomologicalAlgebra.FinitePerturbationCohomology

namespace D5.S3.VertexAlgebra.LatticeBRSTFullNonzeroAbsoluteCohomology

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeLightConeCoordinates
open LatticeLightConeCoordinates.NullFrame LatticeQuartetContraction
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open LatticeBRSTPerturbationFiltration
open LatticeRelativeMassShell (fixedMomentum totalCharge_mem_fixedMomentum)
open LatticeMatterGhostCoupling (ghostC)
open LatticeRelativeBRSTCohomology.Ground (energyTarget)
open D5.S3.HomologicalAlgebra
open D5.S3.HomologicalAlgebra.FiniteSupportEndomorphismCalculus


variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (p : Charge D)

private theorem fixedMomentum_iff_project (v : State D) :
    v ∈ fixedMomentum D p ↔ chargeProject p v = v := by
  constructor
  · exact LatticeBRSTChargeCohomology.chargeProject_fixed D p v
  · intro hv
    apply (LatticeRelativeMassShell.mem_fixedMomentum_iff D p v).mpr
    intro i hi
    have hc := congrArg (fun w => LatticeRelativeMassShell.coeff D w i) hv
    rw [LatticeBRSTChargeCohomology.chargeProject_coeff, if_neg hi] at hc
    exact hc.symm

private theorem fixedMomentum_iff_support (v : State D) :
    v ∈ fixedMomentum D p ↔ HasCharge F B p v := by
  classical
  rw [fixedMomentum_iff_project]
  constructor
  · intro hv i hi
    by_contra hn
    have hc := congrArg (fun w => (actualBasis F B).repr w i) hv
    rw [chargeProject_diagonal F B, diagonal_coefficient, if_neg hn, zero_mul] at hc
    exact hi hc.symm
  · intro hv
    apply (actualBasis F B).repr.injective
    ext i
    rw [chargeProject_diagonal F B, diagonal_coefficient]
    by_cases hi : i.1.1 = p
    · simp [hi]
    · have hz : (actualBasis F B).repr v i = 0 := by
        by_contra hn
        exact hi (hv i hn)
      simp [hi, hz]

include B H in
private theorem d0_mem (v : State D) (hv : v ∈ fixedMomentum D p) :
    d0 F p v ∈ fixedMomentum D p := by
  apply (fixedMomentum_iff_support F B p _).mpr
  exact (original_operators_preserve_charge F B H p v
    ((fixedMomentum_iff_support F B p v).mp hv)).2.1

include H in
private theorem h_mem (v : State D) (hv : v ∈ fixedMomentum D p) :
    h F B p v ∈ fixedMomentum D p := by
  apply (fixedMomentum_iff_support F B p _).mpr
  exact (original_operators_preserve_charge F B H p v
    ((fixedMomentum_iff_support F B p v).mp hv)).2.2

private theorem P0_mem (v : State D) (hv : v ∈ fixedMomentum D p) :
    P0 F B v ∈ fixedMomentum D p := by
  apply (fixedMomentum_iff_support F B p _).mpr
  intro i hi
  apply (fixedMomentum_iff_support F B p v).mp hv i
  intro hz
  apply hi
  simp only [P0, projectZero, diagonal_coefficient, hz, mul_zero]

/-- Restrictions to the ENTIRE original fixedMomentum, with no energy input. -/
def momentumD0 : Module.End ℂ (fixedMomentum D p) :=
  (d0 F p).restrict (d0_mem F B H p)
def momentumH : Module.End ℂ (fixedMomentum D p) :=
  (h F B p).restrict (h_mem F B H p)
def momentumP0 : Module.End ℂ (fixedMomentum D p) :=
  (P0 F B).restrict (P0_mem F B p)

local notation "V" => fixedMomentum D p
local notation "qV" => LatticeBRSTChargeCohomology.sectorQ D H p
local notation "dV" => momentumD0 F B H p
local notation "hV" => momentumH F B H p
local notation "pV" => momentumP0 F B p

@[simp] theorem momentumD0_coe (v : V) : (dV v : State D) = d0 F p v := rfl
@[simp] theorem momentumH_coe (v : V) : (hV v : State D) = h F B p v := rfl
@[simp] theorem momentumP0_coe (v : V) : (pV v : State D) = P0 F B v := rfl

private theorem momentumP0_square : pV * pV = pV := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simpa only [Module.End.mul_apply, momentumP0_coe] using
    LinearMap.congr_fun (spectral_projection_inverse F B).2.2.1 v.val

abbrev quartetGround := LinearMap.range pV
local notation "U" => quartetGround F B p

private theorem ground_fixed (u : U) : pV (u : V) = (u : V) := by
  obtain ⟨v, hv⟩ := u.property
  rw [← hv]
  exact LinearMap.congr_fun (momentumP0_square F B p) v

/-- The fixed-sector supplier Input adapted to literal fixedMomentum. Only the
original quartet identities and actual critical totalCharge square fill fields. -/
def fullInput (hp : F.pPlus p ≠ 0) (h26 : D.rank = 26) :
    D5.S3.HomologicalAlgebra.FinitePerturbation.Input (R := ℂ) («U» := U) («V» := V) where
  d0 := dV
  h := hV
  delta := qV - dV
  i := (LinearMap.range pV).subtype
  p := (pV).rangeRestrict
  d0_sq := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simpa only [Module.End.mul_apply, momentumD0_coe, LinearMap.zero_apply,
      Submodule.coe_zero] using LinearMap.congr_fun (d0_square F p) v.val
  pi := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    exact ground_fixed F B p u
  di := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    obtain ⟨v, hv⟩ := u.property
    change d0 F p (u : State D) = 0
    rw [← hv]
    exact LinearMap.congr_fun (d0_mul_P0 F B p) v.val
  pd := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.congr_fun (P0_mul_d0 F B p) v.val
  contraction := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (homotopy_contraction F B p hp) v.val
  hh := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simpa only [Module.End.mul_apply, momentumH_coe, LinearMap.zero_apply,
      Submodule.coe_zero] using LinearMap.congr_fun (homotopy_square F B p) v.val
  hi := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    obtain ⟨v, hv⟩ := u.property
    change h F B p (u : State D) = 0
    rw [← hv]
    exact LinearMap.congr_fun (h_mul_P0 F B p) v.val
  ph := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    exact LinearMap.congr_fun (P0_mul_h F B p) v.val
  perturbed_sq := by
    have qs : LatticeBRST.totalCharge D H * LatticeBRST.totalCharge D H = 0 := by
      have eq := LatticeBRST.total_square_anomaly D H hHG hGH
      simpa only [h26, Nat.cast_ofNat, sub_self, zero_div, zero_smul, pow_two] using eq
    have eq : dV + (qV - dV) = qV := by abel
    rw [eq]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun qs v.val

set_option backward.isDefEq.respectTransparency true

local instance : AddCommGroup (Carrier D) := inferInstance
local instance : AddCommGroup (State D) := inferInstance
local instance : AddCommGroup V := inferInstance
local instance : AddCommGroup U := inferInstance
local instance : AddCommGroup (LatticeBRSTAbsoluteQuartetGround.absoluteGround F B p) :=
  inferInstance
local instance : AddCommGroup (LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH) :=
  inferInstance
local instance : AddCommGroup (LatticeBRSTChargeCohomology.sectorCycles D H p) := inferInstance

/-- A power that kills one vector kills it at every greater exponent. -/
private theorem correction_power_mono (v : State D) (a b : ℕ)
    (hab : a ≤ b)
    (ha : ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^ a) v = 0) :
    ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^ b) v = 0 := by
  let A := h F B p * (LatticeBRST.totalCharge D H - d0 F p)
  change (A ^ b) v = 0
  calc
    (A ^ b) v = (A ^ ((b - a) + a)) v := by rw [Nat.sub_add_cancel hab]
    _ = 0 := by rw [pow_add, Module.End.mul_apply, ha, map_zero]

/-- This cutoff belongs to v, not to the full module. sup of empty support is
zero, so adding one also handles v=0 and all empty transverse-rank cases. -/
def vectorCutoff (v : State D) : ℕ :=
  ((actualBasis F B).repr v).support.sup
    (fun i => 2 * (indexLevel i).toNat + 2) + 1

theorem vectorCutoff_pos (v : State D) : 1 ≤ vectorCutoff F B v := by
  unfold vectorCutoff
  omega

include hHG hGH in
/-- Pointwise termination on every original fixed-momentum finite state.
Every basis summand uses its own true energy sector. No decomposition or
local nilpotence is an input premise. -/
theorem original_pointwise_termination (v : State D) (hv : v ∈ fixedMomentum D p) :
    ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^
      vectorCutoff F B v) v = 0 := by
  classical
  let A := h F B p * (LatticeBRST.totalCharge D H - d0 F p)
  have kill (i : StateIndex D t) (hi : i ∈ ((actualBasis F B).repr v).support) :
      (A ^ vectorCutoff F B v) (actualBasis F B i) = 0 := by
    have hc : i.1.1 = p := (fixedMomentum_iff_support F B p v).mp hv i
      (Finsupp.mem_support_iff.mp hi)
    have hs := basis_mem_fixedSector F B H hHG hGH i
    rw [hc] at hs
    have hk := LatticeBRSTFiniteTransfer.actual_normalized_perturbation_termination
      F B H hHG hGH p (indexLevel i) (actualBasis F B i) hs.1 hs.2
    have hle : 2 * (indexLevel i).toNat + 2 ≤ vectorCutoff F B v := by
      have hm := Finset.le_sup (f := fun j : StateIndex D t =>
        2 * (indexLevel j).toNat + 2) hi
      unfold vectorCutoff
      omega
    exact correction_power_mono F B H p _ _ _ hle hk
  change (A ^ vectorCutoff F B v) v = 0
  calc
    (A ^ vectorCutoff F B v) v =
        (A ^ vectorCutoff F B v)
          (∑ i ∈ ((actualBasis F B).repr v).support,
            (actualBasis F B).repr v i • actualBasis F B i) :=
      congrArg (fun w : State D => (A ^ vectorCutoff F B v) w)
        (basis_expand (actualBasis F B) v).symm
    _ = 0 := by
      simp only [map_sum, map_smul]
      apply Finset.sum_eq_zero
      intro i hi
      rw [kill i hi, smul_zero]

theorem correction_power_coe (n : ℕ) (v : V) :
    (((hV * (qV - dV)) ^ n) v : State D) =
      ((h F B p * (LatticeBRST.totalCharge D H - d0 F p)) ^ n) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ]
    change (((hV * (qV - dV)) ^ n) ((hV * (qV - dV)) v) : State D) = _
    rw [ih]
    rfl

private theorem inversePolynomial_coe (n : ℕ) (v : V) :
    (D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial (hV * (qV - dV)) n v : State D) =
      D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial
        (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) n v := by
  have hpowers (j : ℕ) (w : V) :
      (((-(hV * (qV - dV))) ^ j) w : State D) =
        ((-(h F B p * (LatticeBRST.totalCharge D H - d0 F p))) ^ j) w := by
    induction j generalizing w with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ, pow_succ]
      change (((-(hV * (qV - dV))) ^ j) ((-(hV * (qV - dV))) w) : State D) = _
      rw [ih]
      rfl
  simp only [D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial, LinearMap.sum_apply, Submodule.coe_sum, hpowers]

variable (hp : F.pPlus p ≠ 0) (h26 : D.rank = 26)
local notation "c" => fullInput F B H hHG hGH p hp h26

@[simp] theorem fullInput_D : (c).D = qV := by
  change dV + (qV - dV) = qV
  abel

/-- Genuine local nilpotence of the restricted endomorphism, by coercion of
powers from the entire fixedMomentum. No uniform entire-carrier cutoff. -/
theorem actual_local_nilpotence (v : V) :
    ∃ n : ℕ, (((c).h * (c).delta) ^ n) v = 0 := by
  refine ⟨vectorCutoff F B v.val, ?_⟩
  apply Subtype.ext
  rw [show (c).h * (c).delta = hV * (qV - dV) from rfl, correction_power_coe]
  exact original_pointwise_termination F B H hHG hGH p v.val v.property

local notation "ln" => actual_local_nilpotence F B H hHG hGH p hp h26
local notation "dU" => D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.transferred c ln

local instance : AddCommGroup (LinearMap.ker ((c).D)) := inferInstance
local instance : AddCommGroup (LinearMap.ker dU) := inferInstance

/-- Reconcile the literal range of restricted P0 with the full absoluteGround.
No b0 condition, relative carrier or energy shell is present on either side. -/
def rangeToGround : U →ₗ[ℂ] LatticeBRSTAbsoluteQuartetGround.absoluteGround F B p where
  toFun u := ⟨(u.1 : State D),
    ⟨congrArg Subtype.val (ground_fixed F B p u),
      (fixedMomentum_iff_project p _).mp u.1.property⟩⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def groundToRange : LatticeBRSTAbsoluteQuartetGround.absoluteGround F B p →ₗ[ℂ] U where
  toFun x :=
    let v : V := ⟨x.val, (fixedMomentum_iff_project p x.val).mpr x.property.2⟩
    ⟨v, ⟨v, Subtype.ext x.property.1⟩⟩
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; rfl

def rangeGroundEquiv : U ≃ₗ[ℂ] LatticeBRSTAbsoluteQuartetGround.absoluteGround F B p where
  toFun := rangeToGround F B p
  invFun := groundToRange F B p
  map_add' := (rangeToGround F B p).map_add
  map_smul' := (rangeToGround F B p).map_smul
  left_inv u := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

/-- Actual transferred endomorphism: first replace K on THIS input by its
finite polynomial, then consume the immutable full original tail, then the
repaired original-Q compression. N is positive by vectorCutoff_pos. -/
theorem actual_transferred_compression (u : U) :
    ((dU u : V) : State D) =
      (P0 F B * ghostC D 0 * LatticeRelativeMassShell.totalL0 D H * P0 F B)
        (u.1 : State D) := by
  let v : V := (c).i u
  let N := vectorCutoff F B v.val
  have hvnil : (((c).h * (c).delta) ^ N) v = 0 := by
    apply Subtype.ext
    rw [show (c).h * (c).delta = hV * (qV - dV) from rfl, correction_power_coe]
    exact original_pointwise_termination F B H hHG hGH p v.val v.property
  have hk := D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K_apply_eq_inversePolynomial c ln v N hvnil
  have hI : ((D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln u : V) : State D) =
      D5.S3.HomologicalAlgebra.FinitePerturbation.inversePolynomial
        (h F B p * (LatticeBRST.totalCharge D H - d0 F p)) N (u.1 : State D) := by
    change (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.K c ln v : State D) = _
    rw [hk]
    exact inversePolynomial_coe F B H p N v
  have hP : P0 F B (u.1 : State D) = (u.1 : State D) :=
    congrArg Subtype.val (ground_fixed F B p u)
  have hcharge : chargeProject p (u.1 : State D) = (u.1 : State D) :=
    (fixedMomentum_iff_project p _).mp u.1.property
  have tail := LinearMap.congr_fun
    (LatticeBRSTQuartetTransferTail.full_original_finite_transfer_compression
      F B H hHG hGH p N (vectorCutoff_pos F B v.val)) (u.1 : State D)
  simp only [Module.End.mul_apply] at tail
  rw [hcharge, hP] at tail
  have hd0 : d0 F p (u.1 : State D) = 0 := by
    rw [← hP]
    exact LinearMap.congr_fun (d0_mul_P0 F B p) (u.1 : State D)
  have compress := LinearMap.congr_fun
    (LatticeBRSTQuartetGroundCompression.original_Q_ground_compression
      F B H hHG hGH) (u.1 : State D)
  change P0 F B ((LatticeBRST.totalCharge D H - d0 F p)
      ((D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln u : V) : State D)) = _
  rw [hI, tail]
  simp only [LinearMap.sub_apply, hd0, sub_zero]
  simpa only [Module.End.mul_apply, hP] using compress

/-- The transport retains the actual nonzero energy differential on full G
coordinates. In particular it does NOT replace dU by zero on full ground. -/
theorem actual_ground_chain :
    (rangeGroundEquiv F B p).toLinearMap.comp dU =
      (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH).comp (rangeGroundEquiv F B p).toLinearMap := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact actual_transferred_compression F B H hHG hGH p hp h26 u


/-- On every unrestricted G pair the actual transferred operator is
(f,g) ↦ (0,E f). The second ghost-zero-mode coordinate remains unrestricted. -/
theorem actual_transferred_groundState
    (fg : LatticeBRSTAbsoluteQuartetGround.Poly t × LatticeBRSTAbsoluteQuartetGround.Poly t) :
    dU ((rangeGroundEquiv F B p).symm
        (LatticeBRSTAbsoluteGroundCohomology.groundState F B p fg)) =
      (rangeGroundEquiv F B p).symm
        (LatticeBRSTAbsoluteGroundCohomology.groundState F B p
          (0,LatticeBRSTAbsoluteQuartetGround.E p fg.1)) := by
  apply (rangeGroundEquiv F B p).injective
  have eq := LinearMap.congr_fun
    (actual_ground_chain F B H hHG hGH p hp h26)
    ((rangeGroundEquiv F B p).symm
      (LatticeBRSTAbsoluteGroundCohomology.groundState F B p fg))
  change rangeGroundEquiv F B p
      (dU ((rangeGroundEquiv F B p).symm
        (LatticeBRSTAbsoluteGroundCohomology.groundState F B p fg))) =
    LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH
      (rangeGroundEquiv F B p ((rangeGroundEquiv F B p).symm
        (LatticeBRSTAbsoluteGroundCohomology.groundState F B p fg))) at eq
  rw [LinearEquiv.apply_symm_apply,
    LatticeBRSTAbsoluteGroundCohomology.d_groundState] at eq
  exact eq

private theorem inverse_ground_chain :
    (rangeGroundEquiv F B p).symm.toLinearMap.comp
        (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH) =
      (dU).comp (rangeGroundEquiv F B p).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  apply (rangeGroundEquiv F B p).injective
  have eq := LinearMap.congr_fun
    (actual_ground_chain F B H hHG hGH p hp h26)
    ((rangeGroundEquiv F B p).symm x)
  change rangeGroundEquiv F B p (dU ((rangeGroundEquiv F B p).symm x)) =
    LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH
      (rangeGroundEquiv F B p ((rangeGroundEquiv F B p).symm x)) at eq
  change rangeGroundEquiv F B p ((rangeGroundEquiv F B p).symm
      (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH x)) =
    rangeGroundEquiv F B p (dU ((rangeGroundEquiv F B p).symm x))
  rw [LinearEquiv.apply_symm_apply] at eq ⊢
  exact eq.symm

/-- Concrete kernel map from the literal sectorQ kernel to the HPL D kernel. -/
def literalCycleToInput : LatticeBRSTChargeCohomology.sectorCycles D H p →ₗ[ℂ]
    LinearMap.ker (c).D where
  toFun x := ⟨x.val, by rw [fullInput_D]; exact x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def inputCycleToLiteral : LinearMap.ker (c).D →ₗ[ℂ]
    LatticeBRSTChargeCohomology.sectorCycles D H p where
  toFun x := ⟨x.val, by simpa only [fullInput_D] using x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

private theorem literal_boundary_to_input
    (x : LatticeBRSTChargeCohomology.sectorCycles D H p)
    (hx : x ∈ LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p) :
    literalCycleToInput F B H hHG hGH p hp h26 x ∈
      D5.S3.HomologicalAlgebra.FinitePerturbation.Boundaries (c).D (c).perturbed_sq := by
  obtain ⟨y, hy⟩ :=
    (LatticeBRSTChargeCohomology.mem_sectorBoundaries D H h26 hHG hGH p x).mp hx
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change (c).D y = x.val
  rw [fullInput_D]
  exact hy

private theorem input_boundary_to_literal (x : LinearMap.ker (c).D)
    (hx : x ∈ D5.S3.HomologicalAlgebra.FinitePerturbation.Boundaries (c).D (c).perturbed_sq) :
    inputCycleToLiteral F B H hHG hGH p hp h26 x ∈
      LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p := by
  obtain ⟨y, hy⟩ := hx
  apply (LatticeBRSTChargeCohomology.mem_sectorBoundaries D H h26 hHG hGH p _).mpr
  refine ⟨y, ?_⟩
  have eq := congrArg Subtype.val hy
  change (c).D y = x.val at eq
  change qV y = x.val
  simpa only [fullInput_D] using eq

/-- Identification with the LITERAL supplied SectorCohomology, including its
fixedMomentum boundary witnesses and parameter order D H h26 hHG hGH p.
Only Mathlib mapQ is used; there is no replacement quotient convention. -/
def literalQuotientEquiv :
    LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p ≃ₗ[ℂ]
      D5.S3.HomologicalAlgebra.FinitePerturbation.Cohomology (c).D (c).perturbed_sq := by
  let fwd := (LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p).mapQ
    (D5.S3.HomologicalAlgebra.FinitePerturbation.Boundaries (c).D (c).perturbed_sq)
    (literalCycleToInput F B H hHG hGH p hp h26)
    (by intro x hx; exact literal_boundary_to_input F B H hHG hGH p hp h26 x hx)
  let bwd := (D5.S3.HomologicalAlgebra.FinitePerturbation.Boundaries (c).D (c).perturbed_sq).mapQ
    (LatticeBRSTChargeCohomology.sectorBoundaries D H h26 hHG hGH p)
    (inputCycleToLiteral F B H hHG hGH p hp h26)
    (by intro x hx; exact input_boundary_to_literal F B H hHG hGH p hp h26 x hx)
  refine { fwd with toFun := fwd, invFun := bwd, left_inv := ?_, right_inv := ?_ }
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    rfl
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    rfl

@[simp] theorem literalQuotientEquiv_mk
    (x : LatticeBRSTChargeCohomology.sectorCycles D H p) :
    literalQuotientEquiv F B H hHG hGH p hp h26
        (LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p x) =
      Submodule.Quotient.mk (literalCycleToInput F B H hHG hGH p hp h26 x) := rfl

/-- Transport the actual transferred quotient through the actual range/ground
linear equivalence. The existing generic cohomologyMap handles boundaries. -/
def groundQuotientEquiv :
    D5.S3.HomologicalAlgebra.FinitePerturbation.Cohomology dU
        (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation c ln).1
      ≃ₗ[ℂ] LatticeBRSTAbsoluteGroundCohomology.Cohomology F B p H hHG hGH := by
  let dsq :=
    (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation c ln).1
  let gsq := LatticeBRSTAbsoluteGroundCohomology.d_square F B p H hHG hGH
  let fwd := cohomologyMap dU (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH)
    dsq gsq (rangeGroundEquiv F B p).toLinearMap
    (actual_ground_chain F B H hHG hGH p hp h26)
  let bwd := cohomologyMap (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH) dU
    gsq dsq (rangeGroundEquiv F B p).symm.toLinearMap
    (inverse_ground_chain F B H hHG hGH p hp h26)
  refine { fwd with toFun := fwd, invFun := bwd, left_inv := ?_, right_inv := ?_ }
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    change Submodule.Quotient.mk
      (cycleMap (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH) dU
        (rangeGroundEquiv F B p).symm.toLinearMap
        (inverse_ground_chain F B H hHG hGH p hp h26)
        (cycleMap dU (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH)
          (rangeGroundEquiv F B p).toLinearMap
          (actual_ground_chain F B H hHG hGH p hp h26) x)) = Submodule.Quotient.mk x
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact (rangeGroundEquiv F B p).symm_apply_apply x.val
  · intro z
    refine Submodule.Quotient.induction_on _ z (fun x => ?_)
    change Submodule.Quotient.mk
      (cycleMap dU (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH)
        (rangeGroundEquiv F B p).toLinearMap
        (actual_ground_chain F B H hHG hGH p hp h26)
        (cycleMap (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH) dU
          (rangeGroundEquiv F B p).symm.toLinearMap
          (inverse_ground_chain F B H hHG hGH p hp h26) x)) = Submodule.Quotient.mk x
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact (rangeGroundEquiv F B p).apply_symm_apply x.val

@[simp] theorem groundQuotientEquiv_mk (u : LinearMap.ker dU) :
    groundQuotientEquiv F B H hHG hGH p hp h26 (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk
        (cycleMap dU (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH)
          (rangeGroundEquiv F B p).toLinearMap
          (actual_ground_chain F B H hHG hGH p hp h26) u) := rfl

/-- ENTIRE original fixed-momentum, original totalCharge cohomology in the
pPlus chart. No termination, shell, b0, collapse or target equivalence is assumed.
Both original zero modes survive; the middle differential is actual energy. -/
def cohomologyEquiv :
    LatticeBRSTChargeCohomology.SectorCohomology D H h26 hHG hGH p ≃ₗ[ℂ]
      (energyTarget D t p × energyTarget D t p) :=
  (((literalQuotientEquiv F B H hHG hGH p hp h26).trans
    (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cohomologyEquiv c ln)).trans
      (groundQuotientEquiv F B H hHG hGH p hp h26)).trans
        (LatticeBRSTAbsoluteGroundCohomology.cohomologyEquiv F B p H hHG hGH)

/-- Actual P followed by the actual range/ground equivalence on source cycles. -/
def projectedCycle : LatticeBRSTChargeCohomology.sectorCycles D H p →ₗ[ℂ]
    LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH :=
  (cycleMap dU (LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH)
    (rangeGroundEquiv F B p).toLinearMap
    (actual_ground_chain F B H hHG hGH p hp h26)).comp
      ((cycleMap (c).D dU
        (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln)
        (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation c ln).2.2.1).comp
          (literalCycleToInput F B H hHG hGH p hp h26))

/-- Forward readout is (f, pi g) for the G coordinates of the ACTUAL P x. -/
@[simp] theorem cohomologyEquiv_mk
    (x : LatticeBRSTChargeCohomology.sectorCycles D H p) :
    cohomologyEquiv F B H hHG hGH p hp h26
        (LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p x) =
      LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH
        (projectedCycle F B H hHG hGH p hp h26 x) := by
  unfold cohomologyEquiv
  simp only [LinearEquiv.trans_apply, literalQuotientEquiv_mk]
  rw [D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cohomologyEquiv_mk c ln
    (literalCycleToInput F B H hHG hGH p hp h26 x).val
    (literalCycleToInput F B H hHG hGH p hp h26 x).property]
  rw [groundQuotientEquiv_mk]
  change LatticeBRSTAbsoluteGroundCohomology.cohomologyEquiv F B p H hHG hGH
      ((LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH).mkQ
        (projectedCycle F B H hHG hGH p hp h26 x)) = _
  exact LatticeBRSTAbsoluteGroundCohomology.cohomologyEquiv_mk F B p H hHG hGH _

/-- Corrected original-Q cycles: ACTUAL I applied to the full G pair through
its literal range-P0 identification. Uncorrected G is never declared Q-closed. -/
def correctedRepresentative : (energyTarget D t p × energyTarget D t p) →ₗ[ℂ]
    LatticeBRSTChargeCohomology.sectorCycles D H p :=
  ((D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln).comp
    ((rangeGroundEquiv F B p).symm.toLinearMap.comp
      ((LatticeBRSTAbsoluteGroundCohomology.Cycles F B p H hHG hGH).subtype.comp
        (LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH)))).codRestrict _ (by
    intro fg
    let x := LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH fg
    have hg : LatticeBRSTAbsoluteGroundCohomology.groundState F B p
        (0,LatticeBRSTAbsoluteQuartetGround.E p
          (fg.1 : LatticeBRSTAbsoluteQuartetGround.Poly t)) = 0 := by
      rw [← LatticeBRSTAbsoluteGroundCohomology.d_groundState F B p H hHG hGH
        ((fg.1 : LatticeBRSTAbsoluteQuartetGround.Poly t),
         (fg.2 : LatticeBRSTAbsoluteQuartetGround.Poly t))]
      exact x.property
    have hu : dU ((rangeGroundEquiv F B p).symm x.val) = 0 := by
      change dU ((rangeGroundEquiv F B p).symm
        (LatticeBRSTAbsoluteGroundCohomology.groundState F B p
          ((fg.1 : LatticeBRSTAbsoluteQuartetGround.Poly t),
           (fg.2 : LatticeBRSTAbsoluteQuartetGround.Poly t)))) = 0
      rw [actual_transferred_groundState F B H hHG hGH p hp h26, hg]
      exact (rangeGroundEquiv F B p).symm.map_zero
    have eq := LinearMap.congr_fun
      (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation c ln).2.1
      ((rangeGroundEquiv F B p).symm x.val)
    change qV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
      ((rangeGroundEquiv F B p).symm x.val)) = 0
    simpa only [LinearMap.comp_apply, fullInput_D, hu, map_zero] using eq)

/-- Literal corrected state formula; groundState has ambient value G(f,g). -/
theorem correctedRepresentative_state (fg : energyTarget D t p × energyTarget D t p) :
    ((correctedRepresentative F B H hHG hGH p hp h26 fg).val : State D) =
      ((D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
        (groundToRange F B p
          (LatticeBRSTAbsoluteGroundCohomology.groundState F B p
            ((fg.1 : LatticeBRSTAbsoluteQuartetGround.Poly t),
             (fg.2 : LatticeBRSTAbsoluteQuartetGround.Poly t)))) : V) : State D) := rfl

private theorem projected_corrected (fg : energyTarget D t p × energyTarget D t p) :
    projectedCycle F B H hHG hGH p hp h26
        (correctedRepresentative F B H hHG hGH p hp h26 fg) =
      LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH fg := by
  let u := (rangeGroundEquiv F B p).symm
    (LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH fg).val
  have ret : D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln
      (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln u) = u :=
    LinearMap.congr_fun
      (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation c ln).2.2.2.1 u
  apply Subtype.ext
  change rangeGroundEquiv F B p
    (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln
      (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln u)) = _
  exact (congrArg (rangeGroundEquiv F B p) ret).trans
    ((rangeGroundEquiv F B p).apply_symm_apply _)

/-- Readout and uniqueness of corrected original-Q representatives. -/
@[simp] theorem cohomologyEquiv_correctedRepresentative
    (fg : energyTarget D t p × energyTarget D t p) :
    cohomologyEquiv F B H hHG hGH p hp h26
      (LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
        (correctedRepresentative F B H hHG hGH p hp h26 fg)) = fg := by
  rw [cohomologyEquiv_mk, projected_corrected,
    LatticeBRSTAbsoluteGroundCohomology.classMap_representative]

/-- Inverse representative readout for the literal original-Q quotient. -/
theorem cohomologyEquiv_symm (fg : energyTarget D t p × energyTarget D t p) :
    (cohomologyEquiv F B H hHG hGH p hp h26).symm fg =
      LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
        (correctedRepresentative F B H hHG hGH p hp h26 fg) := by
  apply (cohomologyEquiv F B H hHG hGH p hp h26).injective
  rw [LinearEquiv.apply_symm_apply, cohomologyEquiv_correctedRepresentative]

/-- Exact kernel/boundary test for an original cycle, with primitives still in
ENTIRE fixedMomentum and the two actual projected G coordinates. -/
theorem original_boundary_iff (x : LatticeBRSTChargeCohomology.sectorCycles D H p) :
    (∃ y : V, qV y = x.val) ↔
      LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH
        (projectedCycle F B H hHG hGH p hp h26 x) = 0 := by
  rw [← LatticeBRSTChargeCohomology.sectorClassOf_eq_zero D H h26 hHG hGH p x,
    ← cohomologyEquiv_mk F B H hHG hGH p hp h26 x]
  constructor
  · intro hx
    rw [hx]
    exact (cohomologyEquiv F B H hHG hGH p hp h26).map_zero
  · intro hx
    apply (cohomologyEquiv F B H hHG hGH p hp h26).injective
    exact hx.trans (cohomologyEquiv F B H hHG hGH p hp h26).map_zero.symm

/-- Every original cycle differs from ONE corrected G pair by a genuine
original Q boundary. The witness constructed here is H x + I(e.symm y), where
y is the actual compressed-ground boundary primitive. No formal exactness or
uncorrected ground representative substitutes for that original primitive. -/
theorem canonical_original_representative
    (x : LatticeBRSTChargeCohomology.sectorCycles D H p) :
    ∃! fg : energyTarget D t p × energyTarget D t p,
      ∃ y : V,
        x.val - (correctedRepresentative F B H hHG hGH p hp h26 fg).val = qV y := by
  let z := projectedCycle F B H hHG hGH p hp h26 x
  let fg := LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH z
  let r := LatticeBRSTAbsoluteGroundCohomology.representative F B p H hHG hGH fg
  have hb : z - r ∈ LatticeBRSTAbsoluteGroundCohomology.Boundaries F B p H hHG hGH := by
    rw [LatticeBRSTAbsoluteGroundCohomology.boundaries_eq_ker]
    change LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH (z - r) = 0
    rw [(LatticeBRSTAbsoluteGroundCohomology.classMap F B p H hHG hGH).map_sub,
      LatticeBRSTAbsoluteGroundCohomology.classMap_representative, sub_self]
  obtain ⟨y, hy⟩ := hb
  have hy' : LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH y = z.val - r.val :=
    congrArg Subtype.val hy
  let uy := (rangeGroundEquiv F B p).symm y
  have hty : dU uy =
      D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val -
        (rangeGroundEquiv F B p).symm r.val := by
    apply (rangeGroundEquiv F B p).injective
    calc
      rangeGroundEquiv F B p (dU uy) =
          LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH y := by
        have eq := LinearMap.congr_fun
          (actual_ground_chain F B H hHG hGH p hp h26) uy
        change rangeGroundEquiv F B p (dU uy) =
          LatticeBRSTAbsoluteGroundCohomology.d F B p H hHG hGH
            (rangeGroundEquiv F B p uy) at eq
        dsimp only [uy] at eq ⊢
        rw [LinearEquiv.apply_symm_apply] at eq
        exact eq
      _ = z.val - r.val := hy'
      _ = rangeGroundEquiv F B p
          (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val -
            (rangeGroundEquiv F B p).symm r.val) := by
        change _ = (rangeGroundEquiv F B p).toLinearMap
          (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val -
            (rangeGroundEquiv F B p).symm r.val)
        rw [(rangeGroundEquiv F B p).toLinearMap.map_sub]
        change _ = rangeGroundEquiv F B p
          (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val) -
          rangeGroundEquiv F B p ((rangeGroundEquiv F B p).symm r.val)
        rw [LinearEquiv.apply_symm_apply]
        rfl
  have hxD : (c).D x.val = 0 := by rw [fullInput_D]; exact x.property
  have hom := D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.cycle_primitive c ln x.val hxD
  have inc := LinearMap.congr_fun
    (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.locally_nilpotent_perturbation c ln).2.1 uy
  have hhom : qV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.H c ln x.val) =
      x.val - D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
        (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.P c ln x.val) := by
    simpa only [fullInput_D] using hom
  have hinc : qV (D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln uy) =
      D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln (dU uy) := by
    simpa only [LinearMap.comp_apply, fullInput_D] using inc
  refine ⟨fg, ⟨D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.H c ln x.val +
    D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln uy, ?_⟩, ?_⟩
  · rw [map_add, hhom, hinc, hty, map_sub]
    change x.val - D5.S3.HomologicalAlgebra.LocallyNilpotentPerturbation.I c ln
        ((rangeGroundEquiv F B p).symm r.val) = _
    abel
  · rintro fg' ⟨v, hv⟩
    have hz : LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p
        (x - correctedRepresentative F B H hHG hGH p hp h26 fg') = 0 := by
      apply (LatticeBRSTChargeCohomology.sectorClassOf_eq_zero D H h26 hHG hGH p _).mpr
      exact ⟨v, hv.symm⟩
    rw [(LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p).map_sub] at hz
    have he := congrArg (cohomologyEquiv F B H hHG hGH p hp h26) (sub_eq_zero.mp hz)
    rw [cohomologyEquiv_mk F B H hHG hGH p hp h26 x,
      cohomologyEquiv_correctedRepresentative] at he
    exact he.symm

end D5.S3.VertexAlgebra.LatticeBRSTFullNonzeroAbsoluteCohomology
