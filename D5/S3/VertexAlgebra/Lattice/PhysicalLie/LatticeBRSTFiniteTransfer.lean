import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
import D5.S3.HomologicalAlgebra.FinitePerturbation

/-!
Actual current original-Q finite transfer, on the full fixed-energy sector.

The induction and restriction arguments adapt the retained
LatticeBcGhostPerturbationTermination.original_normalized_perturbation_termination
and OriginalQFixedEnergyTransferTransient. The finite perturbation algebra and
the quartet contraction are imported CURRENT library content, not ported.

The normalized perturbation step below consumes the current
`full_remainder_fixed_charge_vectors` theorem on the same `actualBasis`.
The finite perturbation theorem is instantiated directly; no nilpotence or
termination certificate is introduced as a hypothesis.

SOURCE CHECKPOINT ONLY: no native elaboration or kernel acceptance is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFiniteTransfer

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticeSugawaraVirasoro
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration
open LatticeBRSTModeFiltration LatticeBRSTFullOriginalRaising
open D5.S3.HomologicalAlgebra
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock

variable {D : LatticeData} (F : NullFrame D) {t : ℕ}
variable (B : Module.Basis (Fin t) ℂ F.K)
variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
variable (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
variable (beta : Charge D)

def normalizedPerturbation : Module.End ℂ (State D) :=
  h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)

variable (level : ℤ)

def sectorQ : Module.End ℂ (fixedSector H beta level) :=
  (LatticeBRST.totalCharge D H).restrict (Q_preserves F B H hHG hGH beta level)

def sectorD0 : Module.End ℂ (fixedSector H beta level) :=
  (d0 F beta).restrict (d0_preserves F B H hHG hGH beta level)

def sectorH : Module.End ℂ (fixedSector H beta level) :=
  (h F B beta).restrict (h_preserves F B H hHG hGH beta level)

def sectorP0 : Module.End ℂ (fixedSector H beta level) :=
  (P0 F B).restrict (P0_preserves F B H hHG hGH beta level)

local notation "qE" => sectorQ F B H hHG hGH beta level
local notation "dE" => sectorD0 F B H hHG hGH beta level
local notation "hE" => sectorH F B H hHG hGH beta level
local notation "pE" => sectorP0 F B H hHG hGH beta level
local notation "V" => fixedSector H beta level

@[simp] theorem sectorQ_coe (v : V) : (qE v : State D) = LatticeBRST.totalCharge D H v := rfl
@[simp] theorem sectorD0_coe (v : V) : (dE v : State D) = d0 F beta v := rfl
@[simp] theorem sectorH_coe (v : V) : (hE v : State D) = h F B beta v := rfl
@[simp] theorem sectorP0_coe (v : V) : (pE v : State D) = P0 F B v := rfl

private theorem sectorP0_square : pE * pE = pE := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  simpa only [Module.End.mul_apply, sectorP0_coe] using
    LinearMap.congr_fun (spectral_projection_inverse F B).2.2.1 v.val

/-- The retract is the FULL range of the actual zero-count projector INSIDE
the fixed sector. It has both ghost zero-mode states whenever their transverse
energy matches. No relative-ground identification is used to define it. -/
abbrev quartetGround := LinearMap.range pE

/-- A concrete input for the EXISTING library theorem. All its structural fields
come from the existing quartet laws and actual critical total-Q square. -/
def finiteInput (hp : F.pPlus beta ≠ 0) (critical : D.rank = 26) :
    FinitePerturbation.Input (R := ℂ) (U := quartetGround F B H hHG hGH beta level)
      («V» := V) where
  d0 := dE
  h := hE
  delta := qE - dE
  i := (LinearMap.range pE).subtype
  p := (pE).rangeRestrict
  d0_sq := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simpa only [Module.End.mul_apply, sectorD0_coe, LinearMap.zero_apply, Submodule.coe_zero] using
      LinearMap.congr_fun (d0_square F beta) v.val
  pi := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    obtain ⟨v,hv⟩ := u.property
    change pE (u : V) = (u : V)
    rw [← hv]
    exact LinearMap.congr_fun (sectorP0_square F B H hHG hGH beta level) v
  di := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    obtain ⟨v,hv⟩ := u.property
    change d0 F beta (u : State D) = 0
    rw [← hv]
    simpa only [sectorP0_coe, Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (d0_mul_P0 F B beta) v.val
  pd := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    change P0 F B (d0 F beta v.val) = 0
    exact LinearMap.congr_fun (P0_mul_d0 F B beta) v.val
  contraction := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change d0 F beta (h F B beta v.val) + h F B beta (d0 F beta v.val) =
      v.val - P0 F B v.val
    exact LinearMap.congr_fun (homotopy_contraction F B beta hp) v.val
  hh := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simpa only [Module.End.mul_apply, sectorH_coe, LinearMap.zero_apply, Submodule.coe_zero] using
      LinearMap.congr_fun (homotopy_square F B beta) v.val
  hi := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    obtain ⟨v,hv⟩ := u.property
    change h F B beta (u : State D) = 0
    rw [← hv]
    simpa only [sectorP0_coe, Module.End.mul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun (h_mul_P0 F B beta) v.val
  ph := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    change P0 F B (h F B beta v.val) = 0
    exact LinearMap.congr_fun (P0_mul_h F B beta) v.val
  perturbed_sq := by
    have qs : LatticeBRST.totalCharge D H * LatticeBRST.totalCharge D H = 0 := by
      have eq := LatticeBRST.total_square_anomaly D H hHG hGH
      simpa only [critical, Nat.cast_ofNat, sub_self, zero_div, zero_smul, pow_two] using eq
    have eq : dE + (qE - dE) = qE := by abel
    rw [eq]
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    simpa only [Module.End.mul_apply, sectorQ_coe, LinearMap.zero_apply, Submodule.coe_zero] using
      LinearMap.congr_fun qs v.val

set_option backward.isDefEq.respectTransparency true

set_option maxRecDepth 2048 in
include hHG hGH in
/-- The current full-original raising supplier gives one genuine step on each
raw occupation basis vector.  Its charge and energy conclusions are handled
by the literal fixed-sector lemmas above; its degree conclusion is the current
`LatticeBRSTModeFiltration.degree`, including all zero modes and transverse
charge. -/
private theorem normalizedPerturbation_basis_step
    (m : Exponents t) (S : Finset ℕ) :
    normalizedPerturbation F B H beta (actualBasis F B (⟨beta,m⟩,S)) ∈
      signedFiltration F B beta (indexLevel (⟨beta,m⟩,S))
        (degree (⟨beta,m⟩,S) + 1) := by
  classical
  let i : StateIndex D t := (⟨beta,m⟩, S)
  have hcharge : HasCharge F B beta (actualBasis F B i) := by
    intro j hj
    have hji : j = i := by
      by_contra hne
      exact hj (by simp [Module.Basis.repr_self, hne])
    rw [hji]
  have hdegree : ∀ j : StateIndex D t,
      (actualBasis F B).repr (actualBasis F B i) j ≠ 0 →
        degree i ≤ degree j := by
    intro j hj
    have hji : j = i := by
      by_contra hne
      exact hj (by simp [Module.Basis.repr_self, hne])
    simpa [hji]
  have hraise := full_remainder_fixed_charge_vectors F B H hHG hGH beta
    (actualBasis F B i) hcharge (degree i) hdegree
  have hsector : actualBasis F B i ∈ fixedSector H beta (indexLevel i) := by
    exact basis_mem_fixedSector F B H hHG hGH i
  have hminus :
      (LatticeBRST.totalCharge D H - d0 F beta) (actualBasis F B i) ∈
        fixedSector H beta (indexLevel i) := by
    exact Submodule.sub_mem _
      (Q_preserves F B H hHG hGH beta (indexLevel i) (actualBasis F B i) hsector)
      (d0_preserves F B H hHG hGH beta (indexLevel i) (actualBasis F B i) hsector)
  have hnorm : normalizedPerturbation F B H beta (actualBasis F B i) ∈
      fixedSector H beta (indexLevel i) := by
    unfold normalizedPerturbation
    exact h_preserves F B H hHG hGH beta (indexLevel i)
      ((LatticeBRST.totalCharge D H - d0 F beta) (actualBasis F B i)) hminus
  rw [mem_signedFiltration_iff]
  intro j hj
  have hje := (mem_fixedSector_iff F B H hHG hGH beta (indexLevel i)
      (normalizedPerturbation F B H beta (actualBasis F B i))).mp hnorm j hj
  refine ⟨hje.1, hje.2, ?_⟩
  exact hraise.2.2 j hj

include hHG hGH in
private theorem normalizedPerturbation_raises
    (level lower : ℤ) (v : State D)
    (hv : v ∈ signedFiltration F B beta level lower) :
    normalizedPerturbation F B H beta v ∈
      signedFiltration F B beta level (lower + 1) := by
  have inclusion : signedFiltration F B beta level lower ≤
      (signedFiltration F B beta level (lower + 1)).comap
        (normalizedPerturbation F B H beta) := by
    apply Submodule.span_le.mpr
    rintro v ⟨⟨⟨gamma,m⟩,S⟩, ⟨hc,he,hd⟩, rfl⟩
    dsimp only at hc
    subst gamma
    have step := normalizedPerturbation_basis_step F B H hHG hGH beta m S
    change normalizedPerturbation F B H beta (actualBasis F B (⟨beta,m⟩,S)) ∈
      signedFiltration F B beta level (lower + 1)
    rw [mem_signedFiltration_iff] at step ⊢
    intro j hj
    obtain ⟨hcj,hej,hdj⟩ := step j hj
    exact ⟨hcj, hej.trans he, by omega⟩
  exact inclusion hv

include hHG hGH in
/-- Every vector in the literal fixed charge/energy sector is killed by the
uniform finite power.  The `toNat` expression also covers empty negative-level
sectors: for `level < 0`, the same filtration exhaustion inequality is proved
arithmetically rather than assumed. -/
theorem actual_normalized_perturbation_termination
    (level : ℤ) (v : State D)
    (charge : chargeProject beta v = v)
    (energy : totalL0 H v = (groundEnergy beta + (level : ℂ) - 1) • v) :
    ((h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)) ^
      (2 * level.toNat + 2)) v = 0 := by
  have iterated (k : ℕ) :
      (normalizedPerturbation F B H beta ^ k) v ∈
        signedFiltration F B beta level (-level + (k : ℤ)) := by
    induction k with
    | zero =>
      simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero] using
        sector_mem_filtration F B H hHG hGH beta level v ⟨charge,energy⟩
    | succ k ih =>
      have next := normalizedPerturbation_raises F B H hHG hGH beta
        level (-level + (k : ℤ)) _ ih
      simpa only [pow_succ', Module.End.mul_apply, Nat.cast_add, Nat.cast_one,
        add_assoc] using next
  have out := iterated (2 * level.toNat + 2)
  rw [filtration_exhausted F B beta level
    (-level + ((2 * level.toNat + 2 : ℕ) : ℤ)) (by omega)] at out
  simpa [normalizedPerturbation] using out

theorem sector_correction_power_coe (k : ℕ) (v : V) :
    (((hE * (qE - dE)) ^ k) v : State D) =
      ((h F B beta * (LatticeBRST.totalCharge D H - d0 F beta)) ^ k) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    change (((hE * (qE - dE)) ^ k) ((hE * (qE - dE)) v) : State D) = _
    rw [ih]
    rfl

theorem sector_correction_nilpotent :
    (hE * (qE - dE)) ^ (2 * level.toNat + 2) = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  rw [sector_correction_power_coe]
  exact actual_normalized_perturbation_termination F B H hHG hGH beta level
    v v.property.1 v.property.2

/-- Real finite perturbation consumer, with the bound supplied by the full
fixed-energy signed filtration.  `FinitePerturbation` is the existing HPL
implementation; this theorem only instantiates it with the actual quartet
zero-count projector and the rank-26 square of the full original Q. -/
theorem actual_nonzero_charge_original_q_transfer
    (hp : F.pPlus beta ≠ 0) (critical : D.rank = 26) :
    (finiteInput F B H hHG hGH beta level hp critical).Conclusion
      (2 * level.toNat + 2) := by
  apply FinitePerturbation.Input.finite_perturbation
  · omega
  · exact sector_correction_nilpotent F B H hHG hGH beta level

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTFiniteTransfer
