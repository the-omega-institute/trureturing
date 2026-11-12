/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTGlobalPhysicalBilinear
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTGlobalPhysicalBilinear
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Bilinear descent to the literal all-charge original-Q physical image. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
import D5.S3.VertexAlgebra.Lattice.LatticeNullFrameExistence
import Batteries.Tactic.OpenPrivate

/-!
SOURCE_ONLY_UNCOMPILED. The three new imports above remain the sealed,
uncompiled reflection, opposite-charge-form and neutral-Cartan candidates.
The source150 suppliers retain their native accepted status at
abd316f85f32ac4d65154e20e7268870a632e5ee; this file has no native acceptance.

The carrier below is EXACTLY LatticeBRSTPhysicalLie.physicalImage, and the
class map is its existing physicalClass. No quotient or operation is replaced.
Every incoming primitive in the proof belongs to ALL original State D.
Projection of such a primitive is a derived step, never a new premise.

At nonzero charge the accepted complex null-frame existence theorem supplies
the actual frame and its actual transverseBasis. The integer level is derived
from the accepted integral half-norm identity. The accepted ordinary inserted
representative theorem is applied only after reflection has put both arguments
in the same charge and shell. At zero charge, the terminal neutral shell and
the exclusion of unrestricted global primitives show that the boundary itself
vanishes. Finite sums of the ORIGINAL charge projections then give the global
kernel statement used to construct the two linear maps.

Attribution: the original lattice fields and Wick pairing retain Bakalov--Kac,
Carnahan and Kytölä attribution; BRST and relative-preimage suppliers retain
Becchi--Rouet--Stora--Tyutin, Kato--Ogawa and Lian--Zuckerman attribution.
Finite-support, linear-map and quotient algebra is Mathlib/Batteries material.
Invariance, perfect opposite-charge duality, actual primary representatives,
Monster realization, CFT, anomalies, fusion, string theory and AdS/CFT remain
downstream. None is an assumption or a conclusion of this construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private matterC conjugation_tmul_ket from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection
open private chargeProject_mem from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
open private project_physical neutral_number_one_shell from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear

open LatticeGeneratingFieldLocality
open LatticeMatterGhostCoupling (State)
open LatticeSugawaraCurrents (gramComplex)
open LatticePositiveEnergy (chargeEnergy two_chargeEnergy)
open LatticeRelativeMassShell (fixedMomentum mem_fixedMomentum_iff
  fixedMomentum_eq_span tensorBasis tensorBasis_apply coeff_tmul_original)
open LatticeQuartetContraction (chargeProject)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology (chargeProject_fixed chargeProject_commutes
  chargeSupport sum_chargeProject)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie (physicalStates physicalClass physicalImage)
open LatticeBRSTCohomologyField (cycles Cohomology classOf classOf_eq_zero)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeReflection (conjugation conjugation_totalCharge
  conjugation_physical)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm (statePairing statePairing_symmetric
  statePairing_charge_orthogonal)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan (cartanState cartan_no_global_primitive)
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPerturbationFiltration (groundEnergy)

variable (D : LatticeData)

/-- Reflection reverses the literal full charge sector, without a shell or
physicality premise. Used below before invoking fixed-sector descent. -/
private theorem conjugation_fixedMomentum (p : Charge D) (x : State D)
    (hx : x ∈ fixedMomentum D p) :
    conjugation D x ∈ fixedMomentum D (-p) := by
  classical
  rw [fixedMomentum_eq_span D p] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      change l.1.1 = p at hl
      rw [tensorBasis_apply, conjugation_tmul_ket]
      simp only [matterC, LinearMap.coe_mk, AddHom.coe_mk,
        SourceBPZ.OriginalMatterHermitian.kappaCarrier_single]
      change LatticeInvolution.thetaLinear D
        (Finsupp.single l.1.1 (SourceBPZ.OriginalMatterHermitian.kappaOsc
          (MvPolynomial.monomial l.1.2 1))) ⊗ₜ[ℂ]
            D5.S3.Quantum.Fermionic.CountableOccupationFock.ket l.2 ∈ _
      rw [LatticeInvolution.theta_single]
      apply (mem_fixedMomentum_iff D (-p) _).mpr
      rintro ⟨⟨q, e⟩, S⟩ hq
      rw [coeff_tmul_original]
      have hqp : q ≠ -l.1.1 := by simpa only [hl] using hq
      simp [Finsupp.single_apply, Ne.symm hqp]
  | zero => simpa only [map_zero] using (fixedMomentum D (-p)).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (fixedMomentum D (-p)).add_mem ihx ihy
  | smul a x hx ih =>
      rw [map_smulₛₗ]
      exact (fixedMomentum D (-p)).smul_mem _ ih

/-- A level in Z for every actual integral charge, including zero. This uses
evenness of the original lattice, and asserts no bound on the set of charges. -/
private theorem physical_shell (p : Charge D) :
    groundEnergy p + ((1 - chargeEnergy D p : ℤ) : ℂ) - 1 = 0 := by
  have he : (2 : ℂ) * (chargeEnergy D p : ℂ) = (bilinear D p p : ℂ) := by
    exact_mod_cast two_chargeEnergy D p
  unfold groundEnergy
  rw [← he]
  push_cast
  ring

/-- The SAME original physical state, viewed in the accepted fixed-sector
physicalCycles subtype at its derived integer level. No transport is used. -/
private def sectorRepresentative
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (p : Charge D) (x : physicalStates D H)
    (hx : (x : State D) ∈ fixedMomentum D p) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalCycles H p (1 - chargeEnergy D p) := by
  refine ⟨⟨(x : State D), ?_⟩, x.property.1, x.property.2.1,
    x.property.2.2.1⟩
  refine ⟨chargeProject_fixed D p (x : State D) hx, ?_⟩
  rw [physical_shell D p, zero_smul]
  exact x.property.2.2.2

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (h26 : D.rank = 26)
  (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)

local notation "C" => Cohomology D H h26 hHG hGH
local notation "cl" => physicalClass D H h26 hHG hGH

include h26 hHG hGH in
/-- A boundary in a fixed charge is paired with an arbitrary physical charge.
The primitive z is unrestricted original State D, even in this local step. -/
private theorem fixed_boundary_left
    (p q : Charge D) (x y : physicalStates D H)
    (hx : (x : State D) ∈ fixedMomentum D p)
    (hy : (y : State D) ∈ fixedMomentum D q)
    (z : State D) (hz : LatticeBRST.totalCharge D H z = (x : State D)) :
    statePairing D (x : State D) (y : State D) = 0 := by
  classical
  by_cases hpq : p + q = 0
  · by_cases hp : p = 0
    · subst p
      obtain ⟨e, he, _⟩ := neutral_number_one_shell D H hHG hGH
        (x : State D) hx x.property.2.1 x.property.2.2.1 x.property.2.2.2
      have he0 : e = 0 := cartan_no_global_primitive D H h26 hHG hGH e z
        (hz.trans he.symm)
      have hx0 : (x : State D) = 0 := by rw [← he, he0, map_zero]
      rw [hx0, map_zero, LinearMap.zero_apply]
    · have hq : q = -p := by
        calc
          q = -p + (p + q) := by abel
          _ = -p := by rw [hpq, add_zero]
      subst q
      let cx : physicalStates D H :=
        ⟨conjugation D (x : State D), conjugation_physical H h26 hHG hGH x⟩
      have hcx : (cx : State D) ∈ fixedMomentum D (-p) :=
        conjugation_fixedMomentum D p (x : State D) hx
      have hnp : -p ≠ 0 := by
        intro h
        exact hp (neg_eq_zero.mp h)
      obtain ⟨F, hF⟩ := LatticeNullFrameExistence.exists_nullFrame_pPlus_ne_zero
        D H hHG (by omega) (-p) hnp
      let a := sectorRepresentative D H (-p) cx hcx
      let b := sectorRepresentative D H (-p) y hy
      have ha :
          D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalClass H (-p)
              (1 - chargeEnergy D (-p)) h26 hHG hGH a =
            D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalClass H (-p)
              (1 - chargeEnergy D (-p)) h26 hHG hGH 0 := by
        rw [map_zero]
        change classOf D H h26 hHG hGH
          (⟨(cx : State D), cx.property.1⟩ : cycles D H) = 0
        apply (classOf_eq_zero D H h26 hHG hGH _).mpr
        refine ⟨conjugation D z, ?_⟩
        change LatticeBRST.totalCharge D H (conjugation D z) =
          conjugation D (x : State D)
        rw [← conjugation_totalCharge H hHG hGH, hz]
      have h := D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.inserted_representatives
        F F.transverseBasis H hHG hGH (-p) (1 - chargeEnergy D (-p))
        hF h26 (physical_shell D (-p)) a 0 b b ha rfl
      change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.inserted
          (conjugation D (x : State D)) (y : State D) =
        D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.inserted (0 : State D) (y : State D) at h
      change D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.inserted
        (conjugation D (x : State D)) (y : State D) = 0
      simpa only [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.inserted_zero_left] using h
  · exact statePairing_charge_orthogonal p q (x : State D) (y : State D)
      (chargeProject_fixed D p (x : State D) hx)
      (chargeProject_fixed D q (y : State D) hy) hpq

include h26 hHG hGH in
/-- Finite assembly on actual original states. There is no hypothesis on the
charge, energy, b0, number or support of the incoming primitive z. -/
private theorem global_boundary_left
    (x y : physicalStates D H) (z : State D)
    (hz : LatticeBRST.totalCharge D H z = (x : State D)) :
    statePairing D (x : State D) (y : State D) = 0 := by
  classical
  let zsum : State D := ∑ r ∈ chargeSupport D z, chargeProject r z
  have hzsum : LatticeBRST.totalCharge D H zsum = (x : State D) := by
    change LatticeBRST.totalCharge D H
      (∑ r ∈ chargeSupport D z, chargeProject r z) = (x : State D)
    rw [sum_chargeProject, hz]
  calc
    statePairing D (x : State D) (y : State D) =
        statePairing D
          (∑ p ∈ chargeSupport D (x : State D), chargeProject p (x : State D))
          (∑ q ∈ chargeSupport D (y : State D), chargeProject q (y : State D)) := by
            rw [sum_chargeProject, sum_chargeProject]
    _ = ∑ p ∈ chargeSupport D (x : State D),
        ∑ q ∈ chargeSupport D (y : State D),
          statePairing D (chargeProject p (x : State D))
            (chargeProject q (y : State D)) := by
              simp only [map_sum, LinearMap.sum_apply]
              rw [Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro q hq
      exact fixed_boundary_left D H h26 hHG hGH p q
        ⟨chargeProject p (x : State D), project_physical D H hHG hGH p x⟩
        ⟨chargeProject q (y : State D), project_physical D H hHG hGH q y⟩
        (chargeProject_mem D p (x : State D))
        (chargeProject_mem D q (y : State D)) (chargeProject p zsum) (by
          rw [← chargeProject_commutes D H, hzsum])

include h26 hHG hGH in
private theorem equal_class_left (a a' b : physicalStates D H)
    (ha : cl a = cl a') :
    statePairing D (a : State D) (b : State D) =
      statePairing D (a' : State D) (b : State D) := by
  let d : physicalStates D H := a - a'
  have hd : cl d = 0 := by
    change cl (a - a') = 0
    rw [map_sub, ha, sub_self]
  have hd' : classOf D H h26 hHG hGH
      (⟨(d : State D), d.property.1⟩ : cycles D H) = 0 := hd
  obtain ⟨z, hz⟩ := (classOf_eq_zero D H h26 hHG hGH _).mp hd'
  have h := global_boundary_left D H h26 hHG hGH d b z hz
  change statePairing D ((a : State D) - (a' : State D)) (b : State D) = 0 at h
  rw [map_sub, LinearMap.sub_apply] at h
  exact sub_eq_zero.mp h

/-- BOTH slots descend under equality in the ORIGINAL GLOBAL cohomology.
The equality criterion uses range(Q) on ALL State D. The second slot follows
from proved state-level bilinear symmetry and the first-slot kernel theorem. -/
theorem statePairing_representatives (a a' b b' : physicalStates D H)
    (ha : cl a = cl a') (hb : cl b = cl b') :
    statePairing D (a : State D) (b : State D) =
      statePairing D (a' : State D) (b' : State D) := by
  calc
    _ = statePairing D (a' : State D) (b : State D) :=
      equal_class_left D H h26 hHG hGH a a' b ha
    _ = statePairing D (b : State D) (a' : State D) := statePairing_symmetric _ _
    _ = statePairing D (b' : State D) (a' : State D) :=
      equal_class_left D H h26 hHG hGH b b' a' hb
    _ = _ := statePairing_symmetric _ _

/- This is a set-theoretic section of the EXISTING surjective physicalClass
range restriction. No linearity is assumed of the section. Its use in each
linear-map law below is justified by the proved representative theorem. -/
private def representative (x : physicalImage D H h26 hHG hGH) :
    physicalStates D H := Classical.choose x.property

private theorem representative_class (x : physicalImage D H h26 hHG hGH) :
    cl (representative D H h26 hHG hGH x) = (x : C) :=
  Classical.choose_spec x.property

/-- The actual complex bilinear form on the LITERAL existing all-charge
physical image. The two linearity proofs use global kernel annihilation;
the chosen section itself has no linearity or charge-preservation premise. -/
def physicalBilinearForm : LinearMap.BilinForm ℂ (physicalImage D H h26 hHG hGH) where
  toFun x := {
    toFun y := statePairing D
      (representative D H h26 hHG hGH x : State D)
      (representative D H h26 hHG hGH y : State D)
    map_add' y z := by
      let r := representative D H h26 hHG hGH
      have hc : cl (r (y + z)) = cl (r y + r z) := by
        rw [representative_class, map_add, representative_class, representative_class]
        rfl
      calc
        statePairing D (r x : State D) (r (y + z) : State D) =
            statePairing D (r x : State D) ((r y + r z : physicalStates D H) : State D) :=
          statePairing_representatives D H h26 hHG hGH (r x) (r x)
            (r (y + z)) (r y + r z) rfl hc
        _ = _ := map_add (statePairing D (r x : State D)) _ _
    map_smul' a y := by
      let r := representative D H h26 hHG hGH
      have hc : cl (r (a • y)) = cl (a • r y) := by
        rw [representative_class, map_smul, representative_class]
        rfl
      calc
        statePairing D (r x : State D) (r (a • y) : State D) =
            statePairing D (r x : State D) ((a • r y : physicalStates D H) : State D) :=
          statePairing_representatives D H h26 hHG hGH (r x) (r x)
            (r (a • y)) (a • r y) rfl hc
        _ = _ := map_smul (statePairing D (r x : State D)) a (r y : State D) }
  map_add' x z := by
    apply LinearMap.ext
    intro y
    let r := representative D H h26 hHG hGH
    have hc : cl (r (x + z)) = cl (r x + r z) := by
      rw [representative_class, map_add, representative_class, representative_class]
      rfl
    change statePairing D (r (x + z) : State D) (r y : State D) =
      statePairing D (r x : State D) (r y : State D) +
        statePairing D (r z : State D) (r y : State D)
    calc
      _ = statePairing D ((r x + r z : physicalStates D H) : State D) (r y : State D) :=
        statePairing_representatives D H h26 hHG hGH (r (x + z)) (r x + r z)
          (r y) (r y) hc rfl
      _ = _ := by rw [Submodule.coe_add, map_add, LinearMap.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    let r := representative D H h26 hHG hGH
    have hc : cl (r (a • x)) = cl (a • r x) := by
      rw [representative_class, map_smul, representative_class]
      rfl
    change statePairing D (r (a • x) : State D) (r y : State D) =
      a • statePairing D (r x : State D) (r y : State D)
    calc
      _ = statePairing D ((a • r x : physicalStates D H) : State D) (r y : State D) :=
        statePairing_representatives D H h26 hHG hGH (r (a • x)) (a • r x)
          (r y) (r y) hc rfl
      _ = _ := by rw [Submodule.coe_smul, map_smul, LinearMap.smul_apply]

/-- Recovery for ALL actual physical representatives of two elements of the
existing image. Both equalities are in the original unrestricted quotient. -/
theorem physicalBilinearForm_representatives
    (x y : physicalImage D H h26 hHG hGH) (a b : physicalStates D H)
    (ha : cl a = (x : C)) (hb : cl b = (y : C)) :
    physicalBilinearForm D H h26 hHG hGH x y =
      statePairing D (a : State D) (b : State D) := by
  exact statePairing_representatives D H h26 hHG hGH
    (representative D H h26 hHG hGH x) a
    (representative D H h26 hHG hGH y) b
    ((representative_class D H h26 hHG hGH x).trans ha.symm)
    ((representative_class D H h26 hHG hGH y).trans hb.symm)

end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear
