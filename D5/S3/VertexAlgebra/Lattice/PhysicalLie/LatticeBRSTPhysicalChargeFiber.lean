/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalChargeFiber
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPhysicalChargeFiber
   mirror-E: none(waiver:source-candidate-not-enrolled)
   anchors: []
   utility: none
   digest: Literal physical charge fibers and two-slot removal of actual HPL corrections. -/

import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear
import D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import Batteries.Tactic.OpenPrivate

/-!
SOURCE ONLY UNCOMPILED. The ambient quotient, Q and global bilinear form are
literal supplier definitions. Incoming boundaries still have primitives in
ALL State D. The frame in the recovery theorem is arbitrary and complex.

Attribution: the original BRST, finite HPL and source-Wick suppliers; the
no-minus/pure-down candidate supplies support of the actual inclusion.
The bilinear current argument below uses no Hermitian positivity argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators TensorProduct

open private completeBasis_plus from
  D5.S3.VertexAlgebra.Lattice.LatticeLightConeCoordinates
open private mem_fixedMomentum_iff_chargeProject from
  D5.S3.VertexAlgebra.Lattice.LatticeRelativeBRSTGround
open private physical_charge_representative from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTNeutralPhysicalCartan
open private sectorRepresentative physical_shell from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear
open private pairing_down from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm
open private matterMap current_matterMap creation_matterMap
  minus_derivative_zero rename_noMinus plusCorrections_le from
  D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents LatticePositiveEnergy LatticeMatterGhostCoupling
open LatticeLightConeCoordinates LatticeLightConeCoordinates.NullFrame
open LatticeQuartetContraction D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPureDown
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalTransverseRealization
open D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTOppositeChargeForm D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTGlobalPhysicalBilinear
open SourceBPZ.OriginalSourcePairing SourceBPZ.SourcePairingLaws
open LatticeRelativeBRSTCohomology.Ground (energyTarget)
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open MvPolynomial

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26) (hHG : H * gramComplex D = 1)
  (hGH : gramComplex D * H = 1)

local notation "Coh" => LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH
local notation "Phys" => D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalImage D H h26 hHG hGH

/-- The charge fiber INSIDE the original global cohomology. -/
def physicalChargeFiber (p : Charge D) : Submodule ℂ Coh :=
  Phys ⊓ LinearMap.range (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion D H h26 hHG hGH p)

private theorem inclusion_projection_fixed (p : Charge D) (x : Coh)
    (hx : x ∈ LinearMap.range
      (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion D H h26 hHG hGH p)) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion D H h26 hHG hGH p
      (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.projection D H h26 hHG hGH p x) = x := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨u,rfl⟩ := D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf_surjective
    D H h26 hHG hGH p a
  rw [D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion_sectorClassOf,
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.projection_classOf,
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion_sectorClassOf]
  apply congrArg (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH)
  apply Subtype.ext
  exact D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.chargeProject_fixed D p _ u.val.property

/-- This is precisely the fixed space of the existing inclusion/projection
operator on the literal physical image. -/
theorem mem_physicalChargeFiber (p : Charge D) (x : Coh) :
    x ∈ physicalChargeFiber D H h26 hHG hGH p ↔
      x ∈ Phys ∧
        D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.inclusion D H h26 hHG hGH p
          (D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.projection D H h26 hHG hGH p x) = x := by
  constructor
  · rintro ⟨hx,hp⟩
    exact ⟨hx,inclusion_projection_fixed D H h26 hHG hGH p x hp⟩
  · rintro ⟨hx,hp⟩
    exact ⟨hx,⟨D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.projection D H h26 hHG hGH p x,hp⟩⟩

private def globalRepresentative (p : Charge D)
    (a : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalCycles H p (1-chargeEnergy D p)) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalStates D H := by
  refine ⟨a.val.val,a.property.1,a.property.2.1,a.property.2.2,?_⟩
  have he := a.val.property.2
  rw [physical_shell D p,zero_smul] at he
  exact he

/-- No new quotient: the old fixed-shell image and the literal charge fiber
are equal as submodules of the SAME original global cohomology. -/
theorem physicalChargeFiber_eq_fixedImage (p : Charge D) :
    physicalChargeFiber D H h26 hHG hGH p =
      D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalImage H p (1-chargeEnergy D p) h26 hHG hGH := by
  ext x
  constructor
  · intro hx
    obtain ⟨a,ha,he⟩ := physical_charge_representative D H h26 hHG hGH p x hx.1 hx.2
    exact ⟨sectorRepresentative D H p a ha,he⟩
  · rintro ⟨a,rfl⟩
    refine ⟨⟨globalRepresentative D H p a,rfl⟩,?_⟩
    let z : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorCycles D H p :=
      ⟨⟨a.val.val,by
        apply (mem_fixedMomentum_iff_chargeProject
          p a.val.val).mpr
        exact a.val.property.1⟩,by
        apply Subtype.ext
        exact a.property.1⟩
    exact ⟨D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology.sectorClassOf D H h26 hHG hGH p z,rfl⟩

/-- The literal inclusion into the global physical image. -/
private def fiberInclusion (p : Charge D) :
    physicalChargeFiber D H h26 hHG hGH p →ₗ[ℂ] Phys where
  toFun x := ⟨x.val,x.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def fixedImageEquiv (p : Charge D) :
    D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalPairing.physicalImage H p (1-chargeEnergy D p) h26 hHG hGH ≃ₗ[ℂ]
      physicalChargeFiber D H h26 hHG hGH p where
  toFun x := ⟨x.val,by rw [physicalChargeFiber_eq_fixedImage];exact x.property⟩
  invFun x := ⟨x.val,by rw [← physicalChargeFiber_eq_fixedImage];exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Actual global B restricted to opposite physical charge fibers. -/
def oppositePairing (p : Charge D) :
    physicalChargeFiber D H h26 hHG hGH p →ₗ[ℂ]
      Module.Dual ℂ (physicalChargeFiber D H h26 hHG hGH (-p)) where
  toFun x := (physicalBilinearForm D H h26 hHG hGH
    (fiberInclusion D H h26 hHG hGH p x)).comp
      (fiberInclusion D H h26 hHG hGH (-p))
  map_add' x y := by ext z;simp [map_add]
  map_smul' c x := by ext z;simp [map_smul]

private theorem charge_energy_neg (p : Charge D) :
    chargeEnergy D (-p) = chargeEnergy D p := by
  unfold chargeEnergy
  rw [bilinear_neg_neg]

private def oppositeEnergyEquiv {t : ℕ} (p : Charge D) :
    energyTarget D t p ≃ₗ[ℂ] energyTarget D t (-p) where
  toFun f := ⟨f.val,by simpa only [charge_energy_neg] using f.property⟩
  invFun f := ⟨f.val,by simpa only [charge_energy_neg] using f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- HPL coordinates on the original physical charge fiber, at the exact
signed shell 1-chargeEnergy p. -/
private def transverseFiberEquiv (F : NullFrame D) {t : ℕ}
    (B : Module.Basis (Fin t) ℂ F.K) (p : Charge D) (hp : F.pPlus p ≠ 0) :
    energyTarget D t p ≃ₗ[ℂ] physicalChargeFiber D H h26 hHG hGH p :=
  (physicalTransverseEquiv F B H hHG hGH p (1-chargeEnergy D p) hp h26
    (physical_shell D p)).trans (fixedImageEquiv D H h26 hHG hGH p)

section ComplexFramePairing

variable {D H h26 hHG hGH}
variable (F : NullFrame D) {t : ℕ} (B : Module.Basis (Fin t) ℂ F.K)

private theorem source_a (u : E D) (n : ℤ) (v w : Carrier D) :
    sourcePairing D (a u n v) w = -sourcePairing D v (a u (-n) w) := by
  classical
  simp only [a,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,
    map_smul,LinearMap.smul_apply,sourcePairing_neutralMode,
    smul_eq_mul,mul_neg,Finset.sum_neg_distrib]

private theorem plus_current_noMinus (p : Charge D) (r : ℕ)
    (P : PolynomialCoordinates (Label t)) (hP : P ∈ noMinusPolynomials t) :
    a F.ePlus ((r : ℤ)+1) (matterMap F B p P) = 0 := by
  rw [current_matterMap,
    LatticeBRSTModeFiltration.cm_plus_positive,
    minus_derivative_zero P hP,smul_zero,map_zero]

private theorem plus_ideal_left (p q : Charge D)
    (P Q : PolynomialCoordinates (Label t))
    (hP : P ∈ plusCorrections t) (hQ : Q ∈ noMinusPolynomials t) :
    sourcePairing D (matterMap F B p P) (matterMap F B q Q) = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
      obtain ⟨r,e,he,rfl⟩ := hP
      rw [creation_matterMap,completeBasis_plus,source_a]
      have hn : -(-(r : ℤ)-1) = (r : ℤ)+1 := by ring
      rw [hn,plus_current_noMinus F B q r Q hQ,map_zero,neg_zero]
  | zero => simp
  | add P R hP hR iP iR => simp only [map_add,LinearMap.add_apply,iP,iR,add_zero]
  | smul c P hP iP => simp only [map_smul,LinearMap.smul_apply,iP,smul_zero]

private theorem plus_ideal_right (p q : Charge D)
    (P Q : PolynomialCoordinates (Label t))
    (hP : P ∈ noMinusPolynomials t) (hQ : Q ∈ plusCorrections t) :
    sourcePairing D (matterMap F B p P) (matterMap F B q Q) = 0 := by
  rw [sourcePairing_symmetric]
  exact plus_ideal_left F B q p Q P hQ hP

private theorem remove_both_corrections (p q : Charge D)
    (f g : MvPolynomial (Fin t × ℕ) ℂ)
    (P Q : PolynomialCoordinates (Label t))
    (hP : P ∈ plusCorrections t) (hQ : Q ∈ plusCorrections t) :
    statePairing D
      (sector F B p (rename transverseVariable f + P) (ket {1}))
      (sector F B q (rename transverseVariable g + Q) (ket {1})) =
      sourcePairing D (Finsupp.single p (transverseOriginal F B f))
        (Finsupp.single q (transverseOriginal F B g)) := by
  change statePairing D
    (matterMap F B p (rename transverseVariable f + P) ⊗ₜ[ℂ] ket {1})
    (matterMap F B q (rename transverseVariable g + Q) ⊗ₜ[ℂ] ket {1}) = _
  rw [pairing_down]
  rw [(matterMap F B p).map_add,(sourcePairing D).map_add,LinearMap.add_apply]
  rw [plus_ideal_left F B p q P _ hP
    ((noMinusPolynomials t).add_mem (rename_noMinus g) (plusCorrections_le t hQ)),add_zero]
  rw [(matterMap F B q).map_add,
    (sourcePairing D (matterMap F B p (rename transverseVariable f))).map_add]
  rw [plus_ideal_right F B p q _ Q (rename_noMinus f) hQ,add_zero]
  rfl

/-- All positive terms of both genuine HPL inclusions disappear from the
actual global B. The opposite lift uses the same arbitrary COMPLEX frame.
No invariance or correction-orthogonality hypothesis is introduced. -/
private theorem oppositePairing_transverse (p : Charge D) (hp : F.pPlus p ≠ 0)
    (hm : F.pPlus (-p) ≠ 0) (f : energyTarget D t p)
    (g : energyTarget D t (-p)) :
    oppositePairing D H h26 hHG hGH p
      (transverseFiberEquiv D H h26 hHG hGH F B p hp f)
      (transverseFiberEquiv D H h26 hHG hGH F B (-p) hm g) =
      integerWick D (transverseOriginal F B f.val) (transverseOriginal F B g.val) := by
  let a := physicalLift F B H hHG hGH p (1-chargeEnergy D p) hp h26
    (physical_shell D p) f
  let b := physicalLift F B H hHG hGH (-p) (1-chargeEnergy D (-p)) hm h26
    (physical_shell D (-p)) g
  have ha : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH
      (globalRepresentative D H p a) =
      (transverseFiberEquiv D H h26 hHG hGH F B p hp f).val := rfl
  have hb : D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalLie.physicalClass D H h26 hHG hGH
      (globalRepresentative D H (-p) b) =
      (transverseFiberEquiv D H h26 hHG hGH F B (-p) hm g).val := rfl
  change physicalBilinearForm D H h26 hHG hGH _ _ = _
  rw [physicalBilinearForm_representatives D H h26 hHG hGH _ _
    (globalRepresentative D H p a) (globalRepresentative D H (-p) b) ha hb]
  obtain ⟨P,hP,hnoP,heP,hprimaryP⟩ := physicalLift_pure_down F B H hHG hGH
    p (1-chargeEnergy D p) hp h26 (physical_shell D p) f
  obtain ⟨Q,hQ,hnoQ,heQ,hprimaryQ⟩ := physicalLift_pure_down F B H hHG hGH
    (-p) (1-chargeEnergy D (-p)) hm h26 (physical_shell D (-p)) g
  change statePairing D a.val.val b.val.val = _
  rw [heP,heQ,remove_both_corrections F B p (-p) f.val g.val P Q hP hQ,
    sourcePairing_single_single,if_pos rfl]

end ComplexFramePairing
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTPhysicalChargeFiber
