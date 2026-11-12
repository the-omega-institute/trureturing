/- GID: D5/S3/VertexAlgebra/Lattice/LatticeBRSTPhysicalLieSectors
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeBRSTPhysicalLieSectors
   mirror-E: none(waiver:original-physical-current-charge)
   anchors: []
   utility: none
   digest: Original field charge addition and fixed-sector maps into the literal physical Lie image. -/

/- The frozen physical-pairing module is a source-only, unaccepted supplier.
Only its literal physicalCycles/physicalClass/physicalImage definitions are
used. No pairing or no-ghost claim is made. The actual raw field's epsilon,
cocycle, bilinear form and finite supports are preserved by the proof.
proof_shape: originalMode_charge, current_charge,
  physical_current_fixedSector: content
admission_basis: escape-witness
escape_witness: Charge addition is proved from original raw coefficients,
neutral derivatives, nested fields and tensor convolution, then related to
the existing fixed-sector global-image maps with actual shell bookkeeping.
-/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTPhysicalLie
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTPhysicalPairing
import D5.S3.VertexAlgebra.LatticeActualProductKernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct VertexOperator

namespace D5.S3.VertexAlgebra.LatticeBRSTPhysicalLieSectors

open LatticeGeneratingFieldLocality
open LatticeMatterGhostCoupling (State ghostB)
open LatticeBRSTCohomologyField (originalMode originalMode_apply cycles classOf Cohomology)
open LatticeBRSTCohomologyBVSecondOrder (descentCurrent cohomologyCurrent)
open LatticeRelativeMassShell (fixedMomentum mem_fixedMomentum_iff fixedMomentum_eq_span
  tensorBasis tensorBasis_apply coeff_tmul_original)
open LatticeBRSTPerturbationFiltration (fixedSector groundEnergy)
open LatticeQuartetContraction (chargeProject)
open LatticeBRSTPhysicalLie (physicalStates physicalClass physicalImage physicalLieSubalgebra)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)
open FieldNormalProduct (normalMinusOne dividedDerivative)
open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField
open private term term_tmul Y_modes from
  D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostStateField

noncomputable section

variable (D : LatticeData)

private def matterSector (a : Charge D) : Submodule ℂ (Carrier D) :=
  LinearMap.range (Finsupp.lsingle a : Oscillator D →ₗ[ℂ] Carrier D)

private theorem derivative_charge (i : Index D) (n : ℤ) (a : Charge D)
    (v : matterSector D a) :
    ((dividedDerivative i.2 (LatticeFiniteNegativeGeneration.neutralField D i.1))[[n]]) v ∈
      matterSector D a := by
  obtain ⟨p,hp⟩ := v.property
  rw [← hp, derivative_modes]
  apply (matterSector D a).smul_mem
  change LatticeFiniteNegativeGeneration.neutralMode D i.1 (n-i.2)
    (Finsupp.single a p) ∈ matterSector D a
  simp only [LatticeFiniteNegativeGeneration.neutralMode, Finsupp.lsum_single,
    LinearMap.comp_apply, Finsupp.lsingle_apply]
  exact ⟨_,rfl⟩

private theorem word_charge (a b : Charge D) (w : List (Index D)) (n : ℤ)
    (q : Oscillator D) :
    ((LatticeAllStateField.wordField D a w)[[n]]) (Finsupp.single b q) ∈
      matterSector D (a+b) := by
  induction w generalizing n q with
  | nil =>
    rw [LatticeAllStateField.wordField, actualField, VertexOperator.ncoeff_of_coeff,
      (actual_creation_coefficient_transport D a a).2.2.1]
    unfold rawSingle
    apply (matterSector D (a+b)).smul_mem
    exact ⟨_,rfl⟩
  | cons i tail ih =>
    rw [LatticeAllStateField.wordField, (normalMinusOne _ _).2]
    apply (matterSector D (a+b)).add_mem
    · apply finsum_induction (fun v => v ∈ matterSector D (a+b))
        (Submodule.zero_mem _) (fun _ _ hx hy => Submodule.add_mem _ hx hy)
      intro k
      exact derivative_charge D i _ (a+b) ⟨_,ih _ q⟩
    · apply finsum_induction (fun v => v ∈ matterSector D (a+b))
        (Submodule.zero_mem _) (fun _ _ hx hy => Submodule.add_mem _ hx hy)
      intro k
      have hin := derivative_charge D i (k:ℤ) b ⟨Finsupp.single b q,⟨q,rfl⟩⟩
      obtain ⟨r,hr⟩ := hin
      rw [← hr]
      exact ih _ r

private theorem matter_mode_charge (a b : Charge D) (p q : Oscillator D) (n : ℤ) :
    ((LatticeAllStateField.Y D (Finsupp.single a p))[[n]]) (Finsupp.single b q) ∈
      matterSector D (a+b) := by
  classical
  rw [LatticeAllStateField.Y_single, LatticeAllStateField.polynomialField,
    Module.Basis.constr_apply]
  simp only [Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  apply (matterSector D (a+b)).sum_mem
  intro e he
  exact (matterSector D (a+b)).smul_mem _
    (word_charge D a b (LatticeAllStateField.occurrences D e) n q)

private theorem tensor_sector (a : Charge D) (v : matterSector D a) (w : Fock) :
    (v : Carrier D) ⊗ₜ[ℂ] w ∈ fixedMomentum D a := by
  obtain ⟨p,hp⟩ := v.property
  rw [← hp]
  apply (mem_fixedMomentum_iff D a _).mpr
  rintro ⟨⟨b,e⟩,S⟩ hb
  rw [coeff_tmul_original]
  simp [Ne.symm hb]

private theorem tensor_mode_charge (a b : Charge D) (p q : Oscillator D)
    (u v : Fock) (n : ℤ) :
    originalMode D n (Finsupp.single a p ⊗ₜ[ℂ] u) (Finsupp.single b q ⊗ₜ[ℂ] v) ∈
      fixedMomentum D (a+b) := by
  rw [originalMode_apply, Y_modes]
  simp only [term_tmul]
  apply finsum_induction (fun w => w ∈ fixedMomentum D (a+b))
    (Submodule.zero_mem _) (fun _ _ hx hy => Submodule.add_mem _ hx hy)
  intro k
  exact tensor_sector D (a+b) ⟨_,matter_mode_charge D a b p q k⟩ _

/-- Actual original-mode addition of original charges; no metric assumption is needed. -/
theorem originalMode_charge (a b : Charge D) (x y : State D) (n : ℤ)
    (hx : x ∈ fixedMomentum D a) (hy : y ∈ fixedMomentum D b) :
    originalMode D n x y ∈ fixedMomentum D (a+b) := by
  rw [fixedMomentum_eq_span] at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change i.1.1 = a at hi
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j,hj,rfl⟩ := hy
      change j.1.1 = b at hj
      rw [tensorBasis_apply, tensorBasis_apply]
      simpa only [hi,hj] using tensor_mode_charge D i.1.1 j.1.1
        (MvPolynomial.monomial i.1.2 1) (MvPolynomial.monomial j.1.2 1)
        (D5.S3.Quantum.Fermionic.CountableOccupationFock.ket i.2)
        (D5.S3.Quantum.Fermionic.CountableOccupationFock.ket j.2) n
    | zero => simpa only [map_zero] using (fixedMomentum D (a+b)).zero_mem
    | add y z hy hz iy iz =>
      rw [map_add]
      exact (fixedMomentum D (a+b)).add_mem iy iz
    | smul t y hy iy =>
      rw [map_smul]
      exact (fixedMomentum D (a+b)).smul_mem t iy
  | zero =>
    simp only [map_zero, LinearMap.zero_apply]
    exact (fixedMomentum D (a+b)).zero_mem
  | add x z hx hz ix iz =>
    rw [map_add, LinearMap.add_apply]
    exact (fixedMomentum D (a+b)).add_mem ix iz
  | smul t x hx ix =>
    rw [map_smul, LinearMap.smul_apply]
    exact (fixedMomentum D (a+b)).smul_mem t ix

private theorem b_charge (a : Charge D) (m : ℤ) (x : State D)
    (hx : x ∈ fixedMomentum D a) : ghostB D m x ∈ fixedMomentum D a := by
  rw [fixedMomentum_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change i.1.1 = a at hi
    rw [tensorBasis_apply]
    change TensorProduct.map LinearMap.id _ _ ∈ _
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    simpa only [hi] using tensor_sector D i.1.1
      ⟨Finsupp.single i.1.1 (MvPolynomial.monomial i.1.2 1),
        ⟨MvPolynomial.monomial i.1.2 1,rfl⟩⟩
      (D5.S3.Quantum.Fermionic.BcGhostFock.b m
        (D5.S3.Quantum.Fermionic.CountableOccupationFock.ket i.2))
  | zero => simpa only [map_zero] using (fixedMomentum D a).zero_mem
  | add x y hx hy ix iy =>
    rw [map_add]
    exact (fixedMomentum D a).add_mem ix iy
  | smul t x hx ix =>
    rw [map_smul]
    exact (fixedMomentum D a).smul_mem t ix

/-- The literal descent current adds ORIGINAL charges, including neutral output. -/
theorem current_charge (a b : Charge D) (x y : State D)
    (hx : x ∈ fixedMomentum D a) (hy : y ∈ fixedMomentum D b) :
    descentCurrent D x y ∈ fixedMomentum D (a+b) :=
  originalMode_charge D a b (ghostB D (-1) x) y 0 (b_charge D a (-1) x hx) hy

variable (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

private theorem closed_relative_energy (x : State D)
    (qx : LatticeBRST.totalCharge D H x = 0) (bx : ghostB D 0 x = 0) :
    LatticeBRSTZeroEnergyReduction.totalL0 D H x = 0 := by
  have h := LinearMap.congr_fun (LatticeBRST.total_ward_b D H 0) x
  change LatticeBRST.totalCharge D H (ghostB D 0 x) +
    ghostB D 0 (LatticeBRST.totalCharge D H x) =
      LatticeBRSTZeroEnergyReduction.totalL0 D H x at h
  simpa only [qx,bx,map_zero,add_zero] using h.symm

private def fixedStateInclusion (a : Charge D) (level : ℤ) :
    LatticeBRSTPhysicalPairing.physicalCycles H a level →ₗ[ℂ] physicalStates D H where
  toFun x := ⟨x.val.val, x.property.1, x.property.2.1, x.property.2.2,
    closed_relative_energy D H x.val.val x.property.1 x.property.2.1⟩
  map_add' x y := rfl
  map_smul' t x := rfl

private theorem chargeProject_fixed_iff (a : Charge D) (x : State D) :
    chargeProject a x = x ↔ x ∈ fixedMomentum D a := by
  classical
  have proj : chargeProject a x ∈ fixedMomentum D a := by
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      change Finsupp.single a (v a) ⊗ₜ[ℂ] w ∈ _
      exact tensor_sector D a ⟨_,⟨_,rfl⟩⟩ w
    | add x y hx hy =>
      rw [map_add]
      exact (fixedMomentum D a).add_mem hx hy
  constructor
  · intro hx
    rwa [hx] at proj
  · intro hx
    clear proj
    rw [fixedMomentum_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      change i.1.1 = a at hi
      rw [tensorBasis_apply]
      change Finsupp.single a ((Finsupp.single i.1.1 _ : Carrier D) a) ⊗ₜ[ℂ] _ = _
      simp [hi]
    | zero => exact map_zero _
    | add x y hx hy ix iy => rw [map_add,ix,iy]
    | smul t x hx ix => rw [map_smul,ix]

include hHG hGH in
/-- The exact shell level of the output is determined by its SUM charge.
It is NOT the sum of oscillator levels: the lattice bilinear cross term matters. -/
theorem physical_current_fixedSector (a b : Charge D) (la lb lc : ℤ)
    (x : LatticeBRSTPhysicalPairing.physicalCycles H a la)
    (y : LatticeBRSTPhysicalPairing.physicalCycles H b lb)
    (shell : groundEnergy (a+b) + (lc:ℂ) - 1 = 0) :
    descentCurrent D x.val.val y.val.val ∈ fixedSector H (a+b) lc := by
  have ca := (chargeProject_fixed_iff D a x.val.val).mp x.val.property.1
  have cb := (chargeProject_fixed_iff D b y.val.val).mp y.val.property.1
  refine ⟨(chargeProject_fixed_iff D (a+b) _).mpr (current_charge D a b _ _ ca cb), ?_⟩
  have energy := LatticeBRSTCurrentIdentities.current_zero_energy D H hHG hGH
    (LatticeBRSTPhysicalPairing.cycleInclusion H a la x)
    (LatticeBRSTPhysicalPairing.cycleInclusion H b lb y) x.property.2.1 y.property.2.1
  rw [shell,zero_smul]
  exact energy

/-- Fixed physical representatives give the actual sum-charge physical class,
and its global class is the existing independently descended current. -/
theorem fixed_physical_current (a b : Charge D) (la lb lc : ℤ)
    (x : LatticeBRSTPhysicalPairing.physicalCycles H a la)
    (y : LatticeBRSTPhysicalPairing.physicalCycles H b lb)
    (shell : groundEnergy (a+b) + (lc:ℂ) - 1 = 0) :
    ∃ z : LatticeBRSTPhysicalPairing.physicalCycles H (a+b) lc,
      z.val.val = descentCurrent D x.val.val y.val.val ∧
      LatticeBRSTPhysicalPairing.physicalClass H (a+b) lc h26 hHG hGH z =
        cohomologyCurrent D H h26 hHG hGH
          (LatticeBRSTPhysicalPairing.physicalClass H a la h26 hHG hGH x)
          (LatticeBRSTPhysicalPairing.physicalClass H b lb h26 hHG hGH y) := by
  have h := LatticeBRSTPhysicalLie.physicalStates_current D H hHG hGH
    (fixedStateInclusion D H a la x) (fixedStateInclusion D H b lb y)
  refine ⟨⟨⟨descentCurrent D x.val.val y.val.val,
    physical_current_fixedSector D H hHG hGH a b la lb lc x y shell⟩,
      h.1,h.2.1,h.2.2.1⟩,rfl,?_⟩
  rfl

/-- The original quadratic charge energy retains the bilinear cross term. -/
private theorem groundEnergy_add (a b : Charge D) :
    groundEnergy (a+b) = groundEnergy a + groundEnergy b + (bilinear D a b : ℂ) := by
  have expand : bilinear D (a+b) (a+b) =
      bilinear D a a + bilinear D b b + 2 * bilinear D a b := by
    rw [LatticeActualGeneratorLocality.bilinear_add_right,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D (a+b) a,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D (a+b) b,
      LatticeActualGeneratorLocality.bilinear_add_right,
      LatticeActualGeneratorLocality.bilinear_add_right,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D b a]
    ring
  unfold groundEnergy
  rw [expand]
  push_cast
  ring

/-- Charge-graded multiplication of the EXISTING fixed-sector global images,
with the exact output level la+lb-1-(a,b). Zero sum-charge is permitted. -/
theorem fixedImage_current_addition (a b : Charge D) (la lb : ℤ)
    (sa : groundEnergy a + (la:ℂ) - 1 = 0)
    (sb : groundEnergy b + (lb:ℂ) - 1 = 0)
    (u v : Cohomology D H h26 hHG hGH)
    (hu : u ∈ LatticeBRSTPhysicalPairing.physicalImage H a la h26 hHG hGH)
    (hv : v ∈ LatticeBRSTPhysicalPairing.physicalImage H b lb h26 hHG hGH) :
    cohomologyCurrent D H h26 hHG hGH u v ∈
      LatticeBRSTPhysicalPairing.physicalImage H (a+b)
        (la+lb-1-bilinear D a b) h26 hHG hGH := by
  obtain ⟨x,rfl⟩ := hu
  obtain ⟨y,rfl⟩ := hv
  have shell : groundEnergy (a+b) + ((la+lb-1-bilinear D a b:ℤ):ℂ) - 1 = 0 := by
    rw [groundEnergy_add]
    push_cast
    linear_combination sa + sb
  obtain ⟨z,hz,hclass⟩ := fixed_physical_current D H h26 hHG hGH
    a b la lb (la+lb-1-bilinear D a b) x y shell
  exact ⟨z,hclass⟩

end
end D5.S3.VertexAlgebra.LatticeBRSTPhysicalLieSectors
