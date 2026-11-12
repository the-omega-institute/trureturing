/- GID: D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTChargeCohomology
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTChargeCohomology
   mirror-E: none(waiver:algebraic-original-brst-charge-assembly)
   anchors: []
   utility: none
   digest: The canonical original BRST quotient is the algebraic direct sum of its genuine fixed-charge quotients. -/

/- The original lattice, tensor-state and BRST suppliers retain their
Bakalov--Kac, Scott Carnahan and Kalle Kytölä attribution. The direct-sum,
Finsupp, basis and quotient machinery is Mathlib's (in particular Kenny Lau,
Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov).
No literature novelty or physical classification is asserted.

Source checkpoint only: this file has not been natively elaborated. -/

import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyField
import D5.S3.VertexAlgebra.Lattice.LatticeRelativeMassShell
import D5.S3.VertexAlgebra.Lattice.LatticeQuartetContraction
import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators TensorProduct DirectSum

namespace D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeMatterGhostCoupling (State)
open LatticeRelativeMassShell
  (TensorLabel tensorBasis tensorBasis_apply tensorCoeffEquiv coeff
    coeff_tmul_original fixedMomentum mem_fixedMomentum_iff
    fixedMomentum_eq_span totalCharge_mem_fixedMomentum)
open LatticeQuartetContraction (chargeProject)
open D5.S3.Quantum.Fermionic.CountableOccupationFock (Fock)

noncomputable section

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

private def coefficientLinear (i : TensorLabel D) : State D →ₗ[ℂ] ℂ :=
  (Finsupp.lapply i).comp (tensorCoeffEquiv D).toLinearMap

private theorem coefficient_zero (i : TensorLabel D) : coeff D 0 i = 0 :=
  (coefficientLinear D i).map_zero

private theorem coefficient_add (x y : State D) (i : TensorLabel D) :
    coeff D (x + y) i = coeff D x i + coeff D y i :=
  (coefficientLinear D i).map_add x y

private theorem original_expansion (x : State D) :
    (∑ i ∈ (tensorCoeffEquiv D x).support, coeff D x i • tensorBasis D i) = x := by
  simpa [coeff, tensorCoeffEquiv, Finsupp.linearCombination_apply, Finsupp.sum] using
    (tensorBasis D).linearCombination_repr x

/-- The finite set is read from literal ORIGINAL tensor coefficients. -/
def chargeSupport (x : State D) : Finset (Charge D) := by
  classical
  exact (tensorCoeffEquiv D x).support.image (fun i => i.1.1)

private theorem chargeProject_tmul (p : Charge D) (v : Carrier D) (w : Fock) :
    chargeProject p (v ⊗ₜ[ℂ] w) = Finsupp.single p (v p) ⊗ₜ[ℂ] w := by
  change TensorProduct.map ((Finsupp.lsingle p).comp (Finsupp.lapply p))
    (LinearMap.id : Fock →ₗ[ℂ] Fock) (v ⊗ₜ[ℂ] w) = _
  rw [TensorProduct.map_tmul]
  rfl

private theorem chargeProject_tensorBasis (p : Charge D) (i : TensorLabel D) :
    chargeProject p (tensorBasis D i) =
      if i.1.1 = p then tensorBasis D i else 0 := by
  classical
  rw [tensorBasis_apply, chargeProject_tmul]
  by_cases h : i.1.1 = p
  · simp [h]
  · simp [h, Ne.symm h]

/-- Premise-free coefficient action of the EXISTING projector; no frame is chosen. -/
theorem chargeProject_coeff (p : Charge D) (x : State D) (i : TensorLabel D) :
    coeff D (chargeProject p x) i = if i.1.1 = p then coeff D x i else 0 := by
  classical
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      rcases i with ⟨⟨q, d⟩, S⟩
      rw [chargeProject_tmul, coeff_tmul_original, coeff_tmul_original]
      by_cases h : q = p
      · subst q
        simp
      · simp [h, Ne.symm h]
  | add x y hx hy =>
      rw [map_add, coefficient_add, coefficient_add, hx, hy]
      split_ifs <;> simp

private theorem chargeProject_mem (p : Charge D) (x : State D) :
    chargeProject p x ∈ fixedMomentum D p := by
  apply (mem_fixedMomentum_iff D p _).mpr
  intro i hi
  rw [chargeProject_coeff, if_neg hi]

/-- The existing projector fixes every state in the literal full charge sector. -/
theorem chargeProject_fixed (p : Charge D) (x : State D)
    (hx : x ∈ fixedMomentum D p) : chargeProject p x = x := by
  classical
  apply (tensorCoeffEquiv D).injective
  ext i
  change coeff D (chargeProject p x) i = coeff D x i
  rw [chargeProject_coeff]
  by_cases hi : i.1.1 = p
  · simp [hi]
  · simp [hi, (mem_fixedMomentum_iff D p x).mp hx i hi]

private theorem chargeProject_on_fixed (p q : Charge D) (x : State D)
    (hx : x ∈ fixedMomentum D q) :
    chargeProject p x = if q = p then x else 0 := by
  classical
  by_cases h : q = p
  · subst q
    simpa using chargeProject_fixed D p x hx
  · rw [if_neg h]
    apply (tensorCoeffEquiv D).injective
    ext i
    change coeff D (chargeProject p x) i = coeff D 0 i
    rw [chargeProject_coeff, coefficient_zero]
    by_cases hi : i.1.1 = p
    · have hq : i.1.1 ≠ q := fun e => h (e.symm.trans hi)
      simp [hi, (mem_fixedMomentum_iff D q x).mp hx i hq]
    · simp [hi]

private theorem tensorBasis_mem (i : TensorLabel D) :
    tensorBasis D i ∈ fixedMomentum D i.1.1 := by
  rw [fixedMomentum_eq_span]
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

/-- Vanishing outside support is proved from the original Finsupp coordinates. -/
theorem chargeProject_eq_zero_of_not_mem (x : State D) (p : Charge D)
    (hp : p ∉ chargeSupport D x) : chargeProject p x = 0 := by
  classical
  apply (tensorCoeffEquiv D).injective
  ext i
  change coeff D (chargeProject p x) i = coeff D 0 i
  rw [chargeProject_coeff, coefficient_zero]
  by_cases hi : i.1.1 = p
  · have hn : i ∉ (tensorCoeffEquiv D x).support := by
      intro hmem
      exact hp (Finset.mem_image.mpr ⟨i, hmem, hi⟩)
    have hz : coeff D x i = 0 := Finsupp.notMem_support_iff.mp hn
    simp [hi, hz]
  · simp [hi]

/-- Every original state has this finite, all-charge decomposition. -/
theorem sum_chargeProject (x : State D) :
    (∑ p ∈ chargeSupport D x, chargeProject p x) = x := by
  classical
  apply (tensorCoeffEquiv D).injective
  ext i
  change coefficientLinear D i (∑ p ∈ chargeSupport D x, chargeProject p x) =
    coefficientLinear D i x
  rw [map_sum]
  change (∑ p ∈ chargeSupport D x, coeff D (chargeProject p x) i) = coeff D x i
  simp only [chargeProject_coeff]
  by_cases hi : coeff D x i = 0
  · simp [hi]
  · have hp : i.1.1 ∈ chargeSupport D x :=
      Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩
    rw [Finset.sum_eq_single i.1.1]
    · simp
    · intro p _ hpi
      simp [Ne.symm hpi]
    · intro hn
      exact False.elim (hn hp)

/-- Actual Q/projector commutation, derived from preservation and finite expansion. -/
theorem chargeProject_commutes (p : Charge D) (x : State D) :
    chargeProject p (LatticeBRST.totalCharge D H x) =
      LatticeBRST.totalCharge D H (chargeProject p x) := by
  classical
  have hb (i : TensorLabel D) :
      chargeProject p (LatticeBRST.totalCharge D H (tensorBasis D i)) =
        LatticeBRST.totalCharge D H (chargeProject p (tensorBasis D i)) := by
    rw [chargeProject_on_fixed D p i.1.1 _
      (totalCharge_mem_fixedMomentum D H i.1.1 (tensorBasis_mem D i)),
      chargeProject_tensorBasis]
    by_cases hi : i.1.1 = p <;> simp [hi]
  calc
    _ = chargeProject p (LatticeBRST.totalCharge D H
        (∑ i ∈ (tensorCoeffEquiv D x).support, coeff D x i • tensorBasis D i)) :=
      congrArg (fun z => chargeProject p (LatticeBRST.totalCharge D H z))
        (original_expansion D x).symm
    _ = LatticeBRST.totalCharge D H (chargeProject p
        (∑ i ∈ (tensorCoeffEquiv D x).support, coeff D x i • tensorBasis D i)) := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      rw [hb]
    _ = _ := by rw [original_expansion D x]

/-- Q restricted to the actual full fixedMomentum submodule. -/
def sectorQ (p : Charge D) : Module.End ℂ (fixedMomentum D p) :=
  ((LatticeBRST.totalCharge D H).comp (fixedMomentum D p).subtype).codRestrict
    (fixedMomentum D p) (fun x => totalCharge_mem_fixedMomentum D H p x.property)

@[simp] theorem sectorQ_val (p : Charge D) (x : fixedMomentum D p) :
    (sectorQ D H p x : State D) = LatticeBRST.totalCharge D H (x : State D) := rfl

abbrev sectorCycles (p : Charge D) := LinearMap.ker (sectorQ D H p)

private def sectorProjection (p : Charge D) : State D →ₗ[ℂ] fixedMomentum D p :=
  (chargeProject p).codRestrict (fixedMomentum D p) (chargeProject_mem D p)

/-- Inclusion into the EXISTING canonical cycle space. -/
def cycleInclusion (p : Charge D) :
    sectorCycles D H p →ₗ[ℂ] LatticeBRSTCohomologyField.cycles D H where
  toFun x := ⟨(x.1 : State D), congrArg Subtype.val x.property⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- Original charge projection, with both actual kernel and sector membership proofs. -/
def cycleProjection (p : Charge D) :
    LatticeBRSTCohomologyField.cycles D H →ₗ[ℂ] sectorCycles D H p where
  toFun a := ⟨sectorProjection D p a, by
    apply Subtype.ext
    change LatticeBRST.totalCharge D H (chargeProject p (a : State D)) = 0
    rw [← chargeProject_commutes D H,
      show LatticeBRST.totalCharge D H (a : State D) = 0 from a.property, map_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact (chargeProject p).map_add (a : State D) (b : State D)
  map_smul' z a := by
    apply Subtype.ext
    apply Subtype.ext
    exact (chargeProject p).map_smul z (a : State D)

@[simp] theorem cycleInclusion_val (p : Charge D) (x : sectorCycles D H p) :
    (cycleInclusion D H p x : State D) = (x.1 : State D) := rfl

@[simp] theorem cycleProjection_val (p : Charge D)
    (a : LatticeBRSTCohomologyField.cycles D H) :
    ((cycleProjection D H p a).1 : State D) = chargeProject p (a : State D) := rfl

private theorem cycleProjection_zero_of_outside
    (a : LatticeBRSTCohomologyField.cycles D H) (p : Charge D)
    (hp : p ∉ chargeSupport D (a : State D)) : cycleProjection D H p a = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact chargeProject_eq_zero_of_not_mem D (a : State D) p hp

variable (h26 : D.rank = 26)
  (hHG : H * LatticeSugawaraCurrents.gramComplex D = 1)
  (hGH : LatticeSugawaraCurrents.gramComplex D * H = 1)

/-- Actual restricted Q into its actual kernel. Square-zero is reused from the
canonical full boundaryMap; no anomaly, derivation or BRST square is reproved. -/
def sectorBoundaryMap (p : Charge D) :
    fixedMomentum D p →ₗ[ℂ] sectorCycles D H p :=
  (sectorQ D H p).codRestrict (sectorCycles D H p) (by
    intro x
    apply Subtype.ext
    exact (LatticeBRSTCohomologyField.boundaryMap D H h26 hHG hGH (x : State D)).property)

/-- A genuine image of restricted Q, with primitives IN fixedMomentum. -/
def sectorBoundaries (p : Charge D) : Submodule ℂ (sectorCycles D H p) :=
  LinearMap.range (sectorBoundaryMap D H h26 hHG hGH p)

theorem mem_sectorBoundaries (p : Charge D) (x : sectorCycles D H p) :
    x ∈ sectorBoundaries D H h26 hHG hGH p ↔
      ∃ y : fixedMomentum D p, sectorQ D H p y = x.1 := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

local instance : AddCommGroup (Carrier D) := inferInstance
local instance : AddCommGroup (State D) := inferInstance
local instance (p : Charge D) : AddCommGroup (fixedMomentum D p) := inferInstance
local instance (p : Charge D) : AddCommGroup (sectorCycles D H p) := inferInstance

abbrev SectorCohomology (p : Charge D) :=
  sectorCycles D H p ⧸ sectorBoundaries D H h26 hHG hGH p

def sectorClassOf (p : Charge D) :
    sectorCycles D H p →ₗ[ℂ] SectorCohomology D H h26 hHG hGH p :=
  (sectorBoundaries D H h26 hHG hGH p).mkQ

theorem sectorClassOf_surjective (p : Charge D) :
    Function.Surjective (sectorClassOf D H h26 hHG hGH p) :=
  (sectorBoundaries D H h26 hHG hGH p).mkQ_surjective

theorem sectorClassOf_eq_zero (p : Charge D) (x : sectorCycles D H p) :
    sectorClassOf D H h26 hHG hGH p x = 0 ↔
      ∃ y : fixedMomentum D p, sectorQ D H p y = x.1 :=
  (Submodule.Quotient.mk_eq_zero _).trans
    (mem_sectorBoundaries D H h26 hHG hGH p x)

/-- The exact local-primitive bridge. An ambient witness y is replaced by the
literal original chargeProject p y, not by an intersection-of-ranges premise. -/
theorem globalClassOf_eq_zero_iff_local_primitive (p : Charge D)
    (x : sectorCycles D H p) :
    LatticeBRSTCohomologyField.classOf D H h26 hHG hGH (cycleInclusion D H p x) = 0 ↔
      ∃ y : fixedMomentum D p, sectorQ D H p y = x.1 := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ :=
      (LatticeBRSTCohomologyField.classOf_eq_zero D H h26 hHG hGH _).mp hx
    refine ⟨sectorProjection D p y, ?_⟩
    apply Subtype.ext
    change LatticeBRST.totalCharge D H (chargeProject p y) = (x.1 : State D)
    rw [← chargeProject_commutes D H, hy]
    exact chargeProject_fixed D p (x.1 : State D) x.1.property
  · rintro ⟨y, hy⟩
    apply (LatticeBRSTCohomologyField.classOf_eq_zero D H h26 hHG hGH _).mpr
    exact ⟨(y : State D), congrArg Subtype.val hy⟩

private theorem cycleInclusion_boundary (p : Charge D) (x : sectorCycles D H p)
    (hx : x ∈ sectorBoundaries D H h26 hHG hGH p) :
    cycleInclusion D H p x ∈ LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH := by
  obtain ⟨y, hy⟩ := (mem_sectorBoundaries D H h26 hHG hGH p x).mp hx
  apply (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH _).mpr
  exact ⟨(y : State D), congrArg Subtype.val hy⟩

private theorem cycleProjection_boundary (p : Charge D)
    (a : LatticeBRSTCohomologyField.cycles D H)
    (ha : a ∈ LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH) :
    cycleProjection D H p a ∈ sectorBoundaries D H h26 hHG hGH p := by
  obtain ⟨y, hy⟩ :=
    (LatticeBRSTCohomologyField.mem_boundaries D H h26 hHG hGH a).mp ha
  apply (mem_sectorBoundaries D H h26 hHG hGH p _).mpr
  refine ⟨sectorProjection D p y, ?_⟩
  apply Subtype.ext
  change LatticeBRST.totalCharge D H (chargeProject p y) = chargeProject p (a : State D)
  rw [← chargeProject_commutes D H, hy]

/-- Descent to the literal existing full quotient. -/
def inclusion (p : Charge D) :
    SectorCohomology D H h26 hHG hGH p →ₗ[ℂ]
      LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH :=
  (sectorBoundaries D H h26 hHG hGH p).mapQ
    (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH)
    (cycleInclusion D H p) (cycleInclusion_boundary D H h26 hHG hGH p)

/-- Descent of the actual chargeProject, not an assumed graded-cohomology map. -/
def projection (p : Charge D) :
    LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH →ₗ[ℂ]
      SectorCohomology D H h26 hHG hGH p :=
  (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH).mapQ
    (sectorBoundaries D H h26 hHG hGH p)
    (cycleProjection D H p) (cycleProjection_boundary D H h26 hHG hGH p)

@[simp] theorem inclusion_sectorClassOf (p : Charge D) (x : sectorCycles D H p) :
    inclusion D H h26 hHG hGH p (sectorClassOf D H h26 hHG hGH p x) =
      LatticeBRSTCohomologyField.classOf D H h26 hHG hGH (cycleInclusion D H p x) := rfl

@[simp] theorem projection_classOf (p : Charge D)
    (a : LatticeBRSTCohomologyField.cycles D H) :
    projection D H h26 hHG hGH p (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a) =
      sectorClassOf D H h26 hHG hGH p (cycleProjection D H p a) := rfl

private theorem inclusion_eq_zero_iff (p : Charge D)
    (a : SectorCohomology D H h26 hHG hGH p) :
    inclusion D H h26 hHG hGH p a = 0 ↔ a = 0 := by
  obtain ⟨x, rfl⟩ := sectorClassOf_surjective D H h26 hHG hGH p a
  rw [inclusion_sectorClassOf, globalClassOf_eq_zero_iff_local_primitive,
    sectorClassOf_eq_zero]

/-- Injectivity uses the actual projected-primitive bridge. -/
theorem inclusion_injective (p : Charge D) :
    Function.Injective (inclusion D H h26 hHG hGH p) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (inclusion_eq_zero_iff D H h26 hHG hGH p (a - b)).mp
  rw [map_sub, hab, sub_self]

/-- Conversely, actual local primitives over the finite original charge support
sum to an actual original preimage. There is no assumed finite charge set. -/
theorem classOf_eq_zero_iff_components
    (a : LatticeBRSTCohomologyField.cycles D H) :
    LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a = 0 ↔
      ∀ p : Charge D,
        sectorClassOf D H h26 hHG hGH p (cycleProjection D H p a) = 0 := by
  classical
  constructor
  · intro ha p
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    apply cycleProjection_boundary D H h26 hHG hGH p a
    exact (Submodule.Quotient.mk_eq_zero _).mp ha
  · intro ha
    choose y hy using fun p =>
      (sectorClassOf_eq_zero D H h26 hHG hGH p (cycleProjection D H p a)).mp (ha p)
    apply (LatticeBRSTCohomologyField.classOf_eq_zero D H h26 hHG hGH a).mpr
    refine ⟨∑ p ∈ chargeSupport D (a : State D), (y p : State D), ?_⟩
    calc
      _ = ∑ p ∈ chargeSupport D (a : State D), chargeProject p (a : State D) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro p _
        exact congrArg Subtype.val (hy p)
      _ = (a : State D) := sum_chargeProject D (a : State D)

private def splitCyclesValue (a : LatticeBRSTCohomologyField.cycles D H) :
    ⨁ p : Charge D, sectorCycles D H p := by
  classical
  exact DFinsupp.mk (β := fun p : Charge D => sectorCycles D H p)
    (chargeSupport D (a : State D))
    (fun p => cycleProjection D H p.1 a)

private theorem splitCyclesValue_apply (a : LatticeBRSTCohomologyField.cycles D H)
    (p : Charge D) : splitCyclesValue D H a p = cycleProjection D H p a := by
  classical
  by_cases hp : p ∈ chargeSupport D (a : State D)
  · exact DFinsupp.mk_of_mem hp
  · change DFinsupp.mk (β := fun p : Charge D => sectorCycles D H p)
      (chargeSupport D (a : State D))
      (fun p => cycleProjection D H p.1 a) p = _
    rw [DFinsupp.mk_of_notMem hp]
    exact (cycleProjection_zero_of_outside D H a p hp).symm

private def splitCycles : LatticeBRSTCohomologyField.cycles D H →ₗ[ℂ]
    ⨁ p : Charge D, sectorCycles D H p where
  toFun := splitCyclesValue D H
  map_add' a b := by
    apply DFinsupp.ext
    intro p
    change splitCyclesValue D H (a + b) p =
      splitCyclesValue D H a p + splitCyclesValue D H b p
    simp only [splitCyclesValue_apply, DFinsupp.add_apply]
    exact (cycleProjection D H p).map_add a b
  map_smul' z a := by
    apply DFinsupp.ext
    intro p
    change splitCyclesValue D H (z • a) p = z • splitCyclesValue D H a p
    simp only [splitCyclesValue_apply, DFinsupp.smul_apply]
    exact (cycleProjection D H p).map_smul z a

private def splitClasses : LatticeBRSTCohomologyField.cycles D H →ₗ[ℂ]
    ⨁ p : Charge D, SectorCohomology D H h26 hHG hGH p :=
  (DirectSum.lmap (fun p => sectorClassOf D H h26 hHG hGH p)).comp (splitCycles D H)

/-- The finite-support decomposition DESCENDS from the original canonical quotient. -/
def decompose :
    LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH →ₗ[ℂ]
      ⨁ p : Charge D, SectorCohomology D H h26 hHG hGH p :=
  (LatticeBRSTCohomologyField.boundaries D H h26 hHG hGH).liftQ
    (splitClasses D H h26 hHG hGH) (by
      intro a ha
      change splitClasses D H h26 hHG hGH a = 0
      apply DFinsupp.ext
      intro p
      change sectorClassOf D H h26 hHG hGH p (splitCyclesValue D H a p) = 0
      rw [splitCyclesValue_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (cycleProjection_boundary D H h26 hHG hGH p a ha))

/-- Assembly uses Mathlib's algebraic DirectSum.toModule on the actual inclusions. -/
def assemble :
    (⨁ p : Charge D, SectorCohomology D H h26 hHG hGH p) →ₗ[ℂ]
      LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH := by
  classical
  exact DirectSum.toModule ℂ (Charge D) _ (inclusion D H h26 hHG hGH)

@[simp] theorem decompose_classOf_component
    (a : LatticeBRSTCohomologyField.cycles D H) (p : Charge D) :
    DirectSum.component ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p
      (decompose D H h26 hHG hGH (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a)) =
        sectorClassOf D H h26 hHG hGH p (cycleProjection D H p a) := by
  change sectorClassOf D H h26 hHG hGH p (splitCyclesValue D H a p) = _
  rw [splitCyclesValue_apply]

/-- The component equation holds for arbitrary quotient classes. -/
theorem decompose_component
    (a : LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH) (p : Charge D) :
    DirectSum.component ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p
      (decompose D H h26 hHG hGH a) = projection D H h26 hHG hGH p a := by
  obtain ⟨x, rfl⟩ := LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH a
  rw [decompose_classOf_component, projection_classOf]

attribute [local instance] Classical.propDecidable

/-- Support of the quotient decomposition is bounded by ANY given literal cycle lift. -/
theorem decompose_support_subset (a : LatticeBRSTCohomologyField.cycles D H) :
    (decompose D H h26 hHG hGH
      (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a)).support ⊆
        chargeSupport D (a : State D) := by
  classical
  intro p hp
  by_contra hn
  have hz : decompose D H h26 hHG hGH
      (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a) p = 0 := by
    change DirectSum.component ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p
      (decompose D H h26 hHG hGH
        (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a)) = 0
    rw [decompose_classOf_component, cycleProjection_zero_of_outside D H a p hn, map_zero]
  exact (DFinsupp.notMem_support_iff.mpr hz) hp

@[simp] theorem assemble_lof (p : Charge D)
    (a : SectorCohomology D H h26 hHG hGH p) :
    assemble D H h26 hHG hGH
      (DirectSum.lof ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p a) =
        inclusion D H h26 hHG hGH p a := by
  classical
  exact DirectSum.toModule_lof ℂ p a

private theorem decompose_inclusion (p : Charge D)
    (a : SectorCohomology D H h26 hHG hGH p) :
    decompose D H h26 hHG hGH (inclusion D H h26 hHG hGH p a) =
      DirectSum.lof ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p a := by
  classical
  obtain ⟨x, rfl⟩ := sectorClassOf_surjective D H h26 hHG hGH p a
  rw [inclusion_sectorClassOf]
  apply DirectSum.ext_component ℂ
  intro q
  rw [decompose_classOf_component]
  by_cases hpq : p = q
  · subst q
    rw [DirectSum.component.lof_self]
    apply congrArg (sectorClassOf D H h26 hHG hGH p)
    apply Subtype.ext
    apply Subtype.ext
    exact chargeProject_fixed D p (x.1 : State D) x.1.property
  · rw [DirectSum.component.of]
    simp only [hpq, dite_false]
    have hz : cycleProjection D H q (cycleInclusion D H p x) = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      change chargeProject q (x.1 : State D) = 0
      simpa only [if_neg hpq] using
        chargeProject_on_fixed D q p (x.1 : State D) x.1.property
    rw [hz, map_zero]

private theorem decompose_assemble
    (a : ⨁ p : Charge D, SectorCohomology D H h26 hHG hGH p) :
    decompose D H h26 hHG hGH (assemble D H h26 hHG hGH a) = a := by
  classical
  have he : (decompose D H h26 hHG hGH).comp (assemble D H h26 hHG hGH) =
      LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    change decompose D H h26 hHG hGH
      (assemble D H h26 hHG hGH
        (DirectSum.lof ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p x)) =
      DirectSum.lof ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p x
    rw [assemble_lof, decompose_inclusion]
  exact LinearMap.congr_fun he a

private theorem decompose_injective :
    Function.Injective (decompose D H h26 hHG hGH) := by
  intro a b hab
  apply sub_eq_zero.mp
  obtain ⟨x, hx⟩ :=
    LatticeBRSTCohomologyField.classOf_surjective D H h26 hHG hGH (a - b)
  rw [← hx]
  apply (classOf_eq_zero_iff_components D H h26 hHG hGH x).mpr
  intro p
  have hz : decompose D H h26 hHG hGH
      (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH x) = 0 := by
    rw [hx, map_sub, hab, sub_self]
  have hp := congrArg
    (DirectSum.component ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p) hz
  simpa only [decompose_classOf_component, map_zero] using hp

private theorem assemble_decompose
    (a : LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH) :
    assemble D H h26 hHG hGH (decompose D H h26 hHG hGH a) = a := by
  apply decompose_injective D H h26 hHG hGH
  exact decompose_assemble D H h26 hHG hGH (decompose D H h26 hHG hGH a)

/-- ALL original charges, all original oscillator and ghost occupations, and
both zero modes. The left quotient is literally the canonical supplier quotient.
The right quotients are actual ker(sectorQ)/range(sectorQ into ker), with
fixedMomentum primitives. Only the supplier's critical and two inverse-Gram
hypotheses are used. This is assembly, without a sector classification. -/
def allChargeEquiv :
    LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH ≃ₗ[ℂ]
      ⨁ p : Charge D, SectorCohomology D H h26 hHG hGH p where
  toFun := decompose D H h26 hHG hGH
  invFun := assemble D H h26 hHG hGH
  left_inv := assemble_decompose D H h26 hHG hGH
  right_inv := decompose_assemble D H h26 hHG hGH
  map_add' := (decompose D H h26 hHG hGH).map_add
  map_smul' := (decompose D H h26 hHG hGH).map_smul

/-- Concrete readout: charge projection of an actual canonical cycle lift. -/
theorem allChargeEquiv_component_classOf
    (a : LatticeBRSTCohomologyField.cycles D H) (p : Charge D) :
    DirectSum.component ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p
      (allChargeEquiv D H h26 hHG hGH
        (LatticeBRSTCohomologyField.classOf D H h26 hHG hGH a)) =
      sectorClassOf D H h26 hHG hGH p (cycleProjection D H p a) :=
  decompose_classOf_component D H h26 hHG hGH a p

/-- Concrete inverse readout: inclusion of a genuine fixed-sector cycle class. -/
theorem allChargeEquiv_symm_lof_sectorClassOf (p : Charge D)
    (x : sectorCycles D H p) :
    (allChargeEquiv D H h26 hHG hGH).symm
      (DirectSum.lof ℂ (Charge D) (SectorCohomology D H h26 hHG hGH) p
        (sectorClassOf D H h26 hHG hGH p x)) =
      LatticeBRSTCohomologyField.classOf D H h26 hHG hGH (cycleInclusion D H p x) := by
  change assemble D H h26 hHG hGH _ = _
  rw [assemble_lof, inclusion_sectorClassOf]

end
end D5.S3.VertexAlgebra.Lattice.PhysicalLie.LatticeBRSTChargeCohomology
