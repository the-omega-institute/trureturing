/- GID: D5/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedRelativePositive
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/OriginalOrbifoldClosedRelativePositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical tensor classes and the positive double-relative Hermitian pairing. -/

import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalReal
import D5.S3.VertexAlgebra.BRST.OriginalOrbifoldClosedRelativeKunneth
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.RingTheory.Flat.Basic
import Batteries.Tactic.OpenPrivate

/-!
# The positive physical image in original orbifold double-relative BRST cohomology

Both factors impose the native chiral conditions `b₀ = L₀ = 0`.
The pairing lives on the image of the two specified physical momenta in
the double-relative cohomology. Its pure-class values use the two native
chain-conjugation and contravariant BPZ pairings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.OriginalOrbifoldClosedRelativePositive

open D5.S3.HomologicalAlgebra
open D5.S3.HomologicalAlgebra.FinitePerturbation (boundaryMap)
open OriginalOrbifoldCriticalMatter (Matter State Q hyperbolicData)
open OriginalOrbifoldBRSTSignedLocality (parity)
open OriginalOrbifoldBRSTDescent
  (relativeStates relativeDifferential relativeCycles relativeBoundaries RelativeCohomology)
open OriginalOrbifoldClosedRelativeKunneth
open OriginalOrbifoldBRSTPhysicalLie (N grade)
open OriginalOrbifoldBRSTMomentum (physicalMomentum mem_physicalMomentum_iff)
open OriginalOrbifoldBRSTPhysicalReal
  (canonicalPhysicalHermitian canonicalPhysicalHermitian_conj_symm
    canonicalPhysicalHermitian_positive)
open OriginalOrbifoldRelativeMassShell (fixedMomentum)
open OriginalOrbifoldBRSTZeroEnergy (fullBasis)
open LatticePositiveEnergy (chargeEnergy)

open private relativeNumber number_basis parity_basis from
  D5.S3.VertexAlgebra.BRST.OriginalOrbifoldBRSTPhysicalLie

noncomputable section

local instance : AddCommGroup State := TensorProduct.addCommGroup (M := Matter)

private abbrev UCharge := LatticeGeneratingFieldLocality.Charge hyperbolicData
local notation "V" => relativeStates
local notation "d" => relativeDifferential
local notation "σ" => chiralParity
local notation "qc" => closedRelativeBoundaries.mkQ

/-- The composite of the physical momentum and degree-one subtype inclusions. -/
def physicalInclusion (a : UCharge) : physicalMomentum a →ₗ[ℂ] RelativeCohomology :=
  (grade 1).subtype.comp (physicalMomentum a).subtype

theorem physicalInclusion_injective (a : UCharge) :
    Function.Injective (physicalInclusion a) :=
  (grade 1).subtype_injective.comp (physicalMomentum a).subtype_injective

abbrev PhysicalTensor (a b : UCharge) := physicalMomentum a ⊗[ℂ] physicalMomentum b

/-- Apply the two literal inclusions and the actual Künneth equivalence in this order. -/
def closedPhysicalEmbedding (a b : UCharge) :
    PhysicalTensor a b →ₗ[ℂ] ClosedRelativeCohomology :=
  kunnethEquiv.toLinearMap.comp (TensorProduct.map (physicalInclusion a) (physicalInclusion b))

theorem closedPhysicalEmbedding_injective (a b : UCharge) :
    Function.Injective (closedPhysicalEmbedding a b) :=
  kunnethEquiv.injective.comp
    (TensorProduct.map_injective_of_flat_flat (physicalInclusion a) (physicalInclusion b)
      (physicalInclusion_injective a) (physicalInclusion_injective b))

theorem closedPhysicalEmbedding_tmul_of_cycles (a b : UCharge)
    (x : physicalMomentum a) (y : physicalMomentum b) (u v : relativeCycles)
    (hu : relativeBoundaries.mkQ u = physicalInclusion a x)
    (hv : relativeBoundaries.mkQ v = physicalInclusion b y) :
    closedPhysicalEmbedding a b (x ⊗ₜ[ℂ] y) = qc (closedCycleTensor u v) := by
  simp only [closedPhysicalEmbedding, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, ← hu, ← hv]
  exact kunnethEquiv_classOf_tmul u v

/-- Each physical class has a representative of its specified momentum and ghost number one. -/
theorem physicalInclusion_cycle (a : UCharge) (x : physicalMomentum a) :
    ∃ u : relativeCycles, relativeBoundaries.mkQ u = physicalInclusion a x ∧
      (u.1 : State) ∈ fixedMomentum a ∧ N (u.1 : State) = (u.1 : State) :=
  (mem_physicalMomentum_iff a x.val).mp x.property

/-- The image is a submodule of the literal closed kernel modulo boundaries. -/
abbrev closedPhysicalImage (a b : UCharge) := LinearMap.range (closedPhysicalEmbedding a b)

def closedPhysicalImageEquiv (a b : UCharge) : PhysicalTensor a b ≃ₗ[ℂ] closedPhysicalImage a b :=
  LinearEquiv.ofInjective (closedPhysicalEmbedding a b) (closedPhysicalEmbedding_injective a b)

/-- The actual closed cycle class, as an element of the physical image. -/
def closedPhysicalCycleClass (a b : UCharge) (x : physicalMomentum a) (y : physicalMomentum b)
    (u v : relativeCycles)
    (hu : relativeBoundaries.mkQ u = physicalInclusion a x)
    (hv : relativeBoundaries.mkQ v = physicalInclusion b y) : closedPhysicalImage a b :=
  ⟨qc (closedCycleTensor u v), by
    rw [← closedPhysicalEmbedding_tmul_of_cycles a b x y u v hu hv]
    exact LinearMap.mem_range_self _ (x ⊗ₜ[ℂ] y)⟩

theorem closedPhysicalImageEquiv_tmul_of_cycles (a b : UCharge)
    (x : physicalMomentum a) (y : physicalMomentum b) (u v : relativeCycles)
    (hu : relativeBoundaries.mkQ u = physicalInclusion a x)
    (hv : relativeBoundaries.mkQ v = physicalInclusion b y) :
    closedPhysicalImageEquiv a b (x ⊗ₜ[ℂ] y) =
      closedPhysicalCycleClass a b x y u v hu hv :=
  Subtype.ext (closedPhysicalEmbedding_tmul_of_cycles a b x y u v hu hv)

section GhostNumber

private theorem chiralNumber_differential (x : V) :
    relativeNumber (d x) = d (relativeNumber x) + d x := by
  apply Subtype.ext
  change N (Q (x : State)) = Q (N (x : State)) + Q (x : State)
  exact OriginalOrbifoldBRSTPhysicalLie.number_Q _

private theorem chiralNumber_parity (x : V) :
    relativeNumber (σ x) = σ (relativeNumber x) := by
  apply Subtype.ext
  change N (parity (x : State)) = parity (N (x : State))
  have h : N.comp parity = parity.comp N := by
    apply fullBasis.ext
    intro i
    simp only [LinearMap.comp_apply, number_basis, parity_basis, map_smul, smul_smul]
    rw [mul_comm]
  exact LinearMap.congr_fun h _

/-- The two original ghost-number operators on closed relative states. -/
def closedLeftNumber : Module.End ℂ ClosedRelativeState :=
  TensorProduct.map relativeNumber LinearMap.id

def closedRightNumber : Module.End ℂ ClosedRelativeState :=
  TensorProduct.map LinearMap.id relativeNumber

def closedNumber : Module.End ℂ ClosedRelativeState := closedLeftNumber + closedRightNumber

theorem closedNumber_tmul (x y : V) :
    closedNumber (x ⊗ₜ[ℂ] y) =
      relativeNumber x ⊗ₜ[ℂ] y + x ⊗ₜ[ℂ] relativeNumber y := by
  simp only [closedNumber, closedLeftNumber, closedRightNumber, LinearMap.add_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]

private theorem closedNumber_differential (z : ClosedRelativeState) :
    closedNumber (closedDifferential z) =
      closedDifferential (closedNumber z) + closedDifferential z := by
  have h : closedNumber.comp closedDifferential =
      closedDifferential.comp closedNumber + closedDifferential := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearMap.add_apply, closedNumber_tmul,
      closedDifferential_tmul, map_add, chiralNumber_differential, chiralNumber_parity,
      TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  exact LinearMap.congr_fun h z

private def closedCycleNumber : Module.End ℂ ClosedRelativeCycles :=
  closedNumber.restrict (by
    intro z hz
    change closedDifferential z = 0 at hz
    change closedDifferential (closedNumber z) = 0
    simpa only [hz, map_zero, add_zero] using (closedNumber_differential z).symm)

/-- Total native ghost number descends to the literal closed quotient. -/
def closedCohomologyNumber : Module.End ℂ ClosedRelativeCohomology :=
  closedRelativeBoundaries.mapQ closedRelativeBoundaries closedCycleNumber (by
    intro z hz
    change ∃ w, boundaryMap closedDifferential
      (ParityOddKunneth.closedDifferential_square chiralComplex chiralComplex) w = z at hz
    obtain ⟨w, rfl⟩ := hz
    refine ⟨closedNumber w + w, Subtype.ext ?_⟩
    change closedDifferential (closedNumber w + w) = closedNumber (closedDifferential w)
    rw [map_add]
    exact (closedNumber_differential w).symm)

theorem closedCohomologyNumber_mk (z : ClosedRelativeCycles) :
    closedCohomologyNumber (qc z) = qc (closedCycleNumber z) := rfl

private def closedOneOneCycles : Submodule ℂ ClosedRelativeCycles :=
  (closedLeftNumber.eigenspace (1 : ℂ) ⊓ closedRightNumber.eigenspace (1 : ℂ)).comap
    (LinearMap.ker closedDifferential).subtype

/-- Classes admitting a closed representative of left and right ghost numbers `(1,1)`. -/
def closedOneOne : Submodule ℂ ClosedRelativeCohomology :=
  closedOneOneCycles.map qc

private theorem closedTmul_mem_oneOne (u v : relativeCycles)
    (hu : relativeNumber (u : V) = (u : V)) (hv : relativeNumber (v : V) = (v : V)) :
    closedCycleTensor u v ∈ closedOneOneCycles := by
  change ((u : V) ⊗ₜ[ℂ] (v : V)) ∈ closedLeftNumber.eigenspace (1 : ℂ) ∧
    ((u : V) ⊗ₜ[ℂ] (v : V)) ∈ closedRightNumber.eigenspace (1 : ℂ)
  constructor
  · exact Module.End.mem_eigenspace_iff.mpr (by
      simp only [closedLeftNumber, TensorProduct.map_tmul, LinearMap.id_apply, hu, one_smul])
  · exact Module.End.mem_eigenspace_iff.mpr (by
      simp only [closedRightNumber, TensorProduct.map_tmul, LinearMap.id_apply, hv, one_smul])

private theorem physicalTmul_mem_closedOneOne (a b : UCharge)
    (x : physicalMomentum a) (y : physicalMomentum b) :
    closedPhysicalEmbedding a b (x ⊗ₜ[ℂ] y) ∈ closedOneOne := by
  refine Exists.elim (physicalInclusion_cycle a x) (fun u hu => ?_)
  refine Exists.elim (physicalInclusion_cycle b y) (fun v hv => ?_)
  have hU : relativeNumber (u : V) = (u : V) := Subtype.ext hu.2.2
  have hV : relativeNumber (v : V) = (v : V) := Subtype.ext hv.2.2
  have hClass := closedPhysicalEmbedding_tmul_of_cycles a b x y u v hu.1 hv.1
  exact Submodule.mem_map.mpr ⟨closedCycleTensor u v, closedTmul_mem_oneOne u v hU hV, hClass.symm⟩

theorem closedPhysicalImage_le_oneOne (a b : UCharge) : closedPhysicalImage a b ≤ closedOneOne := by
  intro c hc
  obtain ⟨t, ht⟩ := hc
  rw [← ht]
  refine TensorProduct.inductionOn
    (motive := fun s : PhysicalTensor a b => closedPhysicalEmbedding a b s ∈ closedOneOne)
    t (physicalTmul_mem_closedOneOne a b) ?_
  intro t s ht hs
  rw [map_add]
  exact closedOneOne.add_mem ht hs

theorem closedOneOne_ghost_two (c : ClosedRelativeCohomology) (hc : c ∈ closedOneOne) :
    closedCohomologyNumber c = (2 : ℂ) • c := by
  have hc' : c ∈ closedOneOneCycles.map qc := hc
  obtain ⟨z, hz, hzc⟩ := Submodule.mem_map.mp hc'
  change (z : ClosedRelativeState) ∈ closedLeftNumber.eigenspace (1 : ℂ) ∧
    (z : ClosedRelativeState) ∈ closedRightNumber.eigenspace (1 : ℂ) at hz
  let state : ClosedRelativeState := z
  have hl : closedLeftNumber state = state :=
    (Module.End.mem_eigenspace_iff.mp hz.1).trans (one_smul ℂ state)
  have hr : closedRightNumber state = state :=
    (Module.End.mem_eigenspace_iff.mp hz.2).trans (one_smul ℂ state)
  have h : closedCycleNumber z = (2 : ℂ) • z := by
    apply Subtype.ext
    change closedLeftNumber state + closedRightNumber state = (2 : ℂ) • state
    exact (congrArg₂ (fun x y : ClosedRelativeState => x + y) hl hr).trans (two_smul ℂ state).symm
  calc
    closedCohomologyNumber c = qc (closedCycleNumber z) :=
      (congrArg closedCohomologyNumber hzc.symm).trans (closedCohomologyNumber_mk z)
    _ = qc ((2 : ℂ) • z) := congrArg qc h
    _ = (2 : ℂ) • c := (map_smul qc (2 : ℂ) z).trans (congrArg ((2 : ℂ) • ·) hzc)

theorem closedPhysicalEmbedding_ghost_two (a b : UCharge) (t : PhysicalTensor a b) :
    closedCohomologyNumber (closedPhysicalEmbedding a b t) =
      (2 : ℂ) • closedPhysicalEmbedding a b t :=
  closedOneOne_ghost_two _ (closedPhysicalImage_le_oneOne a b (LinearMap.mem_range_self _ t))

end GhostNumber

section Hermitian

@[instance_reducible] private def physicalInnerCore (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) : InnerProductSpace.Core ℂ (physicalMomentum a) where
  inner := fun x y => canonicalPhysicalHermitian a x y
  conj_inner_symm x y := canonicalPhysicalHermitian_conj_symm a ha0 ha y x
  re_inner_nonneg x := by
    change 0 ≤ (canonicalPhysicalHermitian a x x).re
    by_cases hx : x = 0
    · subst x
      simp
    · exact (canonicalPhysicalHermitian_positive a ha0 ha x hx).2.le
  add_left x y z := LinearMap.map_add₂ (canonicalPhysicalHermitian a) x y z
  smul_left x y r := LinearMap.map_smulₛₗ₂ (canonicalPhysicalHermitian a) r x y
  definite x h := by
    by_contra hx
    have hp := (canonicalPhysicalHermitian_positive a ha0 ha x hx).2
    change canonicalPhysicalHermitian a x x = 0 at h
    rw [h, Complex.zero_re] at hp
    exact (lt_irrefl 0) hp

private abbrev physicalNormedAddCommGroup (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) : NormedAddCommGroup (physicalMomentum a) :=
  (physicalInnerCore a ha0 ha).toNormedAddCommGroup

@[instance_reducible] private def physicalInnerProductSpace (a : UCharge) (ha0 : a ≠ 0)
    (ha : chargeEnergy hyperbolicData a ≤ 1) :
    letI : NormedAddCommGroup (physicalMomentum a) := physicalNormedAddCommGroup a ha0 ha
    InnerProductSpace ℂ (physicalMomentum a) := by
  letI : InnerProductSpace.Core ℂ (physicalMomentum a) := physicalInnerCore a ha0 ha
  exact InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (physicalMomentum a))

variable (a b : UCharge) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
  (ha : chargeEnergy hyperbolicData a ≤ 1) (hb : chargeEnergy hyperbolicData b ≤ 1)

/-- Mathlib's algebraic tensor inner product for the two literal chiral forms. -/
def physicalTensorHermitian : PhysicalTensor a b →ₗ⋆[ℂ] PhysicalTensor a b →ₗ[ℂ] ℂ :=
  letI := physicalNormedAddCommGroup a ha0 ha
  letI := physicalInnerProductSpace a ha0 ha
  letI := physicalNormedAddCommGroup b hb0 hb
  letI := physicalInnerProductSpace b hb0 hb
  innerₛₗ ℂ

theorem physicalTensorHermitian_tmul (x x' : physicalMomentum a) (y y' : physicalMomentum b) :
    physicalTensorHermitian a b ha0 hb0 ha hb (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') =
      canonicalPhysicalHermitian a x x' * canonicalPhysicalHermitian b y y' := by
  let := physicalNormedAddCommGroup a ha0 ha
  let := physicalInnerProductSpace a ha0 ha
  let := physicalNormedAddCommGroup b hb0 hb
  let := physicalInnerProductSpace b hb0 hb
  exact TensorProduct.inner_tmul ℂ x x' y y'

/-- Pull the tensor pairing back through the inverse of the exact image equivalence. -/
def closedPhysicalHermitian : closedPhysicalImage a b →ₗ⋆[ℂ] closedPhysicalImage a b →ₗ[ℂ] ℂ :=
  let f := (closedPhysicalImageEquiv a b).symm.toLinearMap
  ((physicalTensorHermitian a b ha0 hb0 ha hb).comp f).compl₂ f

theorem closedPhysicalHermitian_image (s t : PhysicalTensor a b) :
    closedPhysicalHermitian a b ha0 hb0 ha hb (closedPhysicalImageEquiv a b s)
      (closedPhysicalImageEquiv a b t) = physicalTensorHermitian a b ha0 hb0 ha hb s t := by
  simp only [closedPhysicalHermitian, LinearMap.compl₂_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem closedPhysicalHermitian_conj_symm (u v : closedPhysicalImage a b) :
    star (closedPhysicalHermitian a b ha0 hb0 ha hb u v) =
      closedPhysicalHermitian a b ha0 hb0 ha hb v u := by
  let := physicalNormedAddCommGroup a ha0 ha
  let := physicalInnerProductSpace a ha0 ha
  let := physicalNormedAddCommGroup b hb0 hb
  let := physicalInnerProductSpace b hb0 hb
  let e := (closedPhysicalImageEquiv a b).symm
  exact inner_conj_symm (𝕜 := ℂ) (e v) (e u)

/-- Every nonzero class in the image has real, strictly positive self-pairing. -/
theorem closedPhysicalHermitian_positive (u : closedPhysicalImage a b) (hu : u ≠ 0) :
    (closedPhysicalHermitian a b ha0 hb0 ha hb u u).im = 0 ∧
      0 < (closedPhysicalHermitian a b ha0 hb0 ha hb u u).re := by
  let := physicalNormedAddCommGroup a ha0 ha
  let := physicalInnerProductSpace a ha0 ha
  let := physicalNormedAddCommGroup b hb0 hb
  let := physicalInnerProductSpace b hb0 hb
  let e := (closedPhysicalImageEquiv a b).symm
  have hu' : e u ≠ 0 := fun h => hu (e.injective (h.trans (e.map_zero).symm))
  exact ⟨inner_self_im (𝕜 := ℂ) (e u), (re_inner_self_pos (𝕜 := ℂ)).mpr hu'⟩

/-- Evaluating on actual closed cycle classes multiplies the exact chiral values. -/
theorem closedPhysicalHermitian_cycleClasses
    (x x' : physicalMomentum a) (y y' : physicalMomentum b)
    (u v u' v' : relativeCycles)
    (hu : relativeBoundaries.mkQ u = physicalInclusion a x)
    (hv : relativeBoundaries.mkQ v = physicalInclusion b y)
    (hu' : relativeBoundaries.mkQ u' = physicalInclusion a x')
    (hv' : relativeBoundaries.mkQ v' = physicalInclusion b y') :
    closedPhysicalHermitian a b ha0 hb0 ha hb
      (closedPhysicalCycleClass a b x y u v hu hv)
      (closedPhysicalCycleClass a b x' y' u' v' hu' hv') =
      canonicalPhysicalHermitian a x x' * canonicalPhysicalHermitian b y y' := by
  let H := closedPhysicalHermitian a b ha0 hb0 ha hb
  have h₁ := closedPhysicalImageEquiv_tmul_of_cycles a b x y u v hu hv
  have h₂ := closedPhysicalImageEquiv_tmul_of_cycles a b x' y' u' v' hu' hv'
  calc
    _ = H (closedPhysicalImageEquiv a b (x ⊗ₜ[ℂ] y))
          (closedPhysicalImageEquiv a b (x' ⊗ₜ[ℂ] y')) :=
      congrArg₂ (fun s t : closedPhysicalImage a b => H s t) h₁.symm h₂.symm
    _ = physicalTensorHermitian a b ha0 hb0 ha hb (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') :=
      closedPhysicalHermitian_image a b ha0 hb0 ha hb _ _
    _ = _ := physicalTensorHermitian_tmul a b ha0 hb0 ha hb x x' y y'

end Hermitian

#print axioms closedPhysicalEmbedding_injective
#print axioms closedPhysicalEmbedding_tmul_of_cycles
#print axioms closedPhysicalImage_le_oneOne
#print axioms closedPhysicalEmbedding_ghost_two
#print axioms closedPhysicalHermitian_conj_symm
#print axioms closedPhysicalHermitian_positive
#print axioms closedPhysicalHermitian_cycleClasses

end
end D5.S3.VertexAlgebra.OriginalOrbifoldClosedRelativePositive
