/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeZeroMomentum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeZeroMomentum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.TensorProduct.Basis]
   utility: none
   digest: Native bases for the graded double-relative BRST quotient at zero momentum. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
The exceptional pair of zero momenta in the unprojected double-relative complex.
The two chiral relative constraints are those of the imported literal shells.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Charge)
open LatticeQuartetContraction (State)
open RelativeCohomology (GhostSpace)
open Module (Basis)

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (pL pR : Charge hyperbolicPlane) : AddCommGroup (Shell pL pR) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell pL) (N := relativeShell pR)

section Graded

variable (pL pR : Charge hyperbolicPlane)

/-- Closed cycles of a fixed total ghost degree in the literal tensor complex. -/
abbrev GradedCycles (g : ℤ) : Submodule ℂ (Shell pL pR) :=
  TotalGhostSpace pL pR g ⊓ LinearMap.ker (differential pL pR)

local instance (p q : Charge hyperbolicPlane) (g : ℤ) :
    AddCommGroup (GradedCycles p q g) := Submodule.addCommGroup _

private def gradedBoundaryMap (g : ℤ) :
    TotalGhostSpace pL pR (g - 1) →ₗ[ℂ] GradedCycles pL pR g :=
  ((differential pL pR).comp (TotalGhostSpace pL pR (g - 1)).subtype).codRestrict _ (by
    intro y
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · simpa only [LinearMap.comp_apply, Submodule.subtype_apply, sub_add_cancel] using
        differential_degree pL pR (g - 1) y.val y.property
    · change differential pL pR (differential pL pR y.val) = 0
      exact LinearMap.congr_fun (differential_square pL pR) y.val)

/-- Boundaries in degree `g` are images of actual cochains in degree `g - 1`. -/
abbrev GradedBoundaries (g : ℤ) : Submodule ℂ (GradedCycles pL pR g) :=
  LinearMap.range (gradedBoundaryMap pL pR g)

/-- The degreewise kernel/image quotient for the signed closed differential. -/
abbrev GradedCohomology (g : ℤ) := GradedCycles pL pR g ⧸ GradedBoundaries pL pR g

end Graded

namespace ZeroMomentum

open RelativeZeroMomentum (shellEquiv v u w)

open private signedDifferential tmul_mem_total from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
open private ghost_support zero_mem_degree one_mem_degree two_mem_degree
  representative_zero representative_current representative_two from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeZeroMomentum

/-- Both terms of the literal parity-signed differential vanish at the exceptional pair. -/
theorem differential_eq_zero : differential 0 0 = 0 := by
  simp only [differential, signedDifferential, RelativeZeroMomentum.relativeQ_eq_zero,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]

private def cyclesEquiv (g : ℤ) : TotalGhostSpace 0 0 g ≃ₗ[ℂ] GradedCycles 0 0 g where
  toFun x := ⟨x.val, Submodule.mem_inf.mpr
    ⟨x.property, by rw [LinearMap.mem_ker, differential_eq_zero, LinearMap.zero_apply]⟩⟩
  invFun x := ⟨x.val, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every homogeneous boundary at the exceptional pair is zero. -/
theorem boundaries_eq_bot (g : ℤ) : GradedBoundaries 0 0 g = ⊥ := by
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change differential 0 0 x.val = 0
  rw [differential_eq_zero, LinearMap.zero_apply]

/-- The class of a homogeneous closed cochain at zero momenta. -/
def classOf (g : ℤ) (z : TotalGhostSpace 0 0 g) : GradedCohomology 0 0 g :=
  Submodule.Quotient.mk (cyclesEquiv g z)

/-- The actual graded quotient retains the full cochain in its total ghost degree. -/
def cohomologyGhostEquiv (g : ℤ) : GradedCohomology 0 0 g ≃ₗ[ℂ] TotalGhostSpace 0 0 g :=
  ((GradedBoundaries 0 0 g).quotEquivOfEqBot (boundaries_eq_bot g)).trans (cyclesEquiv g).symm

theorem cohomologyGhostEquiv_symm_apply (g : ℤ) (z : TotalGhostSpace 0 0 g) :
    (cohomologyGhostEquiv g).symm z = classOf g z :=
  Submodule.quotEquivOfEqBot_symm_apply _ (boundaries_eq_bot g) (cyclesEquiv g z)

/-- Chiral vacuum, the two current states, and the two-ghost vacuum state. -/
abbrev ChiralIndex := Unit ⊕ (Fin 2 ⊕ Unit)

def chiralDegree : ChiralIndex → ℤ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

private abbrev NativeCoordinates := ℂ × ((Fin 2 → ℂ) × ℂ)

private abbrev nativeShellEquiv : relativeShell (0 : Charge hyperbolicPlane) ≃ₗ[ℂ] NativeCoordinates :=
  shellEquiv

private def coordinateBasis : Basis ChiralIndex ℂ NativeCoordinates :=
  (Basis.singleton Unit ℂ).prod ((Pi.basisFun ℂ (Fin 2)).prod (Basis.singleton Unit ℂ))

/-- Basis of the literal chiral zero-momentum shell in native ghost degrees. -/
def chiralBasis : Basis ChiralIndex ℂ (relativeShell 0) :=
  coordinateBasis.map nativeShellEquiv.symm

private theorem chiralBasis_v_coord (i : Unit) :
    chiralBasis (.inl i) = nativeShellEquiv.symm (1, (0, 0)) := by
  rw [chiralBasis, Basis.map_apply]
  apply congrArg nativeShellEquiv.symm
  apply Prod.ext
  · rw [coordinateBasis, Basis.prod_apply_inl_fst, Basis.singleton_apply]
  · exact Basis.prod_apply_inl_snd _ _ _

private theorem chiralBasis_u_coord (i : Fin 2) :
    chiralBasis (.inr (.inl i)) = nativeShellEquiv.symm (0, (Pi.single i 1, 0)) := by
  rw [chiralBasis, Basis.map_apply]
  apply congrArg nativeShellEquiv.symm
  apply Prod.ext
  · exact Basis.prod_apply_inr_fst _ _ _
  · rw [coordinateBasis, Basis.prod_apply_inr_snd]
    apply Prod.ext
    · rw [Basis.prod_apply_inl_fst, Pi.basisFun_apply]
    · exact Basis.prod_apply_inl_snd _ _ _

private theorem chiralBasis_w_coord (i : Unit) :
    chiralBasis (.inr (.inr i)) = nativeShellEquiv.symm (0, (0, 1)) := by
  rw [chiralBasis, Basis.map_apply]
  apply congrArg nativeShellEquiv.symm
  apply Prod.ext
  · exact Basis.prod_apply_inr_fst _ _ _
  · rw [coordinateBasis, Basis.prod_apply_inr_snd]
    apply Prod.ext
    · exact Basis.prod_apply_inr_fst _ _ _
    · rw [Basis.prod_apply_inr_snd, Basis.singleton_apply]

/-- The original association of each basis state gives the native vacuum, current or two-ghost
state, with exactly the normalization of the chiral construction. -/
theorem chiralBasis_native (i : ChiralIndex) :
    reassoc.symm (chiralBasis i).val =
      Sum.elim (fun _ => v) (Sum.elim u (fun _ => w)) i := by
  rcases i with i | (i | i)
  · rw [chiralBasis_v_coord]
    exact (representative_zero 1).trans (one_smul ℂ v)
  · rw [chiralBasis_u_coord]
    exact representative_current i
  · rw [chiralBasis_w_coord]
    exact (representative_two 1).trans (one_smul ℂ w)

theorem chiralBasis_mem (i : ChiralIndex) : chiralBasis i ∈ GhostSpace 0 (chiralDegree i) := by
  rcases i with i | (i | i)
  · rw [chiralBasis_v_coord]
    exact zero_mem_degree 1
  · rw [chiralBasis_u_coord]
    exact one_mem_degree (Pi.single i 1)
  · rw [chiralBasis_w_coord]
    exact two_mem_degree 1

private theorem chiral_repr_eq_zero {g : ℤ} {x : relativeShell 0} (hx : x ∈ GhostSpace 0 g)
    (i : ChiralIndex) (hi : chiralDegree i ≠ g) : chiralBasis.repr x i = 0 := by
  obtain ⟨h0, h1, h2⟩ := ghost_support g x hx
  change coordinateBasis.repr (nativeShellEquiv.symm.symm x) i = 0
  rw [LinearEquiv.symm_symm]
  rcases i with i | (i | i)
  · rw [coordinateBasis, Basis.prod_repr_inl, Basis.singleton_repr]
    exact h0 hi.symm
  · rw [coordinateBasis, Basis.prod_repr_inr, Basis.prod_repr_inl, Pi.basisFun_repr]
    exact congrFun (h1 hi.symm) i
  · rw [coordinateBasis, Basis.prod_repr_inr, Basis.prod_repr_inr, Basis.singleton_repr]
    exact h2 hi.symm

/-- The native tensor-pair indices of total ghost degree `g`. -/
abbrev DegreeIndex (g : ℤ) :=
  {ij : ChiralIndex × ChiralIndex // chiralDegree ij.1 + chiralDegree ij.2 = g}

/-- All sixteen ordered tensor pairs of the native chiral states. -/
def tensorBasis : Basis (ChiralIndex × ChiralIndex) ℂ (Shell 0 0) :=
  chiralBasis.tensorProduct chiralBasis

private theorem tensorBasis_mem (g : ℤ) (ij : DegreeIndex g) :
    tensorBasis ij.val ∈ TotalGhostSpace 0 0 g := by
  rcases ij with ⟨⟨i, j⟩, hij⟩
  rw [tensorBasis, Basis.tensorProduct_apply']
  change chiralBasis i ⊗ₜ[ℂ] chiralBasis j ∈ TotalGhostSpace 0 0 g
  change chiralDegree i + chiralDegree j = g at hij
  rw [← hij]
  exact tmul_mem_total 0 0 (chiralBasis_mem i) (chiralBasis_mem j)

/-- The actual span of homogeneous pure tensors is precisely the span of basis pairs of that
degree. Off-degree coordinates of each generating tensor vanish in at least one factor. -/
theorem totalGhostSpace_eq_span (g : ℤ) :
    TotalGhostSpace 0 0 g =
      Submodule.span ℂ (Set.range (fun ij : DegreeIndex g => tensorBasis ij.val)) := by
  have hspan : Set.range (fun ij : DegreeIndex g => tensorBasis ij.val) =
      tensorBasis '' {ij | chiralDegree ij.1 + chiralDegree ij.2 = g} := by
    ext t
    constructor
    · rintro ⟨ij, rfl⟩
      exact ⟨ij.val, ij.property, rfl⟩
    · rintro ⟨ij, hij, rfl⟩
      exact ⟨⟨ij, hij⟩, rfl⟩
  rw [hspan]
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, hab, rfl⟩
    apply (tensorBasis.mem_span_image).mpr
    rintro ⟨i, j⟩ hij
    by_contra hdegree
    have hne := Finsupp.mem_support_iff.mp hij
    change (chiralBasis.tensorProduct chiralBasis).repr (x ⊗ₜ[ℂ] y) (i, j) ≠ 0 at hne
    rw [Basis.tensorProduct_repr_tmul_apply] at hne
    exact hne (by
      by_cases hi : chiralDegree i = a
      · have hj : chiralDegree j ≠ b := fun hj =>
          hdegree (show chiralDegree i + chiralDegree j = g by rw [hi, hj, hab])
        rw [chiral_repr_eq_zero hy j hj, zero_smul]
      · rw [chiral_repr_eq_zero hx i hi, smul_zero])
  · rintro _ ⟨ij, hij, rfl⟩
    exact tensorBasis_mem g ⟨ij, hij⟩

/-- The homogeneous cochain basis is the degree restriction of the native tensor basis. -/
def totalGhostBasis (g : ℤ) : Basis (DegreeIndex g) ℂ (TotalGhostSpace 0 0 g) := by
  have hli : LinearIndependent ℂ (fun ij : DegreeIndex g => tensorBasis ij.val) :=
    tensorBasis.linearIndependent.comp (fun ij : DegreeIndex g => ij.val) Subtype.val_injective
  exact (Basis.span hli).map (LinearEquiv.ofEq _ _ (totalGhostSpace_eq_span g).symm)

theorem totalGhostBasis_val (g : ℤ) (ij : DegreeIndex g) :
    (totalGhostBasis g ij).val = chiralBasis ij.val.1 ⊗ₜ[ℂ] chiralBasis ij.val.2 := by
  rw [totalGhostBasis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  exact Basis.tensorProduct_apply' _ _ _

/-- A basis of the actual graded quotient, indexed by the homogeneous native tensor pairs. -/
def cohomologyBasis (g : ℤ) : Basis (DegreeIndex g) ℂ (GradedCohomology 0 0 g) :=
  (totalGhostBasis g).map (cohomologyGhostEquiv g).symm

/-- Each quotient basis vector is the class of its literal tensor of chiral basis states. -/
theorem cohomologyBasis_apply (g : ℤ) (ij : DegreeIndex g) :
    cohomologyBasis g ij =
      classOf g ⟨chiralBasis ij.val.1 ⊗ₜ[ℂ] chiralBasis ij.val.2, by
        simpa only [tensorBasis, Basis.tensorProduct_apply'] using tensorBasis_mem g ij⟩ := by
  rw [cohomologyBasis, Basis.map_apply, cohomologyGhostEquiv_symm_apply]
  congr 1
  exact Subtype.ext (totalGhostBasis_val g ij)

private theorem chiralDegree_bounds (i : ChiralIndex) : 0 ≤ chiralDegree i ∧ chiralDegree i ≤ 2 := by
  rcases i with i | (i | i) <;> simp [chiralDegree]

private theorem degreeIndex_isEmpty (g : ℤ) (hg : g < 0 ∨ 4 < g) : IsEmpty (DegreeIndex g) := by
  refine ⟨fun ij => ?_⟩
  have ⟨ha, ha'⟩ := chiralDegree_bounds ij.val.1
  have ⟨hb, hb'⟩ := chiralDegree_bounds ij.val.2
  have h := ij.property
  omega

/-- Outside degrees zero through four every actual graded class is zero. -/
theorem cohomology_vanishes (g : ℤ) (hg : g < 0 ∨ 4 < g) :
    Subsingleton (GradedCohomology 0 0 g) := by
  let := degreeIndex_isEmpty g hg
  exact ⟨fun z w => (cohomologyBasis g).repr.injective (Subsingleton.elim _ _)⟩

/-- Multiplicities of the native tensor pairs in each total ghost degree. -/
def multiplicity : ℤ → ℕ
  | 0 => 1
  | 1 => 4
  | 2 => 6
  | 3 => 4
  | 4 => 1
  | _ => 0

/-- The literal quotient has complex dimensions `1, 4, 6, 4, 1` in degrees zero through four. -/
theorem finrank_cohomology (g : ℤ) :
    Module.finrank ℂ (GradedCohomology 0 0 g) = multiplicity g := by
  rw [Module.finrank_eq_card_basis (cohomologyBasis g)]
  by_cases hg : g < 0 ∨ 4 < g
  · let := degreeIndex_isEmpty g hg
    rw [Fintype.card_eq_zero]
    have h0 : g ≠ 0 := by omega
    have h1 : g ≠ 1 := by omega
    have h2 : g ≠ 2 := by omega
    have h3 : g ≠ 3 := by omega
    have h4 : g ≠ 4 := by omega
    simp [multiplicity]
  · have h : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 := by omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

end ZeroMomentum
end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative
