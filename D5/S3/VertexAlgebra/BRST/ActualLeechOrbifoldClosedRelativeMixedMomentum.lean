/- GID: D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeMixedMomentum
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/BRST/ActualLeechOrbifoldClosedRelativeMixedMomentum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graded double-relative BRST at mixed zero and nonzero momenta. -/

import D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeZeroMomentum

/-!
The degreewise cohomology of the unprojected signed tensor complex when
exactly one chiral momentum is zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative.MixedMomentum

open ActualLeechOrbifoldCriticalMatter (hyperbolicPlane)
open ActualLeechOrbifoldMatter (Orbifold)
open LatticeGeneratingFieldLocality (Charge)
open LatticeLightConeCoordinates (NullFrame)
open LatticeQuartetContraction (State)
open RelativeCohomology (GhostSpace OrbifoldWeight)
open ZeroMomentum (chiralBasis chiralDegree chiralBasis_mem)
open Module (Basis)

open private signedDifferential tmul_mem_total chiralRetraction
  tensor_sub_left tensor_sub_right from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeBRST
open private gradedBoundaryMap chiral_repr_eq_zero from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldClosedRelativeZeroMomentum
open private coefficient_differential from
  D5.S3.VertexAlgebra.BRST.ActualLeechOrbifoldRelativeCohomology

local instance : AddCommGroup AssocState :=
  TensorProduct.addCommGroup (R := ℂ) (M := Orbifold) (N := State hyperbolicPlane)

local instance (p : Charge hyperbolicPlane) : AddCommGroup (relativeShell p) :=
  Submodule.addCommGroup _

local instance (p : Charge hyperbolicPlane) : AddCommGroup (OrbifoldWeight p) :=
  Submodule.addCommGroup (R := ℂ) (M := Orbifold) (OrbifoldWeight p)

local instance (p q : Charge hyperbolicPlane) : AddCommGroup (Shell p q) :=
  TensorProduct.addCommGroup (R := ℂ) (M := relativeShell p) (N := relativeShell q)

local instance (p q : Charge hyperbolicPlane) (g : ℤ) :
    AddCommGroup (GradedCycles p q g) := Submodule.addCommGroup _

/-- The degree projection in the native zero-momentum chiral basis. -/
def decompose (g : ℤ) : relativeShell 0 →ₗ[ℂ] GhostSpace 0 g :=
  chiralBasis.constr ℂ (fun i => if h : chiralDegree i = g then
    ⟨chiralBasis i, h ▸ chiralBasis_mem i⟩ else 0)

theorem decompose_of_mem (g : ℤ) (x : relativeShell 0) (hx : x ∈ GhostSpace 0 g) :
    decompose g x = ⟨x, hx⟩ := by
  apply Subtype.ext
  change (GhostSpace 0 g).subtype (decompose g x) = x
  rw [decompose, Basis.constr_apply_fintype, map_sum]
  calc
    _ = ∑ i, chiralBasis.repr x i • chiralBasis i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : chiralDegree i = g
      · simp only [hi, dite_true, map_smul, Submodule.subtype_apply, Basis.equivFun_apply]
      · simp only [hi, dite_false, smul_zero, map_zero, chiral_repr_eq_zero hx i hi,
          Basis.equivFun_apply, zero_smul]
    _ = x := chiralBasis.sum_repr x

/-- The projection preserves each homogeneous cochain of the selected degree. -/
theorem decompose_subtype (g : ℤ) (x : GhostSpace 0 g) :
    decompose g x.val = x :=
  decompose_of_mem g x.val x.property

section Quotient

variable {L R : Charge hyperbolicPlane} {g : ℤ}
variable {U : Type*} [AddCommGroup U] [Module ℂ U]
variable (i : U →ₗ[ℂ] Shell L R) (c : Shell L R →ₗ[ℂ] U)
variable (h : Module.End ℂ (Shell L R))
variable (hi : ∀ u, i u ∈ GradedCycles L R g)
variable (hc : ∀ u, c (i u) = u)
variable (hd : ∀ z, c (differential L R z) = 0)
variable (hh : ∀ z ∈ TotalGhostSpace L R g, h z ∈ TotalGhostSpace L R (g - 1))
variable (hom : ∀ z ∈ GradedCycles L R g, differential L R (h z) = z - i (c z))

/-- Pass the mixed contraction to the quotient by the actual preceding-degree images. -/
private def gradedEquiv : GradedCohomology L R g ≃ₗ[ℂ] U := by
  let f := c.comp (GradedCycles L R g).subtype
  have hs : Function.Surjective f := fun u => ⟨⟨i u, hi u⟩, hc u⟩
  have hb : GradedBoundaries L R g = LinearMap.ker f := by
    ext x
    change (∃ y : TotalGhostSpace L R (g - 1), gradedBoundaryMap L R g y = x) ↔
      c x.val = 0
    constructor
    · rintro ⟨y, rfl⟩
      exact hd y.val
    · intro hx
      refine ⟨⟨h x.val, hh x.val x.property.1⟩, Subtype.ext ?_⟩
      change differential L R (h x.val) = x.val
      rw [hom x.val x.property, hx, map_zero, sub_zero]
  exact ((GradedBoundaries L R g).quotEquivOfEq (LinearMap.ker f) hb).trans
    (f.quotKerEquivOfSurjective hs)

end Quotient

variable (F : NullFrame hyperbolicPlane) (B : Module.Basis (Fin 0) ℂ F.K)
  (p : Charge hyperbolicPlane) (hp : F.pPlus p ≠ 0)

section LeftZero

/-- Native inclusion of the zero-left chiral degree and the corrected right representative. -/
def representativeLeftZero (g : ℤ) :
    (GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) →ₗ[ℂ] Shell 0 p :=
  TensorProduct.map (GhostSpace 0 (g - 1)).subtype
    (RelativeCohomology.representative F B p hp)

/-- Read the zero-left degree and the native right coefficient. -/
def coefficientLeftZero (g : ℤ) :
    Shell 0 p →ₗ[ℂ] (GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :=
  TensorProduct.map (decompose (g - 1)) (RelativeCohomology.coefficient F B p hp)

/-- The right primitive with the actual left Koszul sign. -/
def primitiveLeftZero : Module.End ℂ (Shell 0 p) :=
  TensorProduct.map (ghostParity 0) (RelativeCohomology.primitive F B p hp)

private theorem differential_leftZero :
    differential 0 p = TensorProduct.map (ghostParity 0) (relativeQ F B p) := by
  simp only [differential, signedDifferential, RelativeZeroMomentum.relativeQ_eq_zero,
    TensorProduct.map_zero_left, zero_add]
  rfl

theorem representativeLeftZero_mem (g : ℤ) (u : GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :
    representativeLeftZero F B p hp g u ∈ GradedCycles 0 p g := by
  have hle : (⊤ : Submodule ℂ (GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p)) ≤
      (GradedCycles 0 p g).comap (representativeLeftZero F B p hp g) := by
    rw [← TensorProduct.span_tmul_eq_top ℂ (GhostSpace 0 (g - 1)) (OrbifoldWeight p)]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change representativeLeftZero F B p hp g (x ⊗ₜ[ℂ] y) ∈ GradedCycles 0 p g
    rw [representativeLeftZero, TensorProduct.map_tmul]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change x.val ⊗ₜ[ℂ] RelativeCohomology.representative F B p hp y ∈ TotalGhostSpace 0 p g
      have he := tmul_mem_total 0 p x.property (RelativeCohomology.representative_degree F B p hp y)
      rw [sub_add_cancel] at he
      exact he
    · change differential 0 p _ = 0
      rw [differential_leftZero F B p, TensorProduct.map_tmul,
        RelativeCohomology.representative_closed, TensorProduct.tmul_zero]
  exact hle Submodule.mem_top

theorem coefficientLeftZero_representative (g : ℤ) (u : GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :
    coefficientLeftZero F B p hp g (representativeLeftZero F B p hp g u) = u := by
  have he : (coefficientLeftZero F B p hp g).comp (representativeLeftZero F B p hp g) =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, coefficientLeftZero, representativeLeftZero,
      TensorProduct.map_tmul, Submodule.subtype_apply, decompose_subtype,
      RelativeCohomology.coefficient_representative, LinearMap.id_apply]
  exact LinearMap.congr_fun he u

theorem coefficientLeftZero_differential (g : ℤ) (z : Shell 0 p) :
    coefficientLeftZero F B p hp g (differential 0 p z) = 0 := by
  have he : (coefficientLeftZero F B p hp g).comp (differential 0 p) = 0 := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, differential_leftZero F B p, coefficientLeftZero,
      TensorProduct.map_tmul, coefficient_differential, TensorProduct.tmul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun he z

theorem primitiveLeftZero_degree (g : ℤ) (z : Shell 0 p) (hz : z ∈ TotalGhostSpace 0 p g) :
    primitiveLeftZero F B p hp z ∈ TotalGhostSpace 0 p (g - 1) := by
  have hle : TotalGhostSpace 0 p g ≤
      (TotalGhostSpace 0 p (g - 1)).comap (primitiveLeftZero F B p hp) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, rfl, rfl⟩
    change primitiveLeftZero F B p hp (x ⊗ₜ[ℂ] y) ∈ TotalGhostSpace 0 p (a + b - 1)
    rw [primitiveLeftZero, TensorProduct.map_tmul, ghostParity_degree 0 a x hx,
      show a + b - 1 = a + (b - 1) by omega]
    exact tmul_mem_total 0 p ((GhostSpace 0 a).smul_mem _ hx)
      (RelativeCohomology.primitive_degree F B p hp b y hy)
  exact hle hz

theorem contractionLeftZero :
    differential 0 p * primitiveLeftZero F B p hp +
      primitiveLeftZero F B p hp * differential 0 p =
      1 - TensorProduct.map (1 : Module.End ℂ (relativeShell 0))
        ((RelativeCohomology.representative F B p hp).comp
          (RelativeCohomology.coefficient F B p hp)) := by
  let c := chiralRetraction F B p hp
  rw [differential_leftZero F B p, primitiveLeftZero, ← TensorProduct.map_mul,
    ← TensorProduct.map_mul, ghostParity_square, ← TensorProduct.map_add_right]
  change TensorProduct.map (1 : Module.End ℂ (relativeShell 0)) (c.d0 * c.h + c.h * c.d0) = _
  rw [c.contraction, tensor_sub_right, TensorProduct.map_one]
  rfl

private theorem projectionLeftZero (g : ℤ) (z : Shell 0 p) (hz : z ∈ TotalGhostSpace 0 p g) :
    TensorProduct.map (1 : Module.End ℂ (relativeShell 0))
        ((RelativeCohomology.representative F B p hp).comp
          (RelativeCohomology.coefficient F B p hp)) z =
      representativeLeftZero F B p hp g (coefficientLeftZero F B p hp g z) := by
  let E := TensorProduct.map (1 : Module.End ℂ (relativeShell 0))
    ((RelativeCohomology.representative F B p hp).comp (RelativeCohomology.coefficient F B p hp))
  let G := (representativeLeftZero F B p hp g).comp (coefficientLeftZero F B p hp g)
  have hle : TotalGhostSpace 0 p g ≤ LinearMap.ker (E - G) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, hab, rfl⟩
    change E (x ⊗ₜ[ℂ] y) - G (x ⊗ₜ[ℂ] y) = 0
    apply sub_eq_zero.mpr
    simp only [E, G, LinearMap.comp_apply, representativeLeftZero, coefficientLeftZero,
      TensorProduct.map_tmul, Module.End.one_apply, Submodule.subtype_apply]
    by_cases hb : b = 1
    · have ha : a = g - 1 := by omega
      subst a
      rw [decompose_of_mem _ _ hx]
    · rw [RelativeCohomology.coefficient_eq_zero_of_degree_ne_one F B p hp b hb y hy,
        map_zero, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
  exact sub_eq_zero.mp (hle hz)

theorem cycleLeftZero_sub_rep (g : ℤ) (z : Shell 0 p) (hz : z ∈ GradedCycles 0 p g) :
    differential 0 p (primitiveLeftZero F B p hp z) =
      z - representativeLeftZero F B p hp g (coefficientLeftZero F B p hp g z) := by
  have h := LinearMap.congr_fun (contractionLeftZero F B p hp) z
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    show differential 0 p z = 0 from hz.2, map_zero, add_zero] at h
  rw [projectionLeftZero F B p hp g z hz.1] at h
  exact h

/-- The actual degreewise quotient at (0,p), keeping the zero chiral factor on the left. -/
def cohomologyEquivLeftZero (g : ℤ) :
    GradedCohomology 0 p g ≃ₗ[ℂ] (GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :=
  gradedEquiv (U := GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p)
    (representativeLeftZero F B p hp g) (coefficientLeftZero F B p hp g)
    (primitiveLeftZero F B p hp) (representativeLeftZero_mem F B p hp g)
    (coefficientLeftZero_representative F B p hp g) (coefficientLeftZero_differential F B p hp g)
    (primitiveLeftZero_degree F B p hp g) (cycleLeftZero_sub_rep F B p hp g)

theorem cohomologyEquivLeftZero_mk (g : ℤ) (x : GradedCycles 0 p g) :
    cohomologyEquivLeftZero F B p hp g (Submodule.Quotient.mk x) =
      coefficientLeftZero F B p hp g x.val := rfl

theorem cohomologyEquivLeftZero_symm_apply (g : ℤ)
    (u : GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :
    (cohomologyEquivLeftZero F B p hp g).symm u =
      Submodule.Quotient.mk ⟨representativeLeftZero F B p hp g u,
        representativeLeftZero_mem F B p hp g u⟩ := by
  apply (cohomologyEquivLeftZero F B p hp g).injective
  rw [LinearEquiv.apply_symm_apply, cohomologyEquivLeftZero_mk,
    coefficientLeftZero_representative]

end LeftZero

section RightZero

/-- Native inclusion of the corrected left representative and the zero-right chiral degree. -/
def representativeRightZero (g : ℤ) :
    (OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) →ₗ[ℂ] Shell p 0 :=
  TensorProduct.map (RelativeCohomology.representative F B p hp)
    (GhostSpace 0 (g - 1)).subtype

/-- Read the native left coefficient and the zero-right degree. -/
def coefficientRightZero (g : ℤ) :
    Shell p 0 →ₗ[ℂ] (OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :=
  TensorProduct.map (RelativeCohomology.coefficient F B p hp) (decompose (g - 1))

/-- The left primitive tensored with the identity on the zero-momentum shell. -/
def primitiveRightZero : Module.End ℂ (Shell p 0) :=
  TensorProduct.map (RelativeCohomology.primitive F B p hp) 1

private theorem differential_rightZero :
    differential p 0 = TensorProduct.map (relativeQ F B p) 1 := by
  simp only [differential, signedDifferential, RelativeZeroMomentum.relativeQ_eq_zero,
    TensorProduct.map_zero_right, add_zero]
  rfl

theorem representativeRightZero_mem (g : ℤ) (u : OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :
    representativeRightZero F B p hp g u ∈ GradedCycles p 0 g := by
  have hle : (⊤ : Submodule ℂ (OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1))) ≤
      (GradedCycles p 0 g).comap (representativeRightZero F B p hp g) := by
    rw [← TensorProduct.span_tmul_eq_top ℂ (OrbifoldWeight p) (GhostSpace 0 (g - 1))]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, y, rfl⟩
    change representativeRightZero F B p hp g (x ⊗ₜ[ℂ] y) ∈ GradedCycles p 0 g
    rw [representativeRightZero, TensorProduct.map_tmul]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change RelativeCohomology.representative F B p hp x ⊗ₜ[ℂ] y.val ∈ TotalGhostSpace p 0 g
      have he := tmul_mem_total p 0 (RelativeCohomology.representative_degree F B p hp x) y.property
      rw [show 1 + (g - 1) = g by omega] at he
      exact he
    · change differential p 0 _ = 0
      rw [differential_rightZero F B p, TensorProduct.map_tmul,
        RelativeCohomology.representative_closed, TensorProduct.zero_tmul]
  exact hle Submodule.mem_top

theorem coefficientRightZero_representative (g : ℤ) (u : OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :
    coefficientRightZero F B p hp g (representativeRightZero F B p hp g u) = u := by
  have he : (coefficientRightZero F B p hp g).comp (representativeRightZero F B p hp g) =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, coefficientRightZero, representativeRightZero,
      TensorProduct.map_tmul, Submodule.subtype_apply, decompose_subtype,
      RelativeCohomology.coefficient_representative, LinearMap.id_apply]
  exact LinearMap.congr_fun he u

theorem coefficientRightZero_differential (g : ℤ) (z : Shell p 0) :
    coefficientRightZero F B p hp g (differential p 0 z) = 0 := by
  have he : (coefficientRightZero F B p hp g).comp (differential p 0) = 0 := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, differential_rightZero F B p, coefficientRightZero,
      TensorProduct.map_tmul, coefficient_differential, TensorProduct.zero_tmul, LinearMap.zero_apply]
  exact LinearMap.congr_fun he z

theorem primitiveRightZero_degree (g : ℤ) (z : Shell p 0) (hz : z ∈ TotalGhostSpace p 0 g) :
    primitiveRightZero F B p hp z ∈ TotalGhostSpace p 0 (g - 1) := by
  have hle : TotalGhostSpace p 0 g ≤
      (TotalGhostSpace p 0 (g - 1)).comap (primitiveRightZero F B p hp) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, rfl, rfl⟩
    change primitiveRightZero F B p hp (x ⊗ₜ[ℂ] y) ∈ TotalGhostSpace p 0 (a + b - 1)
    rw [primitiveRightZero, TensorProduct.map_tmul, Module.End.one_apply,
      show a + b - 1 = (a - 1) + b by omega]
    exact tmul_mem_total p 0 (RelativeCohomology.primitive_degree F B p hp a x hx) hy
  exact hle hz

theorem contractionRightZero :
    differential p 0 * primitiveRightZero F B p hp +
      primitiveRightZero F B p hp * differential p 0 =
      1 - TensorProduct.map ((RelativeCohomology.representative F B p hp).comp
          (RelativeCohomology.coefficient F B p hp)) (1 : Module.End ℂ (relativeShell 0)) := by
  let c := chiralRetraction F B p hp
  rw [differential_rightZero F B p, primitiveRightZero, ← TensorProduct.map_mul,
    ← TensorProduct.map_mul]
  simp only [mul_one]
  rw [← TensorProduct.map_add_left]
  change TensorProduct.map (c.d0 * c.h + c.h * c.d0) (1 : Module.End ℂ (relativeShell 0)) = _
  rw [c.contraction, tensor_sub_left, TensorProduct.map_one]
  rfl

private theorem projectionRightZero (g : ℤ) (z : Shell p 0) (hz : z ∈ TotalGhostSpace p 0 g) :
    TensorProduct.map ((RelativeCohomology.representative F B p hp).comp
          (RelativeCohomology.coefficient F B p hp)) (1 : Module.End ℂ (relativeShell 0)) z =
      representativeRightZero F B p hp g (coefficientRightZero F B p hp g z) := by
  let E := TensorProduct.map
    ((RelativeCohomology.representative F B p hp).comp (RelativeCohomology.coefficient F B p hp))
    (1 : Module.End ℂ (relativeShell 0))
  let G := (representativeRightZero F B p hp g).comp (coefficientRightZero F B p hp g)
  have hle : TotalGhostSpace p 0 g ≤ LinearMap.ker (E - G) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, b, x, y, hx, hy, hab, rfl⟩
    change E (x ⊗ₜ[ℂ] y) - G (x ⊗ₜ[ℂ] y) = 0
    apply sub_eq_zero.mpr
    simp only [E, G, LinearMap.comp_apply, representativeRightZero, coefficientRightZero,
      TensorProduct.map_tmul, Module.End.one_apply, Submodule.subtype_apply]
    by_cases ha : a = 1
    · have hb : b = g - 1 := by omega
      subst b
      rw [decompose_of_mem _ _ hy]
    · rw [RelativeCohomology.coefficient_eq_zero_of_degree_ne_one F B p hp a ha x hx,
        map_zero, TensorProduct.zero_tmul, TensorProduct.zero_tmul]
  exact sub_eq_zero.mp (hle hz)

theorem cycleRightZero_sub_rep (g : ℤ) (z : Shell p 0) (hz : z ∈ GradedCycles p 0 g) :
    differential p 0 (primitiveRightZero F B p hp z) =
      z - representativeRightZero F B p hp g (coefficientRightZero F B p hp g z) := by
  have h := LinearMap.congr_fun (contractionRightZero F B p hp) z
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    show differential p 0 z = 0 from hz.2, map_zero, add_zero] at h
  rw [projectionRightZero F B p hp g z hz.1] at h
  exact h

/-- The actual degreewise quotient at (p,0), keeping the zero chiral factor on the right. -/
def cohomologyEquivRightZero (g : ℤ) :
    GradedCohomology p 0 g ≃ₗ[ℂ] (OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :=
  gradedEquiv (U := OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1))
    (representativeRightZero F B p hp g) (coefficientRightZero F B p hp g)
    (primitiveRightZero F B p hp) (representativeRightZero_mem F B p hp g)
    (coefficientRightZero_representative F B p hp g) (coefficientRightZero_differential F B p hp g)
    (primitiveRightZero_degree F B p hp g) (cycleRightZero_sub_rep F B p hp g)

theorem cohomologyEquivRightZero_mk (g : ℤ) (x : GradedCycles p 0 g) :
    cohomologyEquivRightZero F B p hp g (Submodule.Quotient.mk x) =
      coefficientRightZero F B p hp g x.val := rfl

theorem cohomologyEquivRightZero_symm_apply (g : ℤ)
    (u : OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :
    (cohomologyEquivRightZero F B p hp g).symm u =
      Submodule.Quotient.mk ⟨representativeRightZero F B p hp g u,
        representativeRightZero_mem F B p hp g u⟩ := by
  apply (cohomologyEquivRightZero F B p hp g).injective
  rw [LinearEquiv.apply_symm_apply, cohomologyEquivRightZero_mk,
    coefficientRightZero_representative]

end RightZero

section Nonzero

variable (h : p ≠ 0)

/-- The mixed quotient at every nonzero right momentum, using an established polarization. -/
def cohomologyEquivLeftZeroNonzero (g : ℤ) :
    GradedCohomology 0 p g ≃ₗ[ℂ] (GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :=
  if hplus : planeFrame.pPlus p ≠ 0 then
    cohomologyEquivLeftZero planeFrame planeBasis p hplus g
  else
    cohomologyEquivLeftZero swappedPlaneFrame swappedPlaneBasis p
      ((planeFrame_covers_nonzero p h).resolve_left hplus) g

/-- The mixed quotient at every nonzero left momentum, using an established polarization. -/
def cohomologyEquivRightZeroNonzero (g : ℤ) :
    GradedCohomology p 0 g ≃ₗ[ℂ] (OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :=
  if hplus : planeFrame.pPlus p ≠ 0 then
    cohomologyEquivRightZero planeFrame planeBasis p hplus g
  else
    cohomologyEquivRightZero swappedPlaneFrame swappedPlaneBasis p
      ((planeFrame_covers_nonzero p h).resolve_left hplus) g

/-- Class readback in the chosen light-cone orientation. -/
theorem cohomologyEquivLeftZeroNonzero_mk (g : ℤ) (x : GradedCycles 0 p g) :
    cohomologyEquivLeftZeroNonzero p h g (Submodule.Quotient.mk x) =
      if hplus : planeFrame.pPlus p ≠ 0 then coefficientLeftZero planeFrame planeBasis p hplus g x.val
      else coefficientLeftZero swappedPlaneFrame swappedPlaneBasis p
        ((planeFrame_covers_nonzero p h).resolve_left hplus) g x.val := by
  unfold cohomologyEquivLeftZeroNonzero
  split <;> rw [cohomologyEquivLeftZero_mk]

/-- The inverse class is the native representative in the same orientation. -/
theorem cohomologyEquivLeftZeroNonzero_symm_apply (g : ℤ) (u : GhostSpace 0 (g - 1) ⊗[ℂ] OrbifoldWeight p) :
    (cohomologyEquivLeftZeroNonzero p h g).symm u =
      if hplus : planeFrame.pPlus p ≠ 0 then
        Submodule.Quotient.mk ⟨representativeLeftZero planeFrame planeBasis p hplus g u,
          representativeLeftZero_mem planeFrame planeBasis p hplus g u⟩
      else
        Submodule.Quotient.mk ⟨representativeLeftZero swappedPlaneFrame swappedPlaneBasis p
            ((planeFrame_covers_nonzero p h).resolve_left hplus) g u,
          representativeLeftZero_mem swappedPlaneFrame swappedPlaneBasis p
            ((planeFrame_covers_nonzero p h).resolve_left hplus) g u⟩ := by
  unfold cohomologyEquivLeftZeroNonzero
  split <;> rw [cohomologyEquivLeftZero_symm_apply]

/-- Class readback in the chosen light-cone orientation. -/
theorem cohomologyEquivRightZeroNonzero_mk (g : ℤ) (x : GradedCycles p 0 g) :
    cohomologyEquivRightZeroNonzero p h g (Submodule.Quotient.mk x) =
      if hplus : planeFrame.pPlus p ≠ 0 then coefficientRightZero planeFrame planeBasis p hplus g x.val
      else coefficientRightZero swappedPlaneFrame swappedPlaneBasis p
        ((planeFrame_covers_nonzero p h).resolve_left hplus) g x.val := by
  unfold cohomologyEquivRightZeroNonzero
  split <;> rw [cohomologyEquivRightZero_mk]

/-- The inverse class is the native representative in the same orientation. -/
theorem cohomologyEquivRightZeroNonzero_symm_apply (g : ℤ) (u : OrbifoldWeight p ⊗[ℂ] GhostSpace 0 (g - 1)) :
    (cohomologyEquivRightZeroNonzero p h g).symm u =
      if hplus : planeFrame.pPlus p ≠ 0 then
        Submodule.Quotient.mk ⟨representativeRightZero planeFrame planeBasis p hplus g u,
          representativeRightZero_mem planeFrame planeBasis p hplus g u⟩
      else
        Submodule.Quotient.mk ⟨representativeRightZero swappedPlaneFrame swappedPlaneBasis p
            ((planeFrame_covers_nonzero p h).resolve_left hplus) g u,
          representativeRightZero_mem swappedPlaneFrame swappedPlaneBasis p
            ((planeFrame_covers_nonzero p h).resolve_left hplus) g u⟩ := by
  unfold cohomologyEquivRightZeroNonzero
  split <;> rw [cohomologyEquivRightZero_symm_apply]

private theorem ghostSpace_outside (g : ℤ) (hg : g < 1 ∨ 3 < g) :
    Subsingleton (GhostSpace 0 (g - 1)) :=
  Submodule.subsingleton_iff_eq_bot.mpr (RelativeZeroMomentum.ghostSpace_eq_bot (g - 1)
    (by omega) (by omega) (by omega))

include h in
/-- The (0,p) graded quotient is zero outside total ghost degrees one through three. -/
theorem cohomologyLeftZero_vanishes (g : ℤ) (hg : g < 1 ∨ 3 < g) :
    Subsingleton (GradedCohomology 0 p g) := by
  let := ghostSpace_outside g hg
  exact ⟨fun x y => (cohomologyEquivLeftZeroNonzero p h g).injective (Subsingleton.elim _ _)⟩

include h in
/-- The (p,0) graded quotient is zero outside total ghost degrees one through three. -/
theorem cohomologyRightZero_vanishes (g : ℤ) (hg : g < 1 ∨ 3 < g) :
    Subsingleton (GradedCohomology p 0 g) := by
  let := ghostSpace_outside g hg
  exact ⟨fun x y => (cohomologyEquivRightZeroNonzero p h g).injective (Subsingleton.elim _ _)⟩

end Nonzero

end D5.S3.VertexAlgebra.ActualLeechOrbifoldBRST.ClosedRelative.MixedMomentum
