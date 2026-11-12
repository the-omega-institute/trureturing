/- GID: D5/S3/Quantum/Foundation/OriginalUnitSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalUnitSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A faithful native PSD cone representation has an original-unit state with the entire common support. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

/-!
A finite positive sum detects the common kernel of a generating cone. Scaling
this sum by its original strictly positive unit produces an actual state without
changing its native real or complex support. No full-support ambient matrix,
trace unit, rank-one generation, or normalized section is assumed.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder

namespace D5.S3.Quantum.Foundation.OriginalUnitSupport

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

/-- The common support is formed over the native scalar field. -/
def commonSupport (C : PointedCone ℝ V) (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) :
    Submodule 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⨆ x : C, (ρ x.val).toEuclideanLin.range

private theorem sum_kernel (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (s : Finset V)
    (hpos : ∀ x ∈ s, (ρ x).PosSemidef) (z : ι → 𝕜) :
    (ρ (∑ x ∈ s, x)) *ᵥ z = 0 ↔ ∀ x ∈ s, (ρ x) *ᵥ z = 0 := by
  constructor
  · intro hz
    have hsum : ∑ x ∈ s, RCLike.re (star z ⬝ᵥ ((ρ x) *ᵥ z)) = 0 := by
      have hh : RCLike.re (star z ⬝ᵥ ((ρ (∑ x ∈ s, x)) *ᵥ z)) = 0 := by
        rw [hz]
        simp
      simpa only [map_sum, Matrix.sum_mulVec, dotProduct_sum] using hh
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x hx => (hpos x hx).re_dotProduct_nonneg z)).mp hsum
    intro x hx
    apply (hpos x hx).dotProduct_mulVec_zero_iff.mp
    apply RCLike.ext
    · simpa using hall x hx
    · simpa using (hpos x hx).isHermitian.im_star_dotProduct_mulVec_self z
  · intro hz
    simp only [map_sum, Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun x hx => hz x hx

private theorem spanning_sum_kernel (C : PointedCone ℝ V)
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hpos : ∀ x ∈ C, (ρ x).PosSemidef)
    (s : Finset V) (hs : (↑s : Set V) ⊆ C)
    (hspan : Submodule.span ℝ (↑s : Set V) = ⊤) (z : ι → 𝕜) :
    (ρ (∑ x ∈ s, x)) *ᵥ z = 0 ↔ ∀ x : V, (ρ x) *ᵥ z = 0 := by
  constructor
  · intro hz x
    have hall := (sum_kernel ρ s (fun x hx => hpos x (hs hx)) z).mp hz
    let T : V →ₗ[ℝ] (ι → 𝕜) :=
      { toFun := fun x => (ρ x) *ᵥ z
        map_add' := by intros; simp [Matrix.add_mulVec]
        map_smul' := by intros; simp [Matrix.smul_mulVec] }
    have hle : Submodule.span ℝ (↑s : Set V) ≤ T.ker := by
      apply Submodule.span_le.mpr
      intro y hy
      exact hall y hy
    exact hle (by rw [hspan]; trivial)
  · intro hz
    exact (sum_kernel ρ s (fun x hx => hpos x (hs hx)) z).mpr (fun x _ => hz x)

/-- An actual state for the original unit has exactly the common support of the
entire cone, even when that support is a proper ambient subspace. -/
theorem exists_original_unit_full_support [FiniteDimensional ℝ V] [Nontrivial V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hpos : ∀ x ∈ C, (ρ x).PosSemidef) :
    ∃ y : V, y ∈ C ∧ u y = 1 ∧
      (∀ z : ι → 𝕜, (ρ y) *ᵥ z = 0 ↔ ∀ x : V, (ρ x) *ᵥ z = 0) ∧
      (ρ y).toEuclideanLin.range = commonSupport C ρ ∧
      (∀ z : EuclideanSpace 𝕜 ι, z ∈ commonSupport C ρ → z ≠ 0 →
        0 < RCLike.re (star (z : ι → 𝕜) ⬝ᵥ ((ρ y) *ᵥ (z : ι → 𝕜)))) := by
  classical
  obtain ⟨s, hs, _, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (C : Set V)
  rw [hgen] at hspan
  let a : V := ∑ x ∈ s, x
  have ha : a ∈ C := C.sum_mem (fun x hx => hs hx)
  have hkernel : ∀ z : ι → 𝕜, (ρ a) *ᵥ z = 0 ↔ ∀ x : V, (ρ x) *ᵥ z = 0 :=
    spanning_sum_kernel C ρ hpos s hs hspan
  have ha0 : a ≠ 0 := by
    intro ha0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    apply hx
    apply hρ
    rw [map_zero]
    apply Matrix.ext
    intro i j
    have hh := (hkernel (Pi.single j 1)).mp (by
      rw [ha0, map_zero]
      exact Matrix.zero_mulVec _) x
    simpa [Matrix.col] using congrFun hh i
  have hua : 0 < u a := hu a ha ha0
  let y : V := (u a)⁻¹ • a
  have hy : y ∈ C := C.smul_mem (inv_nonneg.mpr hua.le) ha
  have hyu : u y = 1 := by simp [y, hua.ne']
  have hypos : (ρ y).PosSemidef := hpos y hy
  have hykernel : ∀ z : ι → 𝕜, (ρ y) *ᵥ z = 0 ↔ ∀ x : V, (ρ x) *ᵥ z = 0 := by
    intro z
    rw [← hkernel z]
    simp [y, Matrix.smul_mulVec, hua.ne']
  have heq : (ρ y).toEuclideanLin.rangeᗮ = (commonSupport C ρ)ᗮ := by
    rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr hypos.isHermitian).orthogonal_range]
    rw [commonSupport, ← Submodule.iInf_orthogonal]
    simp_rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr (hpos _ (Subtype.property _)).isHermitian).orthogonal_range]
    ext z
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.toLp_eq_zero]
    constructor
    · intro hz x
      exact (hykernel _).mp hz x.val
    · intro hz
      have hle : Submodule.span ℝ (C : Set V) ≤
          (show V →ₗ[ℝ] (ι → 𝕜) from
            { toFun := fun x => (ρ x) *ᵥ (z : ι → 𝕜)
              map_add' := by intros; simp [Matrix.add_mulVec]
              map_smul' := by intros; simp [Matrix.smul_mulVec] }).ker := by
        apply Submodule.span_le.mpr
        intro x hx
        exact hz ⟨x, hx⟩
      exact hle (by rw [hgen]; trivial)
  have hh := congrArg (fun S : Submodule 𝕜 (EuclideanSpace 𝕜 ι) => Sᗮ) heq
  have hrange : (ρ y).toEuclideanLin.range = commonSupport C ρ := by
    simpa only [Submodule.orthogonal_orthogonal] using hh
  refine ⟨y, hy, hyu, hykernel, hrange, ?_⟩
  intro z hz hz0
  by_contra! hnot
  have hzero : RCLike.re (star (z : ι → 𝕜) ⬝ᵥ ((ρ y) *ᵥ (z : ι → 𝕜))) = 0 :=
    le_antisymm hnot (hypos.re_dotProduct_nonneg _)
  have hquad : star (z : ι → 𝕜) ⬝ᵥ ((ρ y) *ᵥ (z : ι → 𝕜)) = 0 := by
    apply RCLike.ext
    · simpa using hzero
    · simpa using hypos.isHermitian.im_star_dotProduct_mulVec_self (z : ι → 𝕜)
  have hker : z ∈ (ρ y).toEuclideanLin.ker := by
    simpa only [LinearMap.mem_ker, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.toLp_eq_zero] using hypos.dotProduct_mulVec_zero_iff.mp hquad
  have horth : z ∈ (ρ y).toEuclideanLin.rangeᗮ := by
    rwa [(Matrix.isSymmetric_toEuclideanLin_iff.mpr hypos.isHermitian).orthogonal_range]
  have hzrange : z ∈ (ρ y).toEuclideanLin.range := by rwa [hrange]
  exact hz0 (Submodule.disjoint_def.mp
    (ρ y).toEuclideanLin.range.orthogonal_disjoint hzrange horth)

end D5.S3.Quantum.Foundation.OriginalUnitSupport
