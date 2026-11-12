/- GID: D5/S3/Quantum/Foundation/OriginalUnitSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalUnitSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native support compression and actual original-unit determinant maximizers. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Tactic

/-!
A finite positive sum detects the common kernel of a generating cone. Scaling
this sum by its original strictly positive unit produces an actual state without
changing its native real or complex support. Native orthonormal compression
reconstructs the entire original representation. The given compact original base
then supplies a positive definite determinant maximum, its affine first variation
and principal inverse square root. Full-vector stationarity gives an actual
trace-preserving congruence whose image contains the identity. No full-support
ambient matrix, trace unit, rank-one
generation, or normalized section is assumed.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Filter Topology

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
    (ρ y).toEuclideanLin.range.orthogonal_disjoint z hzrange horth)

private theorem support_coordinates (W : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) :
    ∃ U : Matrix ι (Fin (Module.finrank 𝕜 W)) 𝕜,
      Uᴴ * U = 1 ∧ U.toEuclideanLin.range = W := by
  classical
  let b := stdOrthonormalBasis 𝕜 W
  let U : Matrix ι (Fin (Module.finrank 𝕜 W)) 𝕜 := fun i j => (b j).val i
  have haction (z : EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 W))) :
      U.toEuclideanLin z = (b.repr.symm z : W).val := by
    have hh := congrArg (fun w : W => w.val) (b.sum_repr (b.repr.symm z))
    ext i
    change ∑ j, U i j * z j = _
    simpa [U,
      dotProduct, mul_comm] using congrArg (fun w : EuclideanSpace 𝕜 ι => w i) hh
  refine ⟨U, ?_, ?_⟩
  · ext i j
    have hh := inner_matrix_col_col U U i j
    have hc (j) : WithLp.toLp 2 (Uᵀ j) = (b j).val := rfl
    rw [hc, hc] at hh
    rw [← hh]
    exact b.inner_eq_ite i j
  · ext z
    constructor
    · rintro ⟨v, rfl⟩
      rw [haction]
      exact Subtype.property _
    · intro hz
      refine ⟨b.repr ⟨z, hz⟩, ?_⟩
      simp [haction]

private theorem range_le_commonSupport (C : PointedCone ℝ V)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (x : V) :
    (ρ x).toEuclideanLin.range ≤ commonSupport C ρ := by
  classical
  let T : Submodule ℝ V :=
    { carrier := {x | ∀ z, (ρ x).toEuclideanLin z ∈ commonSupport C ρ}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy z
        simpa only [map_add, LinearMap.add_apply] using (commonSupport C ρ).add_mem (hx z) (hy z)
      smul_mem' := by
        intro r x hx z
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.smul_mulVec] using
          (commonSupport C ρ).smul_mem (r : 𝕜) (hx z) }
  have hle : Submodule.span ℝ (C : Set V) ≤ T := by
    apply Submodule.span_le.mpr
    intro a ha z
    exact (le_iSup (fun a : C => (ρ a.val).toEuclideanLin.range) ⟨a, ha⟩)
      (LinearMap.mem_range_self _ z)
  rintro z ⟨v, rfl⟩
  exact (hle (by rw [hgen]; trivial) : x ∈ T) v

private theorem reconstruct_of_range {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ 𝕜) (hU : Uᴴ * U = 1) (A : Matrix ι ι 𝕜)
    (hA : A.IsHermitian) (hrange : A.toEuclideanLin.range ≤ U.toEuclideanLin.range) :
    U * (Uᴴ * A * U) * Uᴴ = A := by
  have hleft : (U * Uᴴ) * A = A := by
    apply Matrix.mulVec_injective
    funext z
    have hr := hrange (LinearMap.mem_range_self A.toEuclideanLin (WithLp.toLp 2 z))
    obtain ⟨v, hv⟩ := hr
    have hv' : U *ᵥ (v : κ → 𝕜) = A *ᵥ z := by
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (fun w : EuclideanSpace 𝕜 ι => (w : ι → 𝕜)) hv
    rw [← Matrix.mulVec_mulVec, ← hv', Matrix.mulVec_mulVec, Matrix.mul_assoc,
      hU, Matrix.mul_one]
  have hright : A * (U * Uᴴ) = A := by
    have hh := congrArg Matrix.conjTranspose hleft
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hA.eq] using hh
  calc
    U * (Uᴴ * A * U) * Uᴴ = ((U * Uᴴ) * A) * (U * Uᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hleft, hright]

/-- Compression to the whole native support reconstructs every original vector
and produces an actual positive definite original-unit state. -/
theorem exists_original_unit_support_compression [FiniteDimensional ℝ V] [Nontrivial V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef) :
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧
        (∀ x, ρ x = U * σ x * Uᴴ) ∧ Function.Injective σ ∧
        (∀ x, (σ x).IsHermitian) ∧ (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧
        (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ y : V, y ∈ C ∧ u y = 1 ∧ (σ y).PosDef := by
  classical
  dsimp only
  have hpos (x) (hx : x ∈ C) := (hsection x).mp hx
  obtain ⟨y, hy, hyu, _, hyrange, hypositive⟩ :=
    exists_original_unit_full_support C hgen u hu ρ hρ hpos
  obtain ⟨U, hU, hUrange⟩ := support_coordinates (commonSupport C ρ)
  let σ : V →ₗ[ℝ] Matrix (Fin (Module.finrank 𝕜 (commonSupport C ρ)))
      (Fin (Module.finrank 𝕜 (commonSupport C ρ))) 𝕜 :=
    { toFun := fun x => Uᴴ * ρ x * U
      map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hherm (x : V) : (ρ x).IsHermitian := by
    have hx : x ∈ Submodule.span ℝ (C : Set V) := by rw [hgen]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx => exact (hpos x hx).isHermitian
    | zero => simpa using (Matrix.isHermitian_zero : (0 : Matrix ι ι 𝕜).IsHermitian)
    | add x z hx hz ihx ihz => simpa only [map_add] using ihx.add ihz
    | smul r x hx ih => simpa only [map_smul] using ih.smul (IsSelfAdjoint.all r)
  have hrec (x) : ρ x = U * σ x * Uᴴ := by
    apply Eq.symm
    exact reconstruct_of_range U hU (ρ x) (hherm x)
      ((range_le_commonSupport C hgen ρ x).trans (le_of_eq hUrange.symm))
  have hσ : Function.Injective σ := by
    intro x z hxz
    apply hρ
    rw [hrec x, hrec z, hxz]
  have hn : 0 < Module.finrank 𝕜 (commonSupport C ρ) := by
    by_contra! hn
    have hn0 := Nat.eq_zero_of_le_zero hn
    have hσy : σ y = 0 := by
      ext i
      exact Fin.elim0 (hn0 ▸ i)
    have hy0 : y = 0 := hσ (by simpa using hσy)
    simpa [hy0] using hyu
  refine ⟨hn, U, σ, hU, hUrange, (fun _ => rfl), hrec, hσ, ?_, ?_, ?_, y, hy, hyu, ?_⟩
  · intro x
    exact Matrix.isHermitian_conjTranspose_mul_mul U (hherm x)
  · intro x
    constructor
    · intro hx
      exact (hpos x hx).conjTranspose_mul_mul_same U
    · intro hx
      apply (hsection x).mpr
      rw [hrec x]
      exact hx.mul_mul_conjTranspose_same U
  · intro x
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [hrec x]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hQ : (σ y).PosSemidef := (hpos y hy).conjTranspose_mul_mul_same U
    apply hQ.posDef_iff_mulVec_injective.mpr
    apply (σ y).mulVecLin.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    change (σ y) *ᵥ z = 0 at hz
    have hUz : U *ᵥ z = 0 := by
      by_contra hne
      have hmem : WithLp.toLp 2 (U *ᵥ z) ∈ commonSupport C ρ := by
        exact (le_of_eq hUrange) ⟨WithLp.toLp 2 z, rfl⟩
      have hp := hypositive (WithLp.toLp 2 (U *ᵥ z)) hmem (by simpa using hne)
      have hh : (ρ y) *ᵥ (U *ᵥ z) = 0 := by
        rw [hrec y, Matrix.mulVec_mulVec, Matrix.mul_assoc, hU,
          Matrix.mul_one, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
      simpa only [WithLp.ofLp_toLp, hh, dotProduct_zero, map_zero, lt_self_iff_false] using hp
    have hh := congrArg (fun w => Uᴴ *ᵥ w) hUz
    simpa only [Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, Matrix.mulVec_zero] using hh

private theorem normalized_det_first_variation (B : Matrix ι ι 𝕜) :
    HasDerivAt (fun t : ℝ => RCLike.re (1 + (t : 𝕜) • B).det)
      (RCLike.re B.trace) 0 := by
  let p : Polynomial 𝕜 :=
    (1 + (Polynomial.X : Polynomial 𝕜) • B.map Polynomial.C).det
  have hd : HasDerivAt (fun t : 𝕜 => p.eval t) B.trace 0 := by
    simpa only [p, Matrix.derivative_det_one_add_X_smul] using p.hasDerivAt 0
  have hh := (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).hasFDerivAt.comp (0 : ℝ)
    ((by simpa using hd.hasFDerivAt.restrictScalars ℝ :
      HasFDerivAt (fun t : 𝕜 => p.eval t)
        ((ContinuousLinearMap.toSpanSingleton 𝕜 B.trace).restrictScalars ℝ)
        ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) 0)).comp (0 : ℝ)
      (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt)
  have heval (t : 𝕜) : p.eval t = (1 + t • B).det := by
    have hm : ((1 + (Polynomial.X : Polynomial 𝕜) • B.map Polynomial.C).map
        (Polynomial.evalRingHom t)) = 1 + t • B := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply, smul_eq_mul, hij] <;> ring
    have hh := (Polynomial.evalRingHom t).map_det
      (1 + (Polynomial.X : Polynomial 𝕜) • B.map Polynomial.C)
    change p.eval t = _ at hh
    exact hm ▸ hh
  convert hh.hasDerivAt using 1
  · ext t
    simp only [Function.comp_apply, RCLike.ofRealCLM_apply, RCLike.reCLM_apply]
    exact congrArg RCLike.re (heval t).symm
  · simp


private theorem determinant_first_variation (A B : Matrix ι ι 𝕜) (hA : A.PosDef) :
    HasDerivAt (fun t : ℝ => RCLike.re (A + t • B).det)
      (RCLike.re A.det * RCLike.re (A⁻¹ * B).trace) 0 := by
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hfactor (t : ℝ) : A + t • B = A * (1 + (t : 𝕜) • (A⁻¹ * B)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv A hAdet, Matrix.one_mul]
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hdetim : RCLike.im A.det = 0 := (RCLike.pos_iff.mp hA.det_pos).2
  apply ((normalized_det_first_variation (A⁻¹ * B)).const_mul
    (RCLike.re A.det)).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [hfactor, Matrix.det_mul, RCLike.mul_re, hdetim, zero_mul, sub_zero]

private theorem principal_inverse_sqrt_laws (A : Matrix ι ι 𝕜) (hA : A.PosDef) :
    let S := CFC.sqrt A⁻¹
    S.IsHermitian ∧ IsUnit S ∧ S * S = A⁻¹ ∧ S * A * S = 1 := by
  let S := CFC.sqrt A⁻¹
  have hnonneg : 0 ≤ A⁻¹ := hA.inv.posSemidef.nonneg
  have hSH : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A⁻¹)).isHermitian
  have hSU : IsUnit S := (CFC.isUnit_sqrt_iff A⁻¹ hnonneg).mpr hA.inv.isUnit
  have hSS : S * S = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hnonneg
  have hSinv : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSU
  have hAeq : A = S⁻¹ * S⁻¹ := by
    calc
      A = (A⁻¹)⁻¹ := (Matrix.nonsing_inv_nonsing_inv A
        ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)).symm
      _ = (S * S)⁻¹ := congrArg (fun X : Matrix ι ι 𝕜 => X⁻¹) hSS.symm
      _ = S⁻¹ * S⁻¹ := Matrix.mul_inv_rev S S
  refine ⟨hSH, hSU, hSS, ?_⟩
  change S * A * S = 1
  calc
    S * A * S = S * (S⁻¹ * S⁻¹) * S := congrArg (fun X => S * X * S) hAeq
    _ = (S * S⁻¹) * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv S hSinv, Matrix.nonsing_inv_mul S hSinv,
      Matrix.one_mul]

private theorem quadratic_positive_open {κ : Type*} [Fintype κ] [DecidableEq κ] :
    IsOpen {M : Matrix κ κ 𝕜 | ∀ x : κ → 𝕜, x ≠ 0 →
      0 < RCLike.re (star x ⬝ᵥ M *ᵥ x)} := by
  rw [isOpen_iff_mem_nhds]
  intro M hM
  have key : ∀ᶠ N in 𝓝 M, ∀ x ∈ Metric.sphere (0 : κ → 𝕜) 1,
      0 < RCLike.re (star x ⬝ᵥ N *ᵥ x) := by
    refine (isCompact_sphere (0 : κ → 𝕜) 1).eventually_forall_of_forall_eventually
      fun y hy => ?_
    have hcont : Continuous fun z : Matrix κ κ 𝕜 × (κ → 𝕜) =>
        RCLike.re (star z.2 ⬝ᵥ z.1 *ᵥ z.2) := by fun_prop
    exact (hcont.tendsto (M, y)).eventually_const_lt
      (hM y (ne_zero_of_mem_sphere one_ne_zero ⟨y, hy⟩))
  filter_upwards [key] with N hN x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := hN (‖x‖⁻¹ • x) (by simp [norm_smul, hx0.ne'])
  simp only [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct,
    dotProduct_smul] at h
  simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul,
    RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero] at h
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp
    ((mul_pos_iff_of_pos_left (inv_pos.mpr hx0)).mp h)

private theorem posDef_line_eventually {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : Matrix κ κ 𝕜) (hA : A.PosDef) (hB : B.IsHermitian) :
    ∀ᶠ t : ℝ in 𝓝 0, (A + t • B).PosDef := by
  let P : ℝ → Matrix κ κ 𝕜 := fun t => A + t • B
  have hP : Continuous P := by
    dsimp [P]
    fun_prop
  have hQ : ∀ x : κ → 𝕜, x ≠ 0 →
      0 < RCLike.re (star x ⬝ᵥ A *ᵥ x) := by
    intro x hx
    exact hA.re_dotProduct_pos hx
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ x : κ → 𝕜, x ≠ 0 →
      0 < RCLike.re (star x ⬝ᵥ P t *ᵥ x) := by
    have hopen := quadratic_positive_open (𝕜 := 𝕜) (κ := κ)
    have hmem : P 0 ∈ {M : Matrix κ κ 𝕜 | ∀ x : κ → 𝕜, x ≠ 0 →
        0 < RCLike.re (star x ⬝ᵥ M *ᵥ x)} := by
      simpa [P] using hQ
    have hset : {t : ℝ | P t ∈ {M : Matrix κ κ 𝕜 | ∀ x : κ → 𝕜, x ≠ 0 →
        0 < RCLike.re (star x ⬝ᵥ M *ᵥ x)}} ∈ 𝓝 0 :=
      (hopen.preimage hP).mem_nhds hmem
    exact hset
  filter_upwards [hnear] with t ht
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact hA.isHermitian.add (hB.smul (IsSelfAdjoint.all _))
  · intro x hx
    exact RCLike.pos_iff.mpr ⟨ht x hx,
      (hA.isHermitian.add (hB.smul (IsSelfAdjoint.all _))).im_star_dotProduct_mulVec_self x⟩

private theorem trace_mul_hermitian_real {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A B : Matrix κ κ 𝕜) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace = (RCLike.re (A * B).trace : 𝕜) := by
  have hstar : star (A * B).trace = (A * B).trace := by
    calc
      star (A * B).trace = ((A * B)ᴴ).trace :=
        (Matrix.trace_conjTranspose (A * B)).symm
      _ = (Bᴴ * Aᴴ).trace := by simp
      _ = (B * A).trace := by rw [hB.eq, hA.eq]
      _ = (A * B).trace := Matrix.trace_mul_comm _ _
  apply RCLike.ext
  · simp
  · have him := congrArg RCLike.im hstar
    have him' : -RCLike.im (A * B).trace = RCLike.im (A * B).trace := by
      simpa using him
    have himzero : RCLike.im (A * B).trace = 0 := by linarith
    simp [himzero]

/-- The given entire compact original base produces a positive definite global
determinant maximum on the actual original mass-support-dimension slice. -/
theorem exists_original_unit_determinant_maximum
    [FiniteDimensional ℝ V] [Nontrivial V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hcompact : IsCompact {x : V | x ∈ C ∧ u x = 1})
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef) :
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, ρ x = U * σ x * Uᴴ) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        IsCompact (σ '' {x : V | x ∈ C ∧ u x = (n : ℝ)}) ∧
        ∃ m : V, m ∈ C ∧ u m = (n : ℝ) ∧ (σ m).PosDef ∧
          0 < RCLike.re (σ m).det ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ m).det) ∧
          (∀ v : V, HasDerivAt (fun t : ℝ => RCLike.re (σ (m + t • v)).det)
            (RCLike.re (σ m).det * RCLike.re ((σ m)⁻¹ * σ v).trace) 0) ∧
          let S := CFC.sqrt (σ m)⁻¹
          S.IsHermitian ∧ IsUnit S ∧ S * S = (σ m)⁻¹ ∧ S * σ m * S = 1 := by
  classical
  dsimp only
  obtain ⟨hn, U, σ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank, y, hy, hyu, hyPD⟩ :=
    exists_original_unit_support_compression C hgen u hu ρ hρ hsection
  let n := Module.finrank 𝕜 (commonSupport C ρ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let T : Set V := {x | x ∈ C ∧ u x = (n : ℝ)}
  have hTeq : T = (fun x : V => (n : ℝ) • x) '' {x : V | x ∈ C ∧ u x = 1} := by
    ext x
    constructor
    · rintro ⟨hx, hux⟩
      refine ⟨(n : ℝ)⁻¹ • x, ⟨C.smul_mem (inv_nonneg.mpr hnR.le) hx, ?_⟩, ?_⟩
      · simp [hux, hnR.ne']
      · simp [smul_smul, hnR.ne']
    · rintro ⟨k, ⟨hk, huk⟩, rfl⟩
      exact ⟨C.smul_mem hnR.le hk, by simp [huk]⟩
  have hT : IsCompact T := by
    rw [hTeq]
    exact hcompact.image (continuous_const.smul continuous_id)
  let a : V := (n : ℝ) • y
  have ha : a ∈ T := ⟨C.smul_mem hnR.le hy, by simp [a, hyu]⟩
  have haPD : (σ a).PosDef := by simpa [a] using hyPD.smul hnR
  have haDet : 0 < RCLike.re (σ a).det := (RCLike.pos_iff.mp haPD.det_pos).1
  have hcont : Continuous (fun x : V => RCLike.re (σ x).det) :=
    RCLike.continuous_re.comp σ.continuous_of_finiteDimensional.matrix_det
  obtain ⟨m, hm, hmax⟩ := hT.exists_isMaxOn ⟨a, ha⟩ hcont.continuousOn
  have hmDet : 0 < RCLike.re (σ m).det := haDet.trans_le (hmax ha)
  have hmPD : (σ m).PosDef := (hC m).mp hm.1 |>.posDef_iff_det_ne_zero.mpr (by
    intro hz
    simpa [hz] using hmDet)
  refine ⟨hn, U, σ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
    hT.image σ.continuous_of_finiteDimensional, m, hm.1, hm.2, hmPD, hmDet, ?_⟩
  refine ⟨(fun x hx hux => hmax ⟨hx, hux⟩), ?_, principal_inverse_sqrt_laws (σ m) hmPD⟩
  intro v
  simpa only [map_add, map_smul] using determinant_first_variation (σ m) (σ v) hmPD

private theorem maximal_inverse_trace (C : PointedCone ℝ V)
    (u : V →ₗ[ℝ] ℝ) (σ : V →ₗ[ℝ] Matrix ι ι 𝕜)
    (hn : 0 < Fintype.card ι) (hHerm : ∀ v, (σ v).IsHermitian)
    (hC : ∀ v, v ∈ C ↔ (σ v).PosSemidef)
    (m : V) (hmass : u m = (Fintype.card ι : ℝ)) (hmPD : (σ m).PosDef)
    (hmax : ∀ x ∈ C, u x = (Fintype.card ι : ℝ) →
      RCLike.re (σ x).det ≤ RCLike.re (σ m).det) :
    ∀ v, ((σ m)⁻¹ * σ v).trace = (u v : 𝕜) := by
  let n := Fintype.card ι
  have hmass' : u m = (n : ℝ) := hmass
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmDet : 0 < RCLike.re (σ m).det := (RCLike.pos_iff.mp hmPD.det_pos).1
  have hker : ∀ v : V, u v = 0 → ((σ m)⁻¹ * σ v).trace = 0 := by
    intro v huv
    let f : ℝ → ℝ := fun t => RCLike.re (σ (m + t • v)).det
    have hlocal : IsLocalMax f 0 := by
      change ∀ᶠ t : ℝ in 𝓝 0, f t ≤ f 0
      filter_upwards [posDef_line_eventually (σ m) (σ v) hmPD (hHerm v)] with t ht
      have hmtC : m + t • v ∈ C := by
        apply (hC _).mpr
        simpa only [map_add, map_smul] using ht.posSemidef
      have hmtu : u (m + t • v) = (n : ℝ) := by
        simpa only [map_add, map_smul, hmass', huv, add_zero, smul_zero]
      simpa [f] using hmax _ hmtC hmtu
    have hz := IsLocalMax.hasDerivAt_eq_zero hlocal (by
      simpa only [f, map_add, map_smul] using
        determinant_first_variation (σ m) (σ v) hmPD)
    have hprod : RCLike.re (σ m).det *
        RCLike.re ((σ m)⁻¹ * σ v).trace = 0 := hz
    have htrre : RCLike.re ((σ m)⁻¹ * σ v).trace = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hmDet)
    have htrreal := trace_mul_hermitian_real (σ m)⁻¹ (σ v)
      hmPD.isHermitian.inv (hHerm v)
    rw [htrreal, htrre]
    simp
  have htrace_m : ((σ m)⁻¹ * σ m).trace = (n : 𝕜) := by
    rw [Matrix.nonsing_inv_mul (σ m)
      ((Matrix.isUnit_iff_isUnit_det (σ m)).mp hmPD.isUnit)]
    simp [n]
  intro v
  let q : ℝ := u v / (n : ℝ)
  let w : V := v - q • m
  have hw : u w = 0 := by
    dsimp [w, q]
    simp only [map_sub, map_smul, hmass']
    simp only [smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hnR, mul_one, sub_self]
  have hzero := hker w hw
  have hσv : σ v = σ w + q • σ m := by
    dsimp [w]
    simp only [map_sub, map_smul]
    abel
  rw [hσv, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    hzero, htrace_m]
  dsimp [q]
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  simp only [smul_eq_mul]
  push_cast
  change (0 : 𝕜) + ((u v : 𝕜) / (n : 𝕜)) * (n : 𝕜) = (u v : 𝕜)
  have hnk : (n : 𝕜) ≠ 0 := by exact_mod_cast hnR
  field_simp [hnk]
  simp

private theorem eq_of_inverse_cross_traces (A B : Matrix ι ι 𝕜)
    (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (A⁻¹ * B).trace = (Fintype.card ι : 𝕜))
    (hBA : (B⁻¹ * A).trace = (Fintype.card ι : 𝕜)) : A = B := by
  let S := CFC.sqrt A⁻¹
  let T := CFC.sqrt B⁻¹
  obtain ⟨hSH, hSU, hSS, _⟩ := principal_inverse_sqrt_laws A hA
  obtain ⟨hTH, hTU, hTT, _⟩ := principal_inverse_sqrt_laws B hB
  change S.IsHermitian at hSH
  change T.IsHermitian at hTH
  change S * S = A⁻¹ at hSS
  change T * T = B⁻¹ at hTT
  have hAd := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  have hBd := (Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit
  have hAi := Matrix.mul_nonsing_inv A hAd
  have hiA := Matrix.nonsing_inv_mul A hAd
  have hiB := Matrix.nonsing_inv_mul B hBd
  have hexpand : B⁻¹ * (A - B) * A⁻¹ * (A - B) =
      B⁻¹ * A - 1 - 1 + A⁻¹ * B := by
    calc
      _ = B⁻¹ * (A * A⁻¹) * A - B⁻¹ * (A * A⁻¹) * B -
          (B⁻¹ * B) * A⁻¹ * A + (B⁻¹ * B) * A⁻¹ * B := by noncomm_ring
      _ = _ := by simp only [hAi, hiB, hiA, Matrix.mul_one, Matrix.one_mul]
  have hgram : ((S * (A - B) * T)ᴴ * (S * (A - B) * T)).trace = 0 := by
    calc
      _ = (T * ((A - B) * (S * S) * (A - B)) * T).trace := by
        congr 1
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
          hSH.eq, hTH.eq, hA.isHermitian.eq, hB.isHermitian.eq]
        noncomm_ring
      _ = (T * T * ((A - B) * (S * S) * (A - B))).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = (B⁻¹ * (A - B) * A⁻¹ * (A - B)).trace := by
        rw [hSS, hTT]
        simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
          hBA, hAB]
        simp
  have hzero : S * (A - B) * T = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hgram
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSU
  have hTd : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).mp hTU
  have hleft := Matrix.nonsing_inv_mul S hSd
  have hright := Matrix.mul_nonsing_inv T hTd
  apply sub_eq_zero.mp
  calc
    A - B = (S⁻¹ * S) * (A - B) * (T * T⁻¹) := by
      rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
    _ = S⁻¹ * (S * (A - B) * T) * T⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hzero]; simp

/-- The determinant maximizer is stationary in every original direction after
decomposing along the original mass functional. -/
theorem exists_original_unit_inverse_trace_stationarity
    [FiniteDimensional ℝ V] [Nontrivial V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hcompact : IsCompact {x : V | x ∈ C ∧ u x = 1})
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef) :
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, ρ x = U * σ x * Uᴴ) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ m : V, m ∈ C ∧ u m = (n : ℝ) ∧ (σ m).PosDef ∧
          (∀ v : V, ((σ m)⁻¹ * σ v).trace = (u v : 𝕜)) ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ m).det) ∧
          (∀ k ∈ C, u k = (n : ℝ) →
            (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ k).det) →
            k = m) := by
  classical
  dsimp only
  let n := Module.finrank 𝕜 (commonSupport C ρ)
  obtain ⟨hn, U, σ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
      _hcompact_image, m, hm, hmass, hmPD, hmDet, hmax, hderiv, _hroot⟩ :=
    exists_original_unit_determinant_maximum C hgen u hu hcompact ρ hρ hsection
  have htr := maximal_inverse_trace C u σ (by simpa using hn) hHerm hC m
    (by simpa using hmass) hmPD (by simpa using hmax)
  refine ⟨hn, U, σ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
    m, hm, hmass, hmPD, htr, hmax, ?_⟩
  intro k hk hku hkmax
  have hkDet : 0 < RCLike.re (σ k).det := hmDet.trans_le (hkmax m hm hmass)
  have hkPD : (σ k).PosDef := (hC k).mp hk |>.posDef_iff_det_ne_zero.mpr (by
    intro hz
    simpa [hz] using hkDet)
  have hktr := maximal_inverse_trace C u σ (by simpa using hn) hHerm hC k
    (by simpa using hku) hkPD (by simpa using hkmax)
  apply hσ
  exact eq_of_inverse_cross_traces (σ k) (σ m) hkPD hmPD
    (by simpa only [hmass, RCLike.ofReal_natCast, Fintype.card_fin] using hktr m)
    (by simpa only [hku, RCLike.ofReal_natCast, Fintype.card_fin] using htr k)



private theorem matrix_eq_one_of_card_one (A : Matrix ι ι 𝕜)
    (hcard : Fintype.card ι = 1) (htrace : A.trace = 1) : A = 1 := by
  classical
  obtain ⟨hunique⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp hcard
  letI : Unique ι := hunique
  ext i j
  have htr : A.trace = A i i := by simp [Matrix.trace, Subsingleton.elim (default : ι) i]
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simpa only [Matrix.one_apply, ite_true] using htr.symm.trans htrace

set_option maxHeartbeats 1200000 in
/-- The principal congruence of the actual original-unit maximizer normalizes
all original vectors, with the identity and entire base in the same image. -/
theorem exists_original_unit_normalization
    [FiniteDimensional ℝ V] [Nontrivial V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hcompact : IsCompact {x : V | x ∈ C ∧ u x = 1})
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef) :
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ Ψ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, ρ x = U * σ x * Uᴴ) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ h : V, h ∈ C ∧ u h = (n : ℝ) ∧ (σ h).PosDef ∧
          (∀ v : V, ((σ h)⁻¹ * σ v).trace = (u v : 𝕜)) ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ h).det) ∧
          (∀ k ∈ C, u k = (n : ℝ) →
            (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ k).det) →
            k = h) ∧
          let S := CFC.sqrt (σ h)⁻¹
          S.IsHermitian ∧ IsUnit S ∧ S * S = (σ h)⁻¹ ∧
          (∀ v, Ψ v = S * σ v * S) ∧ Ψ h = 1 ∧
          Function.Injective Ψ ∧ (∀ v, (Ψ v).IsHermitian) ∧
          (∀ v, (Ψ v).trace = (u v : 𝕜)) ∧
          (∀ v, v ∈ C ↔ (Ψ v).PosSemidef) ∧
          (∀ v, (Ψ v).rank = (ρ v).rank) ∧
          (∀ v, ρ v = U * (S⁻¹ * Ψ v * S⁻¹) * Uᴴ) ∧
          (1 : Matrix (Fin n) (Fin n) 𝕜) ∈ Ψ.range ∧
          Ψ '' {v : V | v ∈ C ∧ u v = 1} =
            {X | X ∈ Ψ.range ∧ X.PosSemidef ∧ X.trace = 1} ∧
          (∀ x ∈ C,
            (∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (ρ (y j)).rank = 1) ∧ ρ x = ∑ j, ρ (y j)) ↔
            (∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (Ψ (y j)).rank = 1) ∧ Ψ x = ∑ j, Ψ (y j))) ∧
          ((∃ p : V, {v : V | v ∈ C ∧ u v = 1} = {p}) →
            (∀ x ∈ C, ∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (ρ (y j)).rank = 1) ∧ ρ x = ∑ j, ρ (y j)) → n = 1) ∧
          (n = 1 →
            {v : V | v ∈ C ∧ u v = 1} = {h} ∧
            ({v : V | v ∈ C ∧ u v = 1}).extremePoints ℝ = {h} ∧
            {f : V →ₗ[ℝ] ℝ | (∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v) ∧ f h = 1} = {u} ∧
            {v : V | (v ∈ C ∧ u v = 1) ∧ ∃ f : V →ₗ[ℝ] ℝ,
              (∀ w ∈ C, 0 ≤ f w ∧ f w ≤ u w) ∧ f h = 1 ∧ f v = 0} = ∅ ∧
            {f : V →ₗ[ℝ] ℝ | ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v} =
              {f | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ f = t • u}) ∧
          ∃ e : V ≃ₗ[ℝ] Ψ.range,
            (∀ v, (e v).val = Ψ v) ∧
            let K := {v : V | v ∈ C ∧ u v = 1}
            let Q := {X : Ψ.range | X.val.PosSemidef ∧ X.val.trace = 1}
            let d := e.symm.dualMap
            let O := fun f : V →ₗ[ℝ] ℝ => ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v
            let N := fun g : Ψ.range →ₗ[ℝ] ℝ => ∀ X : Ψ.range,
              X.val.PosSemidef → 0 ≤ g X ∧ g X ≤ RCLike.re X.val.trace
            e '' K = Q ∧ e '' K.extremePoints ℝ = Q.extremePoints ℝ ∧
            (∀ F : Set V, Convex ℝ F ↔ Convex ℝ (e '' F)) ∧
            (∀ A B : Set V, IsExtreme ℝ A B ↔ IsExtreme ℝ (e '' A) (e '' B)) ∧
            (∀ A S : Set V,
              e '' {v | ∀ F : Set V, Convex ℝ F → IsExtreme ℝ A F → S ⊆ F → v ∈ F} =
              {X | ∀ G : Set Ψ.range, Convex ℝ G → IsExtreme ℝ (e '' A) G →
                e '' S ⊆ G → X ∈ G}) ∧
            (∀ f, O f ↔ N (d f)) ∧
            (∀ p, d '' {f | O f ∧ f p = 1} = {g | N g ∧ g (e p) = 1}) ∧
            (∀ p x,
              {r : ℝ | ∃ f, O f ∧ f p = 1 ∧ f x = r} =
              {r : ℝ | ∃ g, N g ∧ g (e p) = 1 ∧ g (e x) = r}) ∧
            (∀ p x,
              d '' {f | O f ∧ f p = 1 ∧ ∀ g, O g → g p = 1 → f x ≤ g x} =
              {g | N g ∧ g (e p) = 1 ∧ ∀ j, N j → j (e p) = 1 → g (e x) ≤ j (e x)}) := by
  classical
  dsimp only
  obtain ⟨hn, U, σ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
      h, hh, hmass, hhPD, htrace, hmax, hunique⟩ :=
    exists_original_unit_inverse_trace_stationarity C hgen u hu hcompact ρ hρ hsection
  let S := CFC.sqrt (σ h)⁻¹
  obtain ⟨hSH, hSU, hSS, hroot⟩ := principal_inverse_sqrt_laws (σ h) hhPD
  change S.IsHermitian at hSH
  change IsUnit S at hSU
  change S * S = (σ h)⁻¹ at hSS
  change S * σ h * S = 1 at hroot
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSU
  have hleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSd
  have hright : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSd
  let Ψ : V →ₗ[ℝ] Matrix _ _ 𝕜 :=
    { toFun := fun v => S * σ v * S
      map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hinv (v : V) : S⁻¹ * Ψ v * S⁻¹ = σ v := by
    change S⁻¹ * (S * σ v * S) * S⁻¹ = σ v
    calc
      _ = (S⁻¹ * S) * σ v * (S * S⁻¹) := by simp only [Matrix.mul_assoc]
      _ = σ v := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  have hΨ : Function.Injective Ψ := by
    intro v w heq
    apply hσ
    rw [← hinv v, ← hinv w, heq]
  have hΨC (v : V) : v ∈ C ↔ (Ψ v).PosSemidef := by
    rw [hC v]
    change (σ v).PosSemidef ↔ (S * σ v * S).PosSemidef
    simpa only [Matrix.star_eq_conjTranspose, hSH.eq] using
      (Matrix.IsUnit.posSemidef_star_left_conjugate_iff (x := σ v) hSU).symm
  have hΨtrace (v : V) : (Ψ v).trace = (u v : 𝕜) := by
    change (S * σ v * S).trace = (u v : 𝕜)
    calc
      (S * σ v * S).trace = (S * S * σ v).trace := Matrix.trace_mul_cycle _ _ _
      _ = (u v : 𝕜) := by rw [hSS, htrace v]
  refine ⟨hn, U, σ, Ψ, hU, hUr, hσeq, hrec, hσ, hHerm, hC, hrank,
    h, hh, hmass, hhPD, htrace, hmax, hunique, hSH, hSU, hSS, (fun _ => rfl), hroot,
    hΨ, ?_, hΨtrace, hΨC, ?_, ?_, ⟨h, hroot⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    change (S * σ v * S).IsHermitian
    simpa only [hSH.eq] using Matrix.isHermitian_conjTranspose_mul_mul S (hHerm v)
  · intro v
    change (S * σ v * S).rank = (ρ v).rank
    rw [Matrix.rank_mul_eq_left_of_isUnit_det S _ hSd,
      Matrix.rank_mul_eq_right_of_isUnit_det S _ hSd, hrank v]
  · intro v
    rw [hinv, hrec v]
  · ext X
    constructor
    · rintro ⟨v, ⟨hv, huv⟩, rfl⟩
      exact ⟨⟨v, rfl⟩, (hΨC v).mp hv, by rw [hΨtrace v, huv]; simp⟩
    · rintro ⟨⟨v, rfl⟩, hv, huv⟩
      refine ⟨v, ⟨(hΨC v).mpr hv, ?_⟩, rfl⟩
      have hre := congrArg RCLike.re huv
      simpa [hΨtrace v] using hre
  · intro x hx
    have hsum (k : ℕ) (y : Fin k → V) :
        ρ x = ∑ j, ρ (y j) ↔ Ψ x = ∑ j, Ψ (y j) := by
      rw [← map_sum, ← map_sum]
      constructor
      · intro heq
        exact congrArg Ψ (hρ heq)
      · intro heq
        exact congrArg ρ (hΨ heq)
    constructor
    · rintro ⟨k, y, hy, heq⟩
      exact ⟨k, y, (fun j => ⟨(hy j).1, by rw [show (Ψ (y j)).rank = (ρ (y j)).rank from
        by change (S * σ (y j) * S).rank = _
           rw [Matrix.rank_mul_eq_left_of_isUnit_det S _ hSd,
             Matrix.rank_mul_eq_right_of_isUnit_det S _ hSd, hrank], (hy j).2]⟩),
        (hsum k y).mp heq⟩
    · rintro ⟨k, y, hy, heq⟩
      refine ⟨k, y, ?_, (hsum k y).mpr heq⟩
      intro j
      refine ⟨(hy j).1, ?_⟩
      have hr : (Ψ (y j)).rank = (ρ (y j)).rank := by
        change (S * σ (y j) * S).rank = _
        rw [Matrix.rank_mul_eq_left_of_isUnit_det S _ hSd,
          Matrix.rank_mul_eq_right_of_isUnit_det S _ hSd, hrank]
      exact hr.symm.trans (hy j).2
  · rintro ⟨p, hp⟩ hrog
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hh0 : h ≠ 0 := by
      intro hz
      have : (n : ℝ) = 0 := by simpa only [hz, map_zero] using hmass.symm
      exact hnR.ne' this
    have hscale (v : V) (hv : v ∈ C) (hv0 : v ≠ 0) : v = u v • p := by
      have huv := hu v hv hv0
      have hw : (u v)⁻¹ • v ∈ {v : V | v ∈ C ∧ u v = 1} :=
        ⟨C.smul_mem (inv_nonneg.mpr huv.le) hv, by simp [huv.ne']⟩
      rw [hp, Set.mem_singleton_iff] at hw
      calc
        v = u v • ((u v)⁻¹ • v) := by simp [smul_smul, huv.ne']
        _ = u v • p := by rw [hw]
    obtain ⟨k, y, hy, heq⟩ := hrog h hh
    have hk : 0 < k := by
      by_contra! hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      have hzero : ρ h = 0 := by
        simpa only [hk0, Fin.sum_univ_zero] using heq
      exact hh0 (hρ (by simpa only [map_zero] using hzero))
    let j : Fin k := ⟨0, hk⟩
    have hy0 : y j ≠ 0 := by
      intro hz
      have hbad := (hy j).2
      simpa [hz] using hbad
    have hyp := hu (y j) (hy j).1 hy0
    have hscaled : y j = (u (y j) / (n : ℝ)) • h := by
      rw [hscale (y j) (hy j).1 hy0, hscale h hh hh0, hmass, smul_smul]
      congr 1
      change u (y j) = u (y j) / (n : ℝ) * (n : ℝ)
      field_simp [hnR.ne']
    have hyPD : (σ (y j)).PosDef := by
      rw [hscaled, map_smul]
      exact hhPD.smul (div_pos hyp hnR)
    have hr := Matrix.rank_of_isUnit (σ (y j)) hyPD.isUnit
    rw [hrank, (hy j).2, Fintype.card_fin] at hr
    exact hr.symm
  · intro hn1
    have hmass1 : u h = 1 := by simpa only [hn1, Nat.cast_one] using hmass
    have hsingle (v : V) (hv : u v = 1) : v = h := by
      apply hΨ
      change Ψ v = S * σ h * S
      rw [hroot]
      exact matrix_eq_one_of_card_one (Ψ v) (by simpa using hn1)
        (by rw [hΨtrace, hv]; simp)
    have hbase : {v : V | v ∈ C ∧ u v = 1} = {h} := by
      ext v
      constructor
      · intro hv
        exact Set.mem_singleton_iff.mpr (hsingle v hv.2)
      · rintro rfl
        exact ⟨hh, hmass1⟩
    have huray (v : V) (hv : v ∈ C) : v = u v • h := by
      by_cases hz : v = 0
      · simp [hz]
      have hp := hu v hv hz
      have hw : (u v)⁻¹ • v ∈ C ∧ u ((u v)⁻¹ • v) = 1 :=
        ⟨C.smul_mem (inv_nonneg.mpr hp.le) hv, by simp [hp.ne']⟩
      have heq := hsingle ((u v)⁻¹ • v) hw.2
      calc
        v = u v • ((u v)⁻¹ • v) := by simp [smul_smul, hp.ne']
        _ = u v • h := by rw [heq]
    have hu_nonneg (v : V) (hv : v ∈ C) : 0 ≤ u v := by
      by_cases hz : v = 0
      · simp [hz]
      · exact (hu v hv hz).le
    have heffect (f : V →ₗ[ℝ] ℝ) : f = f h • u := by
      apply LinearMap.ext_on hgen
      intro v hv
      calc
        f v = f (u v • h) := congrArg f (huray v hv)
        _ = (f h • u) v := by simp [mul_comm]
    have hproper_u : ∀ v ∈ C, 0 ≤ u v ∧ u v ≤ u v :=
      fun v hv => ⟨hu_nonneg v hv, le_rfl⟩
    refine ⟨hbase, by rw [hbase, extremePoints_singleton], ?_, ?_, ?_⟩
    · ext f
      constructor
      · rintro ⟨hf, hfh⟩
        exact Set.mem_singleton_iff.mpr (by simpa [hfh] using heffect f)
      · rintro rfl
        exact ⟨hproper_u, hmass1⟩
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨hv, f, hf, hfh, hfv⟩
      have hvh := hsingle v hv.2
      have heq : f h = 0 := by simpa only [hvh] using hfv
      exact zero_ne_one (heq.symm.trans hfh)
    · ext f
      constructor
      · intro hf
        have hbound := hf h hh
        exact ⟨f h, hbound.1, by simpa only [hmass1] using hbound.2, heffect f⟩
      · rintro ⟨t, ht0, ht1, rfl⟩ v hv
        change 0 ≤ t * u v ∧ t * u v ≤ u v
        exact ⟨mul_nonneg ht0 (hu_nonneg v hv),
          by simpa using mul_le_mul_of_nonneg_right ht1 (hu_nonneg v hv)⟩
  · let e : V ≃ₗ[ℝ] Ψ.range := LinearEquiv.ofInjective Ψ hΨ
    let K := {v : V | v ∈ C ∧ u v = 1}
    let Q := {X : Ψ.range | X.val.PosSemidef ∧ X.val.trace = 1}
    let d := e.symm.dualMap
    let O := fun f : V →ₗ[ℝ] ℝ => ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v
    let N := fun g : Ψ.range →ₗ[ℝ] ℝ => ∀ X : Ψ.range,
      X.val.PosSemidef → 0 ≤ g X ∧ g X ≤ RCLike.re X.val.trace
    have hd (f : V →ₗ[ℝ] ℝ) (v : V) : d f (e v) = f v := by simp [d]
    have hreal (v : V) : RCLike.re (Ψ v).trace = u v := by rw [hΨtrace]; simp
    have hbase : e '' K = Q := by
      ext X
      obtain ⟨v, rfl⟩ := e.surjective X
      rw [e.injective.mem_set_image]
      change (v ∈ C ∧ u v = 1) ↔ (Ψ v).PosSemidef ∧ (Ψ v).trace = 1
      rw [← hΨC, hΨtrace]
      constructor
      · rintro ⟨hv, huv⟩
        exact ⟨hv, by rw [huv]; simp⟩
      · rintro ⟨hv, huv⟩
        exact ⟨hv, by simpa using congrArg RCLike.re huv⟩
    have hconvex (F : Set V) : Convex ℝ F ↔ Convex ℝ (e '' F) := by
      constructor
      · exact fun hF => hF.linear_image e.toLinearMap
      · intro hF
        have hp := hF.linear_preimage e.toLinearMap
        simpa only [e.injective.preimage_image] using hp
    have hface (A B : Set V) : IsExtreme ℝ A B ↔ IsExtreme ℝ (e '' A) (e '' B) := by
      constructor
      · intro hF
        refine ⟨Set.image_mono hF.subset, ?_⟩
        rintro X ⟨x, hx, rfl⟩ Y ⟨y, hy, rfl⟩ Z ⟨z, hz, rfl⟩ hseg
        rw [← image_openSegment ℝ e.toLinearMap.toAffineMap] at hseg
        have hseg' : z ∈ openSegment ℝ x y := e.injective.mem_set_image.mp hseg
        exact ⟨x, hF.left_mem_of_mem_openSegment hx hy hz hseg', rfl⟩
      · intro hF
        refine ⟨?_, ?_⟩
        · intro z hz
          exact e.injective.mem_set_image.mp (hF.subset ⟨z, hz, rfl⟩)
        · intro x hx y hy z hz hseg
          have hs : e z ∈ openSegment ℝ (e x) (e y) := by
            rw [← image_openSegment ℝ e.toLinearMap.toAffineMap]
            exact ⟨z, hseg, rfl⟩
          exact e.injective.mem_set_image.mp
            (hF.left_mem_of_mem_openSegment ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hs)
    have hminimal (A S : Set V) :
        e '' {v | ∀ F : Set V, Convex ℝ F → IsExtreme ℝ A F → S ⊆ F → v ∈ F} =
          {X | ∀ G : Set Ψ.range, Convex ℝ G → IsExtreme ℝ (e '' A) G →
            e '' S ⊆ G → X ∈ G} := by
      ext X
      constructor
      · rintro ⟨v, hv, rfl⟩ G hGc hGface hSG
        have hpre : e '' (e ⁻¹' G) = G := Set.image_preimage_eq G e.surjective
        have hpreFace : IsExtreme ℝ A (e ⁻¹' G) := (hface A _).mpr (by
          rw [hpre]
          exact hGface)
        exact hv (e ⁻¹' G) (hGc.linear_preimage e.toLinearMap) hpreFace
          (fun z hz => hSG ⟨z, hz, rfl⟩)
      · intro hv
        obtain ⟨v, rfl⟩ := e.surjective X
        refine ⟨v, ?_, rfl⟩
        intro F hFc hFface hSF
        exact e.injective.mem_set_image.mp
          (hv (e '' F) ((hconvex F).mp hFc) ((hface A F).mp hFface) (Set.image_mono hSF))
    have hproper (f : V →ₗ[ℝ] ℝ) : O f ↔ N (d f) := by
      constructor
      · intro hf X hX
        obtain ⟨v, rfl⟩ := e.surjective X
        change (Ψ v).PosSemidef at hX
        change 0 ≤ d f (e v) ∧ d f (e v) ≤ RCLike.re (Ψ v).trace
        rw [hd, hreal]
        exact hf v ((hΨC v).mpr hX)
      · intro hf v hv
        have hp := hf (e v) ((hΨC v).mp hv)
        change 0 ≤ d f (e v) ∧ d f (e v) ≤ RCLike.re (Ψ v).trace at hp
        simpa only [hd, hreal] using hp
    refine ⟨e, (fun _ => rfl), hbase, ?_, hconvex, hface, hminimal,
      hproper, ?_, ?_, ?_⟩
    · rw [image_extremePoints, hbase]
    · intro p
      ext g
      obtain ⟨f, rfl⟩ := d.surjective g
      rw [d.injective.mem_set_image]
      change (O f ∧ f p = 1) ↔ (N (d f) ∧ d f (e p) = 1)
      rw [hproper, hd]
    · intro p x
      ext r
      constructor
      · rintro ⟨f, hf, hfp, hfx⟩
        exact ⟨d f, (hproper f).mp hf, by rw [hd, hfp], by rw [hd, hfx]⟩
      · rintro ⟨g, hg, hgp, hgx⟩
        obtain ⟨f, rfl⟩ := d.surjective g
        exact ⟨f, (hproper f).mpr hg, by simpa only [hd] using hgp,
          by simpa only [hd] using hgx⟩
    · intro p x
      ext g
      obtain ⟨f, rfl⟩ := d.surjective g
      rw [d.injective.mem_set_image]
      change (O f ∧ f p = 1 ∧ ∀ j, O j → j p = 1 → f x ≤ j x) ↔
        (N (d f) ∧ d f (e p) = 1 ∧
          ∀ j, N j → j (e p) = 1 → d f (e x) ≤ j (e x))
      constructor
      · rintro ⟨hf, hfp, hmin⟩
        refine ⟨(hproper f).mp hf, by rw [hd, hfp], ?_⟩
        intro j hj hjp
        obtain ⟨k, rfl⟩ := d.surjective j
        simpa only [hd] using hmin k ((hproper k).mpr hj) (by simpa only [hd] using hjp)
      · rintro ⟨hf, hfp, hmin⟩
        refine ⟨(hproper f).mpr hf, by simpa only [hd] using hfp, ?_⟩
        intro j hj hjp
        simpa only [hd] using hmin (d j) ((hproper j).mp hj) (by simpa only [hd] using hjp)

end D5.S3.Quantum.Foundation.OriginalUnitSupport
