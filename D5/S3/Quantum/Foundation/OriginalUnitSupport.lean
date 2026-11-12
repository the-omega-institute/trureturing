/- GID: D5/S3/Quantum/Foundation/OriginalUnitSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalUnitSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-unit states carrying the native common support of a faithful PSD cone. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
A finite positive sum detects the common kernel of a generating cone. Scaling
this sum by its original strictly positive unit produces an actual state without
changing its native real or complex support. No full-support ambient matrix,
trace unit, rank-one generation, or normalized section is assumed.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

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
  rw [hfactor, Matrix.det_mul, RCLike.mul_re, hdetim, zero_mul, sub_zero]

private theorem principal_inverse_sqrt_laws (A : Matrix ι ι 𝕜) (hA : A.PosDef) :
    let S := CFC.sqrt A⁻¹
    S.IsHermitian ∧ IsUnit S ∧ S * S = A⁻¹ ∧ S * A * S = 1 := by
  let S := CFC.sqrt A⁻¹
  have hnonneg : 0 ≤ A⁻¹ := hA.inv.posSemidef.nonneg
  have hSH : S.IsHermitian := (CFC.sqrt_nonneg A⁻¹).posSemidef.isHermitian
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
  rw [hAeq]
  calc
    S * (S⁻¹ * S⁻¹) * S = (S * S⁻¹) * (S⁻¹ * S) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.mul_nonsing_inv S hSinv, Matrix.nonsing_inv_mul S hSinv,
      Matrix.one_mul]

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

end D5.S3.Quantum.Foundation.OriginalUnitSupport
