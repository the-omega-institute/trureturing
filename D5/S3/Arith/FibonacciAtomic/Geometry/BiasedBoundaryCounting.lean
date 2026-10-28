/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCounting
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual finite spectral cutoffs and stopping spaces give the original multiplicity-aware counting bounds. -/

import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrialEnergy
import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundarySpectralForm

/-! Finite cutoffs count repeated positive boundary modes with their original indices. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting

open FiniteSourceHardy (H)
open BiasedBoundaryTrace (G J b)
open BiasedBoundaryPathSplit (constG)
open BiasedBoundaryCentering (Pi C mean centered_suffix_residual)
open BiasedBoundaryStopping (G0 Threshold A Qt Vt Vt0 actual_stopping_partition actual_stopping_residual)
open BiasedBoundaryFreeRootForm (D K Sigma energy mean_Pi lift free_root_least_energy weakGraph)
open BiasedBoundaryOperator (boundaryOperator actual_self_adjoint_realization actual_covariance_eigenspaces)
open BiasedBoundarySpectralForm (actual_spectral_form_energy)
open BiasedBoundaryTrialEnergy (actual_stopping_trial_energy)
open InnerProductSpace Filter
open scoped Topology ENNReal BigOperators

/-- The span of an arbitrary finite selection of actual positive boundary modes. -/
def modeSpace (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) : Submodule ℝ G0 :=
  Submodule.span ℝ (e '' (s : Set ℕ))

instance (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) : FiniteDimensional ℝ (modeSpace e s) :=
  FiniteDimensional.span_of_finite ℝ (s.finite_toSet.image e)

/-- The finite orthogonal spectral projection, including every selected repeated mode. -/
def modeProjection (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) : G0 →L[ℝ] G0 :=
  ∑ i ∈ s, (innerSL ℝ (e i)).smulRight (e i)

private theorem modeProjection_coeff (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ)
    (u : G0) (i : ℕ) :
    e.repr (modeProjection e s u) i = if i ∈ s then e.repr u i else 0 := by
  classical
  simp [modeProjection, map_sum, map_smul, e.repr_self, lp.single_apply,
    e.repr_apply_apply, innerSL_apply_apply]

private theorem modeProjection_mem (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) (u : G0) :
    modeProjection e s u ∈ modeSpace e s := by
  classical
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)

private theorem modeSpace_support (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ)
    {u : G0} (hu : u ∈ modeSpace e s) (i : ℕ) (hi : i ∉ s) : e.repr u i = 0 := by
  classical
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,hj,rfl⟩ := hx
    simp only [e.repr_self, lp.single_apply]
    split_ifs with he
    · exact (hi (he ▸ hj)).elim
    · rfl
  | zero => simp
  | add x y hx hy ihx ihy => simpa using congrArg₂ (· + ·) ihx ihy
  | smul a x hx ih => simpa using congrArg (a * ·) ih

private theorem modeProjection_fixed (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ)
    {u : G0} (hu : u ∈ modeSpace e s) : modeProjection e s u = u := by
  classical
  apply e.repr.injective
  apply lp.ext
  funext i
  rw [modeProjection_coeff]
  split_ifs with hi
  · rfl
  · exact (modeSpace_support e s hu i hi).symm

private theorem modeSpace_dimension (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) :
    Module.finrank ℝ (modeSpace e s) = s.card := by
  classical
  have hr : Set.range (fun i : s => e i.val) = e '' (s : Set ℕ) := by
    ext u
    simp
  unfold modeSpace
  rw [← hr]
  simpa only [Fintype.card_coe] using
    (finrank_span_eq_card (e.orthonormal.linearIndependent.comp
      (fun i : s => i.val) Subtype.val_injective))

private theorem modeProjection_range (e : HilbertBasis ℕ ℝ G0) (s : Finset ℕ) :
    (modeProjection e s).range = modeSpace e s := by
  apply le_antisymm
  · rintro u ⟨v,rfl⟩
    exact modeProjection_mem e s v
  · intro u hu
    exact ⟨u,modeProjection_fixed e s hu⟩

private theorem cutoff_finite (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) (lam : ℝ) :
    {i | (mu i)⁻¹ ≤ lam}.Finite := by
  by_cases hl : 0 < lam
  · apply (hf lam⁻¹ (inv_pos.mpr hl)).subset
    intro i hi
    exact (inv_le_comm₀ hl (hp i)).mpr hi
  · have he : {i | (mu i)⁻¹ ≤ lam} = ∅ := by
      ext i
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((le_of_not_gt hl).trans_lt (inv_pos.mpr (hp i)))
    rw [he]
    exact Set.finite_empty

private theorem strict_cutoff_finite (mu : ℕ → ℝ) (hp : ∀ i, 0 < mu i)
    (hf : ∀ eps : ℝ, 0 < eps → {i | eps ≤ mu i}.Finite) (lam : ℝ) :
    {i | (mu i)⁻¹ < lam}.Finite :=
  (cutoff_finite mu hp hf lam).subset (fun _ hi => hi.le)

private theorem modeSpace_domain (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hg : ∀ i, ((e i).val,(mu i)⁻¹ • (e i).val) ∈ boundaryOperator.graph)
    (s : Finset ℕ) {u : G0} (hu : u ∈ modeSpace e s) : u.val ∈ D := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,_,rfl⟩ := hx
    exact ((actual_self_adjoint_realization.2.2.2.2.2.2.1 _ _).mp (hg i)).1
  | zero => exact D.zero_mem
  | add x y hx hy ihx ihy => exact D.add_mem ihx ihy
  | smul a x hx ih => exact D.smul_mem a ih

private theorem low_mode_energy (e : HilbertBasis ℕ ℝ G0) (mu : ℕ → ℝ)
    (hp : ∀ i, 0 < mu i)
    (he : ∀ F : D, HasSum (fun i =>
      (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2 / mu i) (energy F.val))
    (s : Finset ℕ) (lam : ℝ) (hs : ∀ i ∈ s, (mu i)⁻¹ ≤ lam)
    (F : D) (hmean : mean F.val = 0) (hF : (⟨F.val,hmean⟩ : G0) ∈ modeSpace e s) :
    energy F.val ≤ lam * ‖F.val‖^2 := by
  have hpi : Pi F.val = F.val := by
    rw [centered_suffix_residual.2.2.1, hmean,
      map_zero,sub_zero]
  have hn : HasSum (fun i => (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i)^2) (‖F.val‖^2) := by
    have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
      (e.repr ⟨Pi F.val,mean_Pi F.val⟩)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,
      e.repr.norm_map,Submodule.norm_coe,hpi] using h
  apply hasSum_le _ (he F) (hn.mul_left lam)
  intro i
  by_cases hi : i ∈ s
  · simpa only [div_eq_mul_inv,mul_comm] using
      mul_le_mul_of_nonneg_right (hs i hi)
        (sq_nonneg (e.repr ⟨Pi F.val,mean_Pi F.val⟩ i))
  · have hz : e.repr ⟨Pi F.val,mean_Pi F.val⟩ i = 0 := by
      simpa only [hpi] using modeSpace_support e s hF i hi
    rw [hz]
    simp

end D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCounting
