/- GID: D5/S3/HilbertOperators/Approximation/KyFanTriangle
   generality: G
   mirror-B: D5/B/S3/HilbertOperators/Approximation/KyFanTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All finite Ky Fan gauges satisfy the triangle inequality on complex Hilbert spaces. -/

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the accompanying LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh,
Claude Opus 5.
Adapted from AIQ-Kitware/aiq-dkps-formalization at
8924c4cc743d2f193bb4f39bee800790698a681b, ApproximationNumber/{Basic,MinMax,
FiniteDimensional,FiniteRestriction,KyFan}.lean. FiniteDimensional credits
Davis--Kahan revision fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7;
Basic credits Mathlib PR #32126. Changes: complex specialization, declaration
slicing, native approximation-number reuse, direct pinned rank API, and reuse
of existing finite spectral and rectangular variational proofs.
Retirement: replace these slices by direct imports when the pinned Mathlib
supplies the equivalent declarations with the same hypotheses.
-/

import D5.S3.HilbertOperators.Approximation.MinMaxLowerBound
import D5.S3.Quantum.Entanglement.Rectangular.FiniteSectorRectangularAttainment
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace D5.S3.HilbertOperators.Approximation.KyFanTriangle
open ContinuousLinearMap
open D5.S3.HilbertOperators.Approximation.MinMaxLowerBound
open Module (finrank)
open scoped InnerProductSpace
noncomputable section
universe u v w
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

private instance approximation_index_nonempty (n : ℕ) :
    Nonempty {R : E →L[ℂ] F // R.rank ≤ (n : Cardinal)} :=
  ⟨⟨0, by simp [LinearMap.rank_zero]⟩⟩

private theorem le_approximation_number_iff (T : E →L[ℂ] F) {n : ℕ} {x : ℝ} :
    x ≤ approximation_number T n ↔
      ∀ R : E →L[ℂ] F, R.rank ≤ (n : Cardinal) → x ≤ ‖T - R‖ := by
  refine ⟨fun h R hR => h.trans (approximation_number_le_error T hR), fun h => ?_⟩
  apply le_ciInf
  rintro ⟨R, hR⟩
  exact h R hR

private theorem approximation_number_nonneg (T : E →L[ℂ] F) (n : ℕ) :
    0 ≤ approximation_number T n := le_ciInf fun _ => norm_nonneg _

private theorem approximation_number_le_norm (T : E →L[ℂ] F) (n : ℕ) :
    approximation_number T n ≤ ‖T‖ := by
  simpa using approximation_number_le_error T (R := 0) (n := n) (by simp [LinearMap.rank_zero])

private theorem exists_rank_le_error_lt_add (T : E →L[ℂ] F)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[ℂ] F, R.rank ≤ (n : Cardinal) ∧
      ‖T - R‖ < approximation_number T n + ε := by
  have hlt : approximation_number T n < approximation_number T n + ε :=
    lt_add_of_pos_right _ hε
  obtain ⟨⟨R, hR⟩, hdist⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨R, hR, hdist⟩

private theorem approximation_number_comp_le_mul_norm
    {G : Type x} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (T : E →L[ℂ] F) (A : G →L[ℂ] E) (n : ℕ) :
    (approximation_number (T ∘L A)) n ≤
      (approximation_number T) n * ‖A‖ := by
  by_cases hA : ‖A‖ = 0
  · calc
      (approximation_number (T ∘L A)) n ≤ ‖T ∘L A‖ :=
        (approximation_number_le_norm (T ∘L A)) n
      _ ≤ ‖T‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = (approximation_number T) n * ‖A‖ := by simp [hA]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεA : 0 < ε / ‖A‖ := div_pos hε (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA))
    obtain ⟨R, hRrank, hRdist⟩ :=
      (exists_rank_le_error_lt_add T) n hεA
    have hcompRank : (R ∘L A).rank ≤ (n : Cardinal) :=
      (LinearMap.rank_comp_le_left A.toLinearMap R.toLinearMap).trans hRrank
    exact le_of_lt <| calc
      (approximation_number (T ∘L A)) n ≤ ‖(T ∘L A) - (R ∘L A)‖ :=
        approximation_number_le_error (T ∘L A) hcompRank
      _ = ‖(T - R) ∘L A‖ := by rw [ContinuousLinearMap.sub_comp]
      _ ≤ ‖T - R‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < ((approximation_number T) n + ε / ‖A‖) * ‖A‖ :=
        mul_lt_mul_of_pos_right hRdist (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA))
      _ = (approximation_number T) n * ‖A‖ + ε := by
        rw [add_mul, div_mul_cancel₀ ε hA]

/-- Left ideal inequality for approximation numbers. -/
private theorem approximation_number_comp_le_norm_mul
    {G : Type x} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (B : F →L[ℂ] G) (T : E →L[ℂ] F) (n : ℕ) :
    (approximation_number (B ∘L T)) n ≤
      ‖B‖ * (approximation_number T) n := by
  by_cases hB : ‖B‖ = 0
  · calc
      (approximation_number (B ∘L T)) n ≤ ‖B ∘L T‖ :=
        (approximation_number_le_norm (B ∘L T)) n
      _ ≤ ‖B‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖B‖ * (approximation_number T) n := by simp [hB]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεB : 0 < ε / ‖B‖ := div_pos hε (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB))
    obtain ⟨R, hRrank, hRdist⟩ :=
      (exists_rank_le_error_lt_add T) n hεB
    have hcompRank : (B ∘L R).rank ≤ (n : Cardinal) := by
      change (B.toLinearMap.comp R.toLinearMap).rank ≤ (n : Cardinal)
      apply Cardinal.lift_le.{v, x}.mp
      rw [Cardinal.lift_natCast]
      exact (LinearMap.lift_rank_comp_le_right R.toLinearMap B.toLinearMap).trans
        (by simpa only [Cardinal.lift_natCast] using Cardinal.lift_le.mpr hRrank)
    exact le_of_lt <| calc
      (approximation_number (B ∘L T)) n ≤ ‖(B ∘L T) - (B ∘L R)‖ :=
        approximation_number_le_error (B ∘L T) hcompRank
      _ = ‖B ∘L (T - R)‖ := by rw [ContinuousLinearMap.comp_sub]
      _ ≤ ‖B‖ * ‖T - R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < ‖B‖ * ((approximation_number T) n + ε / ‖B‖) :=
        mul_lt_mul_of_pos_left hRdist (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB))
      _ = ‖B‖ * (approximation_number T) n + ε := by
        rw [mul_add, mul_div_cancel₀ ε hB]

theorem lower_bound_of_lt_rank
    (T : E →L[ℂ] F) (n : ℕ) (V : Submodule ℂ E) {c : ℝ}
    (hVrank : (n : Cardinal) < Module.rank ℂ V)
    (hV : ∀ x : V, c * ‖(x : E)‖ ≤ ‖T (x : E)‖) :
    c ≤ (approximation_number T) n := by
  refine (le_approximation_number_iff T).mpr ?_
  intro R hR
  let RV : V →L[ℂ] F := R.comp V.subtypeL
  have hRVrank : RV.rank ≤ (n : Cardinal) := by
    calc
      RV.rank ≤ R.rank := by
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        change LinearMap.rank
            (R.toLinearMap.comp V.subtypeL.toLinearMap) ≤ R.rank
        exact LinearMap.rank_comp_le_left V.subtypeL.toLinearMap R.toLinearMap
      _ ≤ (n : Cardinal) := hR
  have hker : RV.ker ≠ ⊥ := by
    intro hkerbot
    -- The rank-nullity identity compares the rank of the range, which lives in
    -- the codomain universe, with the rank of the domain.  Those universes are
    -- independent, so argue through injectivity and `Cardinal.lift` instead: an
    -- injective map identifies the domain with its range.
    have hinj : Function.Injective RV.toLinearMap :=
      LinearMap.ker_eq_bot.mp hkerbot
    have hequiv :
        Cardinal.lift.{v} (Module.rank ℂ V) =
          Cardinal.lift.{u}
            (Module.rank ℂ (LinearMap.range RV.toLinearMap)) :=
      (LinearEquiv.ofInjective RV.toLinearMap hinj).lift_rank_eq
    have hbad : Module.rank ℂ V ≤ (n : Cardinal) := by
      apply Cardinal.lift_le.mp
      simp only [Cardinal.lift_natCast]
      calc
        Cardinal.lift.{v} (Module.rank ℂ V)
            = Cardinal.lift.{u} (LinearMap.rank RV.toLinearMap) := hequiv
        _ ≤ Cardinal.lift.{u} ((n : ℕ) : Cardinal) := Cardinal.lift_le.mpr hRVrank
        _ = ((n : ℕ) : Cardinal) := Cardinal.lift_natCast n
    exact absurd hbad (not_le.mpr hVrank)
  obtain ⟨z, hzker, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hzNorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  let x : V := ((‖z‖⁻¹ : ℝ) : ℂ) • z
  have hxker : x ∈ RV.ker := RV.ker.smul_mem _ hzker
  have hxNorm : ‖(x : E)‖ = 1 := by
    simp only [x, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ hzNorm
  have hRx : R (x : E) = 0 := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change RV x = 0
    exact LinearMap.mem_ker.mp hxker
  calc
    c = c * ‖(x : E)‖ := by rw [hxNorm, mul_one]
    _ ≤ ‖T (x : E)‖ := hV x
    _ = ‖(T - R) (x : E)‖ := by rw [sub_apply, hRx, sub_zero]
    _ ≤ ‖T - R‖ * ‖(x : E)‖ := (T - R).le_opNNNorm (x : E)
    _ = ‖T - R‖ := by rw [hxNorm, mul_one]

/-- Finite-dimensional form of `lower_bound_of_lt_rank`, with the
unit-vector premise the classical statement uses.

Nothing is assumed about the sign of `c`: at `x = 0` the homogeneous bound reads
`c * 0 ≤ 0`, and elsewhere it follows by rescaling to a unit vector. -/
private theorem lower_bound_of_finrank_lt
    (T : E →L[ℂ] F) (n : ℕ) (V : Submodule ℂ E)
    [FiniteDimensional ℂ V] {c : ℝ} (hVdim : n < finrank ℂ V)
    (hV : ∀ x : V, ‖(x : E)‖ = 1 → c ≤ ‖T (x : E)‖) :
    c ≤ (approximation_number T) n := by
  refine lower_bound_of_lt_rank T n V ?_ ?_
  · rw [← Module.finrank_eq_rank' ℂ V]
    exact_mod_cast hVdim
  · intro x
    rcases eq_or_ne (x : E) 0 with hx | hx
    · simp [hx]
    · -- Rescale `x` to the unit sphere of `V` and use homogeneity of both sides.
      have hxn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      set y : V := ((‖(x : E)‖⁻¹ : ℝ) : ℂ) • x with hy
      have hyNorm : ‖(y : E)‖ = 1 := by
        simp only [hy, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
        exact inv_mul_cancel₀ hxn
      have hTy : ‖T (y : E)‖ = ‖(x : E)‖⁻¹ * ‖T (x : E)‖ := by
        simp [hy, norm_smul]
      have hstep := hV y hyNorm
      rw [hTy] at hstep
      calc c * ‖(x : E)‖
          ≤ (‖(x : E)‖⁻¹ * ‖T (x : E)‖) * ‖(x : E)‖ :=
            mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
        _ = ‖T (x : E)‖ := by field_simp

/-- Family form of `lower_bound_of_finrank_lt`: a linearly independent
family of `n + 1` vectors determines the required test subspace.

This is not a forgetful wrapper — it is how every downstream consumer in this
repository applies the bound, since a spanning family is what the perturbation
arguments produce. -/
private theorem lower_bound_of_independent
    (T : E →L[ℂ] F) (n : ℕ) (v : Fin (n + 1) → E)
    (hv : LinearIndependent ℂ v) {c : ℝ}
    (hV : ∀ x ∈ Submodule.span ℂ (Set.range v),
      ‖x‖ = 1 → c ≤ ‖T x‖) :
    c ≤ (approximation_number T) n := by
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
  let : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hVdim : n < finrank ℂ V := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    exact Nat.lt_succ_self n
  refine lower_bound_of_finrank_lt T n V hVdim ?_
  intro x hx
  exact hV (x : E) x.2 hx


section Finite
variable [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- The lower spectral bound holds against every admissible approximation. -/
theorem singular_value_le_approximation_number (T : E →L[ℂ] F) (n : ℕ) :
    T.toLinearMap.singularValues n ≤ approximation_number T n := by
  by_cases hn : finrank ℂ E ≤ n
  · rw [T.toLinearMap.singularValues_of_finrank_le hn]
    exact approximation_number_nonneg T n
  · let k : Fin (finrank ℂ E) := ⟨n, Nat.lt_of_not_ge hn⟩
    obtain ⟨V, hdim, hlow⟩ :=
      D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.exists_submodule_forall_unit_eigenvalue_le_re_inner
        T.toLinearMap.isSymmetric_adjoint_comp_self rfl k
    apply lower_bound_of_finrank_lt T n V (by simpa [k, hdim] using Nat.lt_succ_self n)
    intro x hx
    have h := hlow (x : E) x.property hx
    rw [← T.toLinearMap.sq_singularValues_fin rfl k] at h
    have heq : RCLike.re ⟪(T.toLinearMap.adjoint ∘ₗ T.toLinearMap) (x : E), (x : E)⟫_ℂ
        = ‖T (x : E)‖ ^ 2 := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq]
      rfl
    rw [heq] at h
    exact le_of_sq_le_sq h (norm_nonneg _)

/-- Spectral truncation supplies an actual rank-bounded approximant. -/
theorem approximation_number_le_singular_value (T : E →L[ℂ] F) (n : ℕ) :
    approximation_number T n ≤ T.toLinearMap.singularValues n := by
  classical
  by_cases hn : finrank ℂ E ≤ n
  · have hTrank : T.rank ≤ (n : Cardinal) := by
      apply Cardinal.lift_le.{u, v}.mp
      rw [Cardinal.lift_natCast]
      apply (lift_rank_range_le T.toLinearMap).trans
      simpa only [← Module.finrank_eq_rank' ℂ E, Cardinal.lift_natCast] using
        (show ((finrank ℂ E : ℕ) : Cardinal) ≤ (n : Cardinal) by exact_mod_cast hn)
    have hle : approximation_number T n ≤ 0 := by
      simpa using approximation_number_le_error T (R := T) hTrank
    exact hle.trans (T.toLinearMap.singularValues_nonneg n)
  · let A : E →ₗ[ℂ] F := T.toLinearMap
    let hGram : (A.adjoint ∘ₗ A).IsSymmetric := A.isSymmetric_adjoint_comp_self
    let b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E := hGram.eigenvectorBasis rfl
    let I : Finset (Fin (finrank ℂ E)) := Finset.univ.filter fun i => (i : ℕ) < n
    let W : Submodule ℂ E := Submodule.span ℂ (b '' (I : Set (Fin (finrank ℂ E))))
    let k : Fin (finrank ℂ E) := ⟨n, Nat.lt_of_not_ge hn⟩
    have hWdim : finrank ℂ W = n := by
      rw [D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.finrank_span_image b I]
      have hI : I = Finset.Iio k := by
        ext i
        simp [I, k, Fin.lt_def]
      rw [hI, Fin.card_Iio]
    have hPrank : W.starProjection.rank = (n : Cardinal) := by
      change Module.rank ℂ W.starProjection.range = (n : Cardinal)
      rw [Submodule.range_starProjection, ← Module.finrank_eq_rank' ℂ W, hWdim]
    let R : E →L[ℂ] F := T ∘L W.starProjection
    have hRrank : R.rank ≤ (n : Cardinal) := by
      change (T.toLinearMap.comp W.starProjection.toLinearMap).rank ≤ (n : Cardinal)
      apply Cardinal.lift_le.{u, v}.mp
      rw [Cardinal.lift_natCast]
      exact (LinearMap.lift_rank_comp_le_right W.starProjection.toLinearMap T.toLinearMap).trans
        (by simpa only [Cardinal.lift_natCast] using Cardinal.lift_le.mpr hPrank.le)
    have htailQuad {y : E} (hy : y ∈ Wᗮ) :
        RCLike.re ⟪(A.adjoint ∘ₗ A) y, y⟫_ℂ ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
      rw [D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hGram rfl y,
        show A.singularValues n ^ 2 * ‖y‖ ^ 2 =
          ∑ i : Fin (finrank ℂ E), A.singularValues n ^ 2 * ‖b.repr y i‖ ^ 2 by
            rw [← Finset.mul_sum, D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.sum_sq_norm_repr_eq_sq_norm]]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : (i : ℕ) < n
      · have hmem : b i ∈ W := Submodule.subset_span ⟨i, by simp [I, hi], rfl⟩
        have hz : b.repr y i = 0 := by
          rw [b.repr_apply_apply]
          exact (Submodule.mem_orthogonal W y).mp hy _ hmem
        change hGram.eigenvalues rfl i * ‖b.repr y i‖ ^ 2 ≤ _
        rw [hz]; simp
      · have hval : hGram.eigenvalues rfl i ≤ A.singularValues n ^ 2 := by
          rw [A.sq_singularValues_fin rfl k]
          exact hGram.eigenvalues_antitone rfl (Nat.le_of_not_gt hi)
        exact mul_le_mul_of_nonneg_right hval (sq_nonneg _)
    have htailNorm {y : E} (hy : y ∈ Wᗮ) : ‖T y‖ ≤ A.singularValues n * ‖y‖ := by
      have hsq : ‖T y‖ ^ 2 ≤ A.singularValues n ^ 2 * ‖y‖ ^ 2 := by
        have h := htailQuad hy
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq] at h
        exact h
      apply le_of_sq_le_sq (by nlinarith [hsq])
        (mul_nonneg (A.singularValues_nonneg n) (norm_nonneg y))
    have htailOpNorm : ‖T ∘L Wᗮ.starProjection‖ ≤ A.singularValues n := by
      refine (T ∘L Wᗮ.starProjection).opNorm_le_bound (A.singularValues_nonneg n) fun x => ?_
      exact (htailNorm (Wᗮ.starProjection_apply_mem x)).trans
        (mul_le_mul_of_nonneg_left (Wᗮ.norm_starProjection_apply_le x) (A.singularValues_nonneg n))
    have herr : T - R = T ∘L Wᗮ.starProjection := by
      ext x
      change T x - T (W.starProjection x) = T (Wᗮ.starProjection x)
      rw [Submodule.starProjection_orthogonal_val, map_sub]
    have herror : approximation_number T n ≤ ‖T - R‖ :=
      approximation_number_le_error T hRrank
    rw [herr] at herror
    exact herror.trans htailOpNorm

/-- Finite spectral identification, with the same zero-based index on both sides. -/
theorem approximation_number_eq_singular_value (T : E →L[ℂ] F) (n : ℕ) :
    approximation_number T n = T.toLinearMap.singularValues n :=
  le_antisymm (approximation_number_le_singular_value T n) (singular_value_le_approximation_number T n)

end Finite

/-- Literal finite prefix of the single native rank-error infimum. -/
def ky_fan_gauge (T : E →L[ℂ] F) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range k, approximation_number T n

section FiniteSameUniverse
variable {X Y : Type u}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
open D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

private theorem finite_prefix_saturates (A : X →ₗ[ℂ] Y) (k : ℕ) :
    kyFanSum k A = kyFanSum (min k (min (finrank ℂ X) (finrank ℂ Y))) A := by
  let m := min k (min (finrank ℂ X) (finrank ℂ Y))
  change (∑ i : Fin k, A.singularValues (i : ℕ)) = ∑ i : Fin m, A.singularValues (i : ℕ)
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left _ _))
  intro i hik him
  apply A.singularValues_eq_zero_iff_le_finrank_range.mpr
  have hx := A.finrank_range_le
  have hy := Submodule.finrank_le A.range
  have hi := Finset.mem_range.mp hik
  have him' := Nat.le_of_not_gt (fun h => him (Finset.mem_range.mpr h))
  omega

private theorem finite_spectral_triangle (S T : X →ₗ[ℂ] Y) (k : ℕ) :
    kyFanSum k (S + T) ≤ kyFanSum k S + kyFanSum k T := by
  classical
  let m := min k (min (finrank ℂ X) (finrank ℂ Y))
  have hmX : m ≤ finrank ℂ X := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  have hmY : m ≤ finrank ℂ Y := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  obtain ⟨a, b, ha, hb, hsum⟩ :=
    exists_orthonormal_re_sum_inner_map_eq_ky_fan_sum (S + T) hmX hmY
  rw [finite_prefix_saturates (S + T) k, finite_prefix_saturates S k, finite_prefix_saturates T k]
  change kyFanSum m (S + T) ≤ kyFanSum m S + kyFanSum m T
  rw [← hsum]
  have hsplit : RCLike.re (∑ i, ⟪a i, (S + T) (b i)⟫_ℂ) =
      RCLike.re (∑ i, ⟪a i, S (b i)⟫_ℂ) + RCLike.re (∑ i, ⟪a i, T (b i)⟫_ℂ) := by
    simp [inner_add_right, Finset.sum_add_distrib]
  rw [hsplit]
  exact add_le_add (re_sum_inner_map_le_ky_fan_sum hmX ha hb)
    (re_sum_inner_map_le_ky_fan_sum hmX ha hb)

private theorem finite_same_universe_triangle (S T : X →L[ℂ] Y) (k : ℕ) :
    ky_fan_gauge (S + T) k ≤ ky_fan_gauge S k + ky_fan_gauge T k := by
  have hid (A : X →L[ℂ] Y) : ky_fan_gauge A k = kyFanSum k A.toLinearMap := by
    unfold ky_fan_gauge kyFanSum
    rw [Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun n _ => approximation_number_eq_singular_value A n
  rw [hid, hid, hid]
  exact finite_spectral_triangle S.toLinearMap T.toLinearMap k
end FiniteSameUniverse

private theorem approximation_number_contract
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (B : F →L[ℂ] Y) (T : E →L[ℂ] F) (A : X →L[ℂ] E)
    (hB : ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) (n : ℕ) :
    approximation_number (B ∘L T ∘L A) n ≤ approximation_number T n := by
  calc
    approximation_number (B ∘L T ∘L A) n
        ≤ ‖B‖ * approximation_number (T ∘L A) n :=
      approximation_number_comp_le_norm_mul B (T ∘L A) n
    _ ≤ 1 * approximation_number (T ∘L A) n :=
      mul_le_mul_of_nonneg_right hB (approximation_number_nonneg _ _)
    _ = approximation_number (T ∘L A) n := one_mul _
    _ ≤ approximation_number T n * ‖A‖ := approximation_number_comp_le_mul_norm T A n
    _ ≤ approximation_number T n * 1 :=
      mul_le_mul_of_nonneg_left hA (approximation_number_nonneg _ _)
    _ = approximation_number T n := mul_one _

private theorem approximation_number_coordinates_eq
    {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    (T : E →L[ℂ] F) (e : E ≃ₗᵢ[ℂ] X) (f : F ≃ₗᵢ[ℂ] Y) (n : ℕ) :
    approximation_number (f.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap) n = approximation_number T n := by
  let U := f.toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hback : f.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L U ∘L
        e.toContinuousLinearEquiv.toContinuousLinearMap = T := by
    ext x
    simp [U]
  apply le_antisymm
  · exact approximation_number_contract _ T _ f.toLinearIsometry.norm_toContinuousLinearMap_le
      e.symm.toLinearIsometry.norm_toContinuousLinearMap_le n
  · calc
      approximation_number T n = approximation_number (f.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L U ∘L e.toContinuousLinearEquiv.toContinuousLinearMap) n := congrArg (fun A => approximation_number A n) hback.symm
      _ ≤ approximation_number U n := approximation_number_contract _ U _
        f.symm.toLinearIsometry.norm_toContinuousLinearMap_le
        e.toLinearIsometry.norm_toContinuousLinearMap_le n

private theorem finite_triangle [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (S T : E →L[ℂ] F) (k : ℕ) :
    ky_fan_gauge (S + T) k ≤ ky_fan_gauge S k + ky_fan_gauge T k := by
  let e := (stdOrthonormalBasis ℂ E).repr
  let f := (stdOrthonormalBasis ℂ F).repr
  let C (A : E →L[ℂ] F) := f.toContinuousLinearEquiv.toContinuousLinearMap ∘L A ∘L
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hid (A : E →L[ℂ] F) : ky_fan_gauge (C A) k = ky_fan_gauge A k :=
    Finset.sum_congr rfl fun n _ => approximation_number_coordinates_eq A e f n
  have hsum : C (S + T) = C S + C T := by ext x; simp [C]
  rw [← hid (S + T), ← hid S, ← hid T, hsum]
  exact finite_same_universe_triangle (C S) (C T) k

private theorem approximation_number_restrict_le
    (T : E →L[ℂ] F) (n : ℕ) (V : Submodule ℂ E) :
    approximation_number (T ∘L V.subtypeL) n ≤ approximation_number T n := by
  exact (approximation_number_comp_le_mul_norm T V.subtypeL n).trans
    (by simpa using mul_le_mul_of_nonneg_left V.norm_subtypeL_le (approximation_number_nonneg T n))

private theorem approximation_number_restrict_mono (T : E →L[ℂ] F) (n : ℕ) {U V : Submodule ℂ E}
    (hUV : U ≤ V) :
    (approximation_number (T ∘L U.subtypeL)) n ≤ (approximation_number (T ∘L V.subtypeL)) n := by
  let J : U →L[ℂ] V :=
    (Submodule.inclusion hUV).mkContinuous 1 fun x => by
      -- names the application so the norm bound applies to it directly.
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp
  have hJnorm : ‖J‖ ≤ (1 : ℝ) :=
    J.opNorm_le_bound zero_le_one fun x => by
      -- names the application so the norm bound applies to it directly.
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp
  have hcomp : T ∘L U.subtypeL = (T ∘L V.subtypeL) ∘L J := by
    ext x
    rfl
  rw [hcomp]
  calc
    (approximation_number ((T ∘L V.subtypeL) ∘L J)) n
        ≤ (approximation_number (T ∘L V.subtypeL)) n * ‖J‖ :=
      (approximation_number_comp_le_mul_norm (T ∘L V.subtypeL)) J n
    _ ≤ (approximation_number (T ∘L V.subtypeL)) n * 1 :=
      mul_le_mul_of_nonneg_left hJnorm (approximation_number_nonneg _ _)
    _ = (approximation_number (T ∘L V.subtypeL)) n := by rw [mul_one]

/-- Compressing the codomain to a subspace that already contains the range preserves every
approximation number. -/
private theorem approximation_number_orthogonalProjectionOnto_comp_eq
    (W : Submodule ℂ F) [W.HasOrthogonalProjection]
    (A : E →L[ℂ] F) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    (approximation_number (W.orthogonalProjectionOnto ∘L A)) n = (approximation_number A) n := by
  set AW : E →L[ℂ] W := W.orthogonalProjectionOnto ∘L A with hAW
  have hfactor : W.subtypeL ∘L AW = A := by
    ext x
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  have hproj : ‖W.orthogonalProjectionOnto‖ ≤ (1 : ℝ) := W.orthogonalProjectionOnto_norm_le
  have hsub : ‖W.subtypeL‖ ≤ (1 : ℝ) := W.norm_subtypeL_le
  refine le_antisymm ?_ ?_
  · calc
      (approximation_number AW) n
          ≤ ‖W.orthogonalProjectionOnto‖ * (approximation_number A) n :=
        approximation_number_comp_le_norm_mul
          W.orthogonalProjectionOnto A n
      _ ≤ 1 * (approximation_number A) n :=
        mul_le_mul_of_nonneg_right hproj (approximation_number_nonneg _ _)
      _ = (approximation_number A) n := by rw [one_mul]
  · rw [← hfactor]
    calc
      (approximation_number (W.subtypeL ∘L AW)) n
          ≤ ‖W.subtypeL‖ * (approximation_number AW) n :=
        approximation_number_comp_le_norm_mul W.subtypeL AW n
      _ ≤ 1 * (approximation_number AW) n :=
        mul_le_mul_of_nonneg_right hsub (approximation_number_nonneg _ _)
      _ = (approximation_number AW) n := by rw [one_mul]

/-- The Ky Fan form of `approximation_number_orthogonalProjectionOnto_comp_eq`. -/
private theorem ky_fan_gauge_orthogonalProjectionOnto_comp_eq
    (W : Submodule ℂ F) [W.HasOrthogonalProjection]
    (A : E →L[ℂ] F) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    (ky_fan_gauge (W.orthogonalProjectionOnto ∘L A)) k = (ky_fan_gauge A) k :=
  Finset.sum_congr rfl fun n _ =>
    approximation_number_orthogonalProjectionOnto_comp_eq W A hA n


private theorem finite_source_triangle
    {V G : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (k : ℕ) (A B : V →L[ℂ] G) :
    (ky_fan_gauge (A + B)) k ≤ (ky_fan_gauge A) k + (ky_fan_gauge B) k := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let C : V × V →L[ℂ] G :=
    A ∘L fst ℂ V V + B ∘L snd ℂ V V
  let W : Submodule ℂ G := C.range
  let : FiniteDimensional ℂ W := by
    apply FiniteDimensional.of_surjective C.rangeRestrict.toLinearMap
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  let : W.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hA : ∀ x, A x ∈ W := fun x => ⟨(x, 0), by simp [C]⟩
  have hB : ∀ x, B x ∈ W := fun x => ⟨(0, x), by simp [C]⟩
  have hAB : ∀ x, (A + B) x ∈ W := fun x => W.add_mem (hA x) (hB x)
  let AW : V →L[ℂ] W := W.orthogonalProjectionOnto ∘L A
  let BW : V →L[ℂ] W := W.orthogonalProjectionOnto ∘L B
  have hsum : W.orthogonalProjectionOnto ∘L (A + B) = AW + BW := by
    ext x
    simp [AW, BW]
  have htri := finite_triangle AW BW k
  calc
    (ky_fan_gauge (A + B)) k
        = (ky_fan_gauge (W.orthogonalProjectionOnto ∘L (A + B))) k :=
      (ky_fan_gauge_orthogonalProjectionOnto_comp_eq W (A + B) hAB k).symm
    _ = (ky_fan_gauge (AW + BW)) k := by rw [hsum]
    _ ≤ (ky_fan_gauge AW) k + (ky_fan_gauge BW) k := htri
    _ = (ky_fan_gauge A) k + (ky_fan_gauge B) k := by
      rw [ky_fan_gauge_orthogonalProjectionOnto_comp_eq W A hA k,
        ky_fan_gauge_orthogonalProjectionOnto_comp_eq W B hB k]


private theorem ky_fan_gauge_add_le_of_exists_finiteRestriction {S T : E →L[ℂ] F}
    (hfr : ∀ (n : ℕ) (ε : ℝ), 0 < ε → ∃ v : Fin (n + 1) → E,
      (approximation_number (S + T)) n <
        (approximation_number ((S + T) ∘L (Submodule.span ℂ (Set.range v)).subtypeL)) n + ε)
    (k : ℕ) :
    (ky_fan_gauge (S + T)) k ≤ (ky_fan_gauge S) k + (ky_fan_gauge T) k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [ky_fan_gauge]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hδ : 0 < ε / (k : ℝ) := div_pos hε hkreal
  choose v hv using fun n => hfr n (ε / (k : ℝ)) hδ
  let β : Type := Σ n : Fin k, Fin (n.1 + 1)
  let w : β → E := fun p => v p.1.1 p.2
  let V : Submodule ℂ E := Submodule.span ℂ (Set.range w)
  let : FiniteDimensional ℂ V := Module.Finite.span_of_finite ℂ (Set.finite_range w)
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let SV : V →L[ℂ] F := S ∘L V.subtypeL
  let TV : V →L[ℂ] F := T ∘L V.subtypeL
  have hsumRestrict : (S + T) ∘L V.subtypeL = SV + TV := by
    ext x
    rfl
  have hterm : ∀ n ∈ Finset.range k,
      (approximation_number (S + T)) n ≤ (approximation_number (SV + TV)) n + ε / (k : ℝ) := by
    intro n hn
    let U : Submodule ℂ E := Submodule.span ℂ (Set.range (v n))
    have hUV : U ≤ V := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨j, rfl⟩
      exact Submodule.subset_span ⟨(⟨⟨n, Finset.mem_range.mp hn⟩, j⟩ : β), rfl⟩
    calc
      (approximation_number (S + T)) n
          ≤ (approximation_number ((S + T) ∘L U.subtypeL)) n + ε / (k : ℝ) := (hv n).le
      _ ≤ (approximation_number ((S + T) ∘L V.subtypeL)) n + ε / (k : ℝ) :=
        by gcongr; exact (approximation_number_restrict_mono (S + T)) n hUV
      _ = (approximation_number (SV + TV)) n + ε / (k : ℝ) := by rw [hsumRestrict]
  have hlocal : (ky_fan_gauge (S + T)) k ≤ (ky_fan_gauge (SV + TV)) k + ε := by
    calc
      (ky_fan_gauge (S + T)) k ≤ ∑ n ∈ Finset.range k,
          ((approximation_number (SV + TV)) n + ε / (k : ℝ)) := Finset.sum_le_sum hterm
      _ = (ky_fan_gauge (SV + TV)) k + (k : ℝ) * (ε / (k : ℝ)) := by
        rw [ky_fan_gauge, Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = (ky_fan_gauge (SV + TV)) k + ε := by rw [mul_div_cancel₀ ε hkreal.ne']
  have hrestrictS : (ky_fan_gauge SV) k ≤ (ky_fan_gauge S) k :=
    Finset.sum_le_sum fun n _ => (approximation_number_restrict_le S) n V
  have hrestrictT : (ky_fan_gauge TV) k ≤ (ky_fan_gauge T) k :=
    Finset.sum_le_sum fun n _ => (approximation_number_restrict_le T) n V
  calc
    (ky_fan_gauge (S + T)) k ≤ (ky_fan_gauge (SV + TV)) k + ε := hlocal
    _ ≤ ((ky_fan_gauge SV) k + (ky_fan_gauge TV) k) + ε := by
      gcongr
      exact finite_source_triangle k SV TV
    _ ≤ ((ky_fan_gauge S) k + (ky_fan_gauge T) k) + ε := by gcongr


/-- Every positive tolerance admits a finite source restriction with strictly smaller error. -/
theorem exists_finite_restriction_add_gt [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℂ] F) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E, approximation_number T n <
      approximation_number (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL) n + ε := by
  by_cases hsmall : approximation_number T n < ε
  · exact ⟨fun _ => 0, hsmall.trans_le
      (le_add_of_nonneg_left (approximation_number_nonneg _ _))⟩
  · have hεle : ε ≤ approximation_number T n := le_of_not_gt hsmall
    obtain ⟨s, hrs, v, hv, hV⟩ := exists_independent_lower_bound T n
      (sub_nonneg.mpr hεle) (sub_lt_self _ hε)
    let V := Submodule.span ℂ (Set.range v)
    let b : Module.Basis (Fin (n + 1)) ℂ V := Module.Basis.span hv
    let w : Fin (n + 1) → V := fun i => b i
    have hw : LinearIndependent ℂ w := b.linearIndependent
    have hs : s ≤ approximation_number (T ∘L V.subtypeL) n := by
      apply lower_bound_of_independent (T ∘L V.subtypeL) n w hw
      intro x _ hx
      have h := hV (x : E) x.property
      have hxE : ‖(x : E)‖ = 1 := hx
      change s ≤ ‖T (x : E)‖
      simpa only [hxE, mul_one] using h
    exact ⟨v, by change approximation_number T n < approximation_number (T ∘L V.subtypeL) n + ε; linarith⟩

/-- The Ky Fan triangle inequality for arbitrary independent-universe complex Hilbert spaces. -/
theorem ky_fan_gauge_add_le [CompleteSpace E] [CompleteSpace F]
    (S T : E →L[ℂ] F) (k : ℕ) :
    ky_fan_gauge (S + T) k ≤ ky_fan_gauge S k + ky_fan_gauge T k :=
  ky_fan_gauge_add_le_of_exists_finiteRestriction
    (fun n ε hε => exists_finite_restriction_add_gt (S + T) n ε hε) k

end
end D5.S3.HilbertOperators.Approximation.KyFanTriangle
