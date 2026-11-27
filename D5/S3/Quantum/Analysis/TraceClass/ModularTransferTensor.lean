/- GID: D5/S3/Quantum/Analysis/TraceClass/ModularTransferTensor
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/ModularTransferTensor
   mirror-E: none(waiver:analytic-hilbert-space-proof)
   anchors: []
   utility: none
   digest: Hilbert tensor representation of reflected Hilbert–Schmidt correlations. -/

import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
The transfer operator in the modular correlation expansion represents a
vector in the completed Hilbert tensor product. Its squared norm equals
the trace of the positive transfer square. This supplies the Hilbert
space step for the order-two sewing question of Jia, arXiv:2611.34922v1.
-/

open Filter
open scoped BigOperators ComplexOrder InnerProductSpace TensorProduct Topology

namespace ModularTransferTensor

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem finite_gram (v : ι → H) (s : Finset ι) :
    ‖∑ i ∈ s, v i‖ ^ 2 =
      ∑ p ∈ s ×ˢ s, (inner ℂ (v p.1) (v p.2)).re := by
  calc
    ‖∑ i ∈ s, v i‖ ^ 2 =
        (inner ℂ (∑ i ∈ s, v i) (∑ j ∈ s, v j)).re :=
      (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    _ = ∑ p ∈ s ×ˢ s, (inner ℂ (v p.1) (v p.2)).re := by
      rw [sum_inner, Finset.sum_product, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sum, Complex.re_sum]

/-- Absolute summability of the pairwise real Gram entries gives convergence
of the vector series in a complete Hilbert space, and identifies its
squared norm with the double Gram sum. It does not require summability of
the individual vector norms. -/
private theorem hasSum_gram [CompleteSpace H] (v : ι → H)
    (hgram : Summable fun p : ι × ι => |(inner ℂ (v p.1) (v p.2)).re|) :
    ∃ limit, HasSum v limit ∧
      ‖limit‖ ^ 2 = ∑' p : ι × ι, (inner ℂ (v p.1) (v p.2)).re := by
  classical
  let gram (p : ι × ι) := (inner ℂ (v p.1) (v p.2)).re
  have habs : Summable (fun p => ‖gram p‖) := by
    simpa only [gram, Real.norm_eq_abs] using hgram
  have hg : Summable gram := habs.of_norm
  have hv : Summable v := by
    refine summable_iff_vanishing_norm.mpr fun ε hε => ?_
    obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hg (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨s.image Prod.fst, fun t ht => ?_⟩
    have hdisj : Disjoint (t ×ˢ t) s := by
      refine Finset.disjoint_left.mpr fun p hp hps => ?_
      exact Finset.disjoint_left.mp ht (Finset.mem_product.mp hp).1
        (Finset.mem_image_of_mem Prod.fst hps)
    have hsmall := hs (t ×ˢ t) hdisj
    change ‖∑ p ∈ t ×ˢ t, (inner ℂ (v p.1) (v p.2)).re‖ < ε ^ 2 at hsmall
    rw [← finite_gram v, Real.norm_of_nonneg (sq_nonneg _)] at hsmall
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsmall
  have hprod : Tendsto (fun s : Finset ι => s ×ˢ s) atTop atTop := by
    refine tendsto_atTop.mpr fun s => eventually_atTop.mpr
      ⟨s.image Prod.fst ∪ s.image Prod.snd, ?_⟩
    intro t ht p hp
    exact Finset.mem_product.mpr
      ⟨ht (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)),
        ht (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp))⟩
  refine ⟨∑' i, v i, hv.hasSum, ?_⟩
  have hnorm : Tendsto (fun s : Finset ι => ‖∑ i ∈ s, v i‖ ^ 2) atTop
      (𝓝 (‖∑' i, v i‖ ^ 2)) :=
    (continuous_norm.pow 2).continuousAt.tendsto.comp hv.hasSum
  have hsum := hg.hasSum.comp hprod
  change Tendsto (fun s : Finset ι => ∑ p ∈ s ×ˢ s, gram p) atTop
    (𝓝 (∑' p, gram p)) at hsum
  exact tendsto_nhds_unique hnorm (by simpa only [gram, ← finite_gram v] using hsum)

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private theorem right_orthogonal_tensor (a : ι → H) (b : ι → K)
    (hb : Orthonormal ℂ b) (ha : Summable fun i => ‖a i‖ ^ 2) :
    ∃ vector : UniformSpace.Completion (H ⊗[ℂ] K),
      ‖vector‖ ^ 2 = ∑' i, ‖a i‖ ^ 2 ∧
      ∀ x : H, ∀ y : K,
        HasSum (fun i => inner ℂ (a i) x * inner ℂ (b i) y)
          (inner ℂ vector ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) :
            UniformSpace.Completion (H ⊗[ℂ] K))) := by
  classical
  let v (i : ι) : UniformSpace.Completion (H ⊗[ℂ] K) :=
    a i ⊗ₜ[ℂ] b i
  let diag : ι ↪ ι × ι := ⟨fun i => (i, i), fun _ _ h => congrArg Prod.fst h⟩
  let g := Function.extend diag (fun i => ‖a i‖ ^ 2) 0
  have hg : HasSum g (∑' i, ‖a i‖ ^ 2) := (hasSum_extend_zero diag.injective).2 ha.hasSum
  have g_diag (i : ι) : g (diag i) = ‖a i‖ ^ 2 :=
    diag.injective.extend_apply _ _ i
  have hgram (p : ι × ι) : (inner ℂ (v p.1) (v p.2)).re = g p := by
    rcases p with ⟨i, j⟩
    by_cases hij : i = j
    · subst j
      change (inner ℂ (v i) (v i)).re = g (diag i)
      rw [g_diag]
      simp only [v, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul,
        orthonormal_iff_ite.mp hb, ite_true, mul_one]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    · have hout : ¬ ∃ k, diag k = (i, j) := by
        rintro ⟨k, hk⟩
        exact hij ((congrArg Prod.fst hk).symm.trans (congrArg Prod.snd hk))
      rw [show g (i, j) = 0 from Function.extend_apply' _ _ _ hout]
      simp only [v, UniformSpace.Completion.inner_coe,
        TensorProduct.inner_tmul, orthonormal_iff_ite.mp hb, ite_eq_right hij, mul_zero,
        Complex.zero_re]
  have hnonneg (p : ι × ι) : 0 ≤ g p := by
    by_cases h : ∃ k, diag k = p
    · obtain ⟨k, rfl⟩ := h
      rw [g_diag]
      exact sq_nonneg _
    · rw [show g p = 0 from Function.extend_apply' _ _ _ h]
  obtain ⟨vector, hv, hn⟩ := hasSum_gram v (by
    simpa only [hgram, abs_of_nonneg (hnonneg _)] using hg.summable)
  refine ⟨vector, ?_, fun x y => ?_⟩
  · simpa only [hgram, hg.tsum_eq] using hn
  · let point : UniformSpace.Completion (H ⊗[ℂ] K) := x ⊗ₜ[ℂ] y
    have hs := Complex.hasSum_conj'.2 (hv.mapL (innerSL ℂ point))
    simp only [innerSL_apply_apply, inner_conj_symm] at hs
    simpa only [v, point, UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul] using hs

/-- A Hilbert–Schmidt transfer operator gives a representative of the
reflected correlation in the completed Hilbert tensor product. The
representative's squared norm is the trace of the transfer square. -/
theorem transfer_tensor [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : HilbertSchmidt.IsHilbertSchmidt T) (reflect : H → H)
    (hiso : ∀ x, ‖reflect x‖ = ‖x‖)
    (hsymm : ∀ x y, inner ℂ (reflect x) y = inner ℂ (reflect y) x) :
    ∃ vector : UniformSpace.Completion (H ⊗[ℂ] H),
      ‖vector‖ ^ 2 =
        (trace (star T * T) (HilbertSchmidt.isTraceClass_star_mul_self_of_isHilbertSchmidt hT)).re ∧
      ∀ x y : H, inner ℂ vector
        ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] H) : UniformSpace.Completion (H ⊗[ℂ] H)) =
          inner ℂ (reflect x) (T y) := by
  obtain ⟨s, basis, hb⟩ := hT
  let a (i : s) := reflect (T (basis i))
  have ha : Summable fun i => ‖a i‖ ^ 2 := by simpa only [a, hiso] using hb
  obtain ⟨vector, hn, hpair⟩ := right_orthogonal_tensor a basis basis.orthonormal ha
  refine ⟨vector, ?_, fun x y => ?_⟩
  · rw [hn, trace_eq_of_hilbertBasis_of_nonneg (star_mul_self_nonneg T) _ basis]
    have hentry (i : s) : inner ℂ (basis i) ((star T * T) (basis i)) =
        ((‖T (basis i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
        inner_self_eq_norm_sq_to_K]
      norm_cast
    simp only [hentry, ← Complex.ofReal_tsum, Complex.ofReal_re, a, hiso]
  · have hs := ((basis.hasSum_repr y).mapL T).mapL (innerSL ℂ (reflect x))
    apply (hpair x y).unique
    simpa only [a, hsymm (T _) x, innerSL_apply_apply, ContinuousLinearMap.map_smul,
      inner_smul_right, basis.repr_apply_apply, smul_eq_mul, mul_comm] using hs

/--
info: 'ModularTransferTensor.transfer_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms transfer_tensor

end ModularTransferTensor
