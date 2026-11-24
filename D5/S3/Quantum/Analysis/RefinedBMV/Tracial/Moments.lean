/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/Moments
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Simultaneous approximation of powers by finite positive operator moments. -/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Topology.PartitionOfUnity

/-! Simultaneous approximation of powers by finite positive operator moments. -/

open scoped BigOperators

namespace RefinedBMV.Tracial

/-- One finite family of positive weights approximates all the prescribed powers of `X`. -/
theorem exists_positive_moment_approximation
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (X : A) (hX : 0 ≤ X) (K : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (x : Fin m → ℝ) (P : Fin m → A),
      (∀ i, x i ∈ spectrum ℝ X) ∧
      (∀ i, 0 ≤ x i) ∧
      (∀ i, 0 ≤ P i) ∧
      (∑ i, P i) = 1 ∧
      ∀ k ∈ K, ‖(∑ i, (x i ^ k) • P i) - X ^ k‖ ≤ ε := by
  classical
  let S : Set ℝ := spectrum ℝ X
  letI : CompactSpace S :=
    isCompact_iff_compactSpace.mp
      (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) X)
  let coord : C(S, ℝ) := (ContinuousMap.id ℝ).restrict S
  let U (x : S) : Set S :=
    ⋂ k ∈ K, {z : S | ‖coord x ^ k - coord z ^ k‖ < ε}
  have hU (x : S) : IsOpen (U x) := by
    refine isOpen_biInter_finset (s := K) fun k _ ↦ ?_
    have hc : Continuous (fun _ : S ↦ coord x ^ k) := continuous_const
    exact isOpen_lt (hc.sub (coord.continuous.pow k)).norm continuous_const
  have hcover : (Set.univ : Set S) ⊆ ⋃ x, U x := by
    intro z _
    refine Set.mem_iUnion.mpr ⟨z, Set.mem_iInter₂.mpr ?_⟩
    intro k _
    change ‖coord z ^ k - coord z ^ k‖ < ε
    simpa only [sub_self, norm_zero] using hε
  obtain ⟨t, ht⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set S)).elim_finite_subcover U hU hcover

  let e := t.equivFin.symm
  let node (i : Fin t.card) : S := (e i).val
  have hfiniteCover : (Set.univ : Set S) ⊆ ⋃ i : Fin t.card, U (node i) := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := Set.mem_iUnion₂.mp (ht hz)
    obtain ⟨i, hi⟩ := e.surjective (⟨a, ha⟩ : ↥t)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change z ∈ U (e i).val
    simpa only [hi] using hza
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : Fin t.card ↦ U (node i)) (fun i ↦ hU (node i)) hfiniteCover
  have hsum (z : S) : (∑ i, ρ i z) = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (Set.mem_univ z)
  have hsumMap : (∑ i, ρ i) = (1 : C(S, ℝ)) := by
    apply ContinuousMap.ext
    intro z
    simpa only [ContinuousMap.sum_apply, ContinuousMap.one_apply] using hsum z

  have hXsa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX
  let Φ : C(S, ℝ) →⋆ₐ[ℝ] A := cfcHom (R := ℝ) hXsa
  have hΦ : Φ coord = X := cfcHom_id (R := ℝ) hXsa
  refine ⟨t.card, (fun i ↦ coord (node i)), (fun i ↦ Φ (ρ i)), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i ↦ (node i).property
  · exact fun i ↦ spectrum_nonneg_of_nonneg hX (node i).property
  · intro i
    change 0 ≤ cfcHom (R := ℝ) hXsa (ρ i)
    exact (cfcHom_nonneg_iff (R := ℝ) hXsa).mpr
      (ContinuousMap.le_def.mpr fun z ↦ ρ.nonneg i z)
  · change (∑ i, Φ (ρ i)) = 1
    rw [← map_sum Φ, hsumMap, map_one]
  · intro k hk
    let F : C(S, ℝ) := (∑ i, (coord (node i) ^ k) • ρ i) - coord ^ k
    calc
      ‖(∑ i, (coord (node i) ^ k) • Φ (ρ i)) - X ^ k‖ = ‖Φ F‖ := by
        simp only [F, map_sub, map_sum, map_smul, map_pow, hΦ]
      _ = ‖F‖ := norm_cfcHom (𝕜 := ℝ) X F hXsa
      _ ≤ ε := by
        apply (ContinuousMap.norm_le F hε.le).mpr
        intro z
        have hweighted : (∑ i, coord z ^ k * ρ i z) = coord z ^ k := by
          rw [← Finset.mul_sum, hsum z, mul_one]
        have hF : F z = ∑ i, (coord (node i) ^ k - coord z ^ k) * ρ i z := by
          simp only [F, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
            ContinuousMap.smul_apply, ContinuousMap.pow_apply, smul_eq_mul,
            sub_mul, Finset.sum_sub_distrib, hweighted]
        rw [hF]
        calc
          ‖∑ i, (coord (node i) ^ k - coord z ^ k) * ρ i z‖
              ≤ ∑ i, ‖(coord (node i) ^ k - coord z ^ k) * ρ i z‖ :=
            norm_sum_le Finset.univ _
          _ ≤ ∑ i, ε * ρ i z := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            by_cases hzero : ρ i z = 0
            · simp only [hzero, mul_zero, norm_zero, le_refl]
            · have hzU : z ∈ U (node i) :=
                hρ i (subset_closure (show z ∈ Function.support (ρ i) from hzero))
              have hlocal : ‖coord (node i) ^ k - coord z ^ k‖ < ε :=
                (Set.mem_iInter₂.mp hzU) k hk
              rw [norm_mul, Real.norm_of_nonneg (ρ.nonneg i z)]
              exact mul_le_mul_of_nonneg_right hlocal.le (ρ.nonneg i z)
          _ = ε := by rw [← Finset.mul_sum, hsum z, mul_one]

end RefinedBMV.Tracial
