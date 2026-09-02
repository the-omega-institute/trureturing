/- GID: D5/S3/Observer/AgencyReserveStability
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyReserveStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive singular-value reserve is the sharp radius preserving an agency dimension. -/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/- Library-search audit trail (2026-09-02):
   * Repository searches for agency reserve, singular-value margin, low-rank
     distance, rank stability, and safe regions found
     `EpsilonSelfDimension`, which counts threshold crossings but does not
     prove perturbation stability or boundary sharpness. Generalized searches
     found no theorem with the distance-to-low-rank and continuous-safe-region
     clauses below.
   * Pinned Mathlib supplies `Metric.infDist_le_dist_of_mem`,
     `LinearMap.singularValues_pos_iff_lt_finrank_range`, and
     `LinearMap.singularValues_eq_zero_iff_le_finrank_range`; these are reused
     directly. It has no Eckart--Young--Mirsky theorem or continuity theorem
     for `LinearMap.singularValues`.
   * Accordingly, the best-low-rank identity, attainment, and continuity of
     the selected singular value are explicit premises. The zero-based index
     `k` corresponds to the source's one-based `r = k + 1`, avoiding truncated
     natural subtraction in `r - 1`. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace D5.S3.Observer.AgencyReserveStability

/-- Continuous linear operators whose range has dimension at most `k`. -/
def rankAtMost
    {K State Output : Type*} [RCLike K]
    [NormedAddCommGroup State] [NormedSpace K State]
    [NormedAddCommGroup Output] [NormedSpace K Output]
    (k : ℕ) : Set (State →L[K] Output) :=
  {operator | Module.finrank K operator.toLinearMap.range ≤ k}

/-- The zero-based `k`th agency reserve of an operator. In one-based notation
this is `Reserve_(k+1)`. -/
def agencyReserve
    {K State Output : Type*} [RCLike K]
    [NormedAddCommGroup State] [InnerProductSpace K State]
    [FiniteDimensional K State]
    [NormedAddCommGroup Output] [InnerProductSpace K Output]
    [FiniteDimensional K Output]
    (operator : State →L[K] Output) (k : ℕ) : ℝ :=
  operator.toLinearMap.singularValues k

/-- States whose `k`th reserve is at least `epsilon`. -/
def agencySafeRegion
    {K State Output X : Type*} [RCLike K]
    [NormedAddCommGroup State] [InnerProductSpace K State]
    [FiniteDimensional K State]
    [NormedAddCommGroup Output] [InnerProductSpace K Output]
    [FiniteDimensional K Output]
    (system : X → State →L[K] Output) (k : ℕ) (epsilon : ℝ) : Set X :=
  {x | epsilon ≤ agencyReserve (system x) k}

/-- Assume the Eckart--Young distance identity is attained by `best`, and the
selected singular value varies continuously along a family of operators.
Then every perturbation strictly smaller than the reserve preserves the
`k + 1`st range dimension. The attaining low-rank operator constructs a
boundary perturbation of exactly the reserve that destroys that dimension.
Moreover every threshold below the reserve defines a neighborhood inside the
corresponding safe region, so rank can drop at the base point only when the
reserve is zero.

The explicit nonemptiness conclusion guards against the `infDist` empty-set
convention. -/
theorem agency_reserve_stability
    {K State Output X : Type*} [RCLike K]
    [NormedAddCommGroup State] [InnerProductSpace K State]
    [FiniteDimensional K State]
    [NormedAddCommGroup Output] [InnerProductSpace K Output]
    [FiniteDimensional K Output]
    [TopologicalSpace X]
    (system : X → State →L[K] Output) (x : X) (k : ℕ)
    (best : State →L[K] Output)
    (hBestRank : best ∈ rankAtMost (K := K) (State := State) (Output := Output) k)
    (hEckartYoung :
      Metric.infDist (system x)
          (rankAtMost (K := K) (State := State) (Output := Output) k) =
        agencyReserve (system x) k)
    (hAttained :
      dist (system x) best =
        Metric.infDist (system x)
          (rankAtMost (K := K) (State := State) (Output := Output) k))
    (hReservePositive : 0 < agencyReserve (system x) k)
    (hContinuous : ContinuousAt (fun y => agencyReserve (system y) k) x) :
    (rankAtMost (K := K) (State := State) (Output := Output) k).Nonempty ∧
      Metric.infDist (system x)
          (rankAtMost (K := K) (State := State) (Output := Output) k) =
        agencyReserve (system x) k ∧
      (∀ perturbation : State →L[K] Output,
        ‖perturbation‖ < agencyReserve (system x) k →
          k + 1 ≤ Module.finrank K (system x + perturbation).toLinearMap.range ∧
          0 < agencyReserve (system x + perturbation) k) ∧
      (∃ perturbation : State →L[K] Output,
        ‖perturbation‖ = agencyReserve (system x) k ∧
          Module.finrank K (system x + perturbation).toLinearMap.range ≤ k ∧
          agencyReserve (system x + perturbation) k = 0) ∧
      (∀ epsilon : ℝ, epsilon < agencyReserve (system x) k →
        ∀ᶠ y in 𝓝 x, y ∈ agencySafeRegion system k epsilon) ∧
      (∀ᶠ y in 𝓝 x,
        k + 1 ≤ Module.finrank K (system y).toLinearMap.range) := by
  let lowRank := rankAtMost (K := K) (State := State) (Output := Output) k
  have hLowRankNonempty : lowRank.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [lowRank, rankAtMost, Set.mem_ofPred_eq]
    rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]
    exact Nat.zero_le k
  have hRobust : ∀ perturbation : State →L[K] Output,
      ‖perturbation‖ < agencyReserve (system x) k →
        k + 1 ≤ Module.finrank K (system x + perturbation).toLinearMap.range ∧
        0 < agencyReserve (system x + perturbation) k := by
    intro perturbation hSmall
    have hNotLowRank : system x + perturbation ∉ lowRank := by
      intro hLowRank
      have hDistanceBound :
          Metric.infDist (system x) lowRank ≤
            dist (system x) (system x + perturbation) :=
        Metric.infDist_le_dist_of_mem hLowRank
      have hNormDistance :
          dist (system x) (system x + perturbation) = ‖perturbation‖ := by
        simp [dist_eq_norm]
      rw [show lowRank = rankAtMost (K := K) (State := State)
        (Output := Output) k from rfl, hEckartYoung, hNormDistance] at hDistanceBound
      exact (not_lt_of_ge hDistanceBound) hSmall
    have hNotRank :
        ¬Module.finrank K (system x + perturbation).toLinearMap.range ≤ k := by
      simpa [lowRank, rankAtMost] using hNotLowRank
    have hRank : k < Module.finrank K (system x + perturbation).toLinearMap.range :=
      Nat.lt_of_not_ge hNotRank
    have hSingularPositive : 0 < agencyReserve (system x + perturbation) k := by
      rw [agencyReserve]
      exact (system x + perturbation).toLinearMap
        |>.singularValues_pos_iff_lt_finrank_range.mpr hRank
    exact ⟨Nat.succ_le_iff.mpr hRank, hSingularPositive⟩
  have hBoundary : ∃ perturbation : State →L[K] Output,
      ‖perturbation‖ = agencyReserve (system x) k ∧
        Module.finrank K (system x + perturbation).toLinearMap.range ≤ k ∧
        agencyReserve (system x + perturbation) k = 0 := by
    refine ⟨best - system x, ?_, ?_, ?_⟩
    · rw [← hEckartYoung, ← hAttained]
      simpa [dist_eq_norm] using norm_sub_rev best (system x)
    · have hSum : system x + (best - system x) = best := by abel
      rw [hSum]
      simpa [lowRank, rankAtMost] using hBestRank
    · have hSum : system x + (best - system x) = best := by abel
      rw [hSum, agencyReserve,
        LinearMap.singularValues_eq_zero_iff_le_finrank_range]
      simpa [lowRank, rankAtMost] using hBestRank
  have hSafe : ∀ epsilon : ℝ, epsilon < agencyReserve (system x) k →
      ∀ᶠ y in 𝓝 x, y ∈ agencySafeRegion system k epsilon := by
    intro epsilon hEpsilon
    have hStrict : ∀ᶠ y in 𝓝 x, epsilon < agencyReserve (system y) k :=
      hContinuous (Ioi_mem_nhds hEpsilon)
    filter_upwards [hStrict] with y hy
    exact hy.le
  have hLocalRank : ∀ᶠ y in 𝓝 x,
      k + 1 ≤ Module.finrank K (system y).toLinearMap.range := by
    have hStrict : ∀ᶠ y in 𝓝 x, 0 < agencyReserve (system y) k :=
      hContinuous (Ioi_mem_nhds hReservePositive)
    filter_upwards [hStrict] with y hy
    rw [agencyReserve] at hy
    exact Nat.succ_le_iff.mpr
      ((system y).toLinearMap.singularValues_pos_iff_lt_finrank_range.mp hy)
  exact ⟨hLowRankNonempty, hEckartYoung, hRobust, hBoundary, hSafe, hLocalRank⟩

#print axioms agency_reserve_stability

end D5.S3.Observer.AgencyReserveStability
