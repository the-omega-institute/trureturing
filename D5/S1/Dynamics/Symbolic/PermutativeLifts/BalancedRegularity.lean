/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity
   generality: I
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/BalancedRegularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual balanced Toeplitz regularity along an essential period structure. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.EssentialPeriodStructure
import D5.S1.Dynamics.Symbolic.PermutativeLifts.PeriodicSkeletonRescaling

/-! The same aligned point has a source period structure: its periods are
positive essential periods, strictly increase, divide the next period, and
cover every signed coordinate. Initial empty skeletons and repeated extracted
periods are removed by the generic extraction theorem. Regularity uses actual
normalized skeleton densities along that structure.
Public escape registrations remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/24726. -/

set_option autoImplicit false

open Set Function SymbolicDynamics.FullShift Filter
open scoped Topology

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced

open PeriodicSkeleton

local instance (n : ℕ) : NeZero (height n) := ⟨Nat.ne_of_gt (height_pos n)⟩

/-- The balanced word heights form a divisibility scale. -/
theorem height_dvd_succ (n : ℕ) : height n ∣ height (n + 1) := by
  refine ⟨3 * (n + 1).factorial, ?_⟩
  rw [height_succ]
  ac_rfl

/-- Every positive shifted height has a nonempty actual periodic skeleton.
The empty initial skeleton at height zero is not asserted essential. -/
theorem aligned_shifted_sites_nonempty (n : ℕ) :
    (sites alignedPeriodicPoint.1 (height (n + 1))).Nonempty := by
  classical
  have hpow : (1 / 3 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hd : 0 < density alignedPeriodicPoint.1 (height (n + 1)) :=
    lt_of_lt_of_le (by linarith) (aligned_periodic_density_lower_bound (n + 1))
  have hcard : 0 < (phases alignedPeriodicPoint.1 (height (n + 1))).card := by
    have hp : 0 < (height (n + 1) : ℝ) := by exact_mod_cast height_pos (n + 1)
    have hcast : 0 < ((phases alignedPeriodicPoint.1 (height (n + 1))).card : ℝ) :=
      (div_pos_iff_of_pos_right hp).mp hd
    exact_mod_cast hcast
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  refine ⟨(j.val : ℤ), ?_⟩
  exact (Finset.mem_filter.mp hj).2

/-- Coordinate periods supplied by the compact-limit construction divide
later factorial heights, so this concrete height scale covers every site. -/
theorem aligned_shifted_sites_cover (i : ℤ) :
    ∃ n : ℕ, CoordinatePeriodic alignedPeriodicPoint.1 (height (n + 1)) i := by
  obtain ⟨p, hp, hi⟩ := alignedPeriodicPoint.2.2 i
  refine ⟨p, coordinate_periodic_of_dvd ?_ hi⟩
  have hd : p ∣ (p + 1).factorial := Nat.dvd_factorial hp (by omega)
  rw [height_succ]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 3) (height p)


/-- The same actual aligned compact-limit point has a genuine source period
structure whose normalized actual skeleton densities converge to one. -/
theorem aligned_has_regular_period_structure :
    ∃ P : PeriodStructure alignedPeriodicPoint.1,
      Tendsto P.skeletonDensity atTop (𝓝 1) := by
  obtain ⟨P, ψ, hψ, hbound, hperiod⟩ := exists_period_structure
    alignedPeriodicPoint.1 (fun n => height (n + 1))
    (fun n => height_pos (n + 1)) (fun n => height_dvd_succ (n + 1))
    aligned_shifted_sites_nonempty aligned_shifted_sites_cover
    (fun p hp => balanced_no_positive_period
      ⟨alignedPeriodicPoint.1, alignedPeriodicPoint_mem⟩ hp)
  have hden (n : ℕ) : P.skeletonDensity n =
      density alignedPeriodicPoint.1 (height (ψ n + 1)) := by
    letI : NeZero (leastPeriod alignedPeriodicPoint.1 (height (ψ n + 1))) :=
      ⟨Nat.ne_of_gt (leastPeriod_pos alignedPeriodicPoint.1 (height_pos (ψ n + 1)))⟩
    have heq (i : ℤ) :
        CoordinatePeriodic alignedPeriodicPoint.1
          (leastPeriod alignedPeriodicPoint.1 (height (ψ n + 1))) i ↔
        CoordinatePeriodic alignedPeriodicPoint.1 (height (ψ n + 1)) i := by
      change i ∈ sites _ _ ↔ i ∈ sites _ _
      rw [sites_leastPeriod_eq]
    have hd := density_eq_of_dvd_of_periodic_coordinates_eq alignedPeriodicPoint.1
      (leastPeriod alignedPeriodicPoint.1 (height (ψ n + 1))) (height (ψ n + 1))
      (leastPeriod_dvd alignedPeriodicPoint.1 _) heq
    simpa only [PeriodStructure.skeletonDensity, hperiod n] using hd
  have hψtop : Tendsto ψ atTop atTop := tendsto_atTop_mono hbound tendsto_id
  have hindex : Tendsto (fun n => ψ n + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hψtop
  refine ⟨P, ?_⟩
  have hfn : P.skeletonDensity = fun n => density alignedPeriodicPoint.1 (height (ψ n + 1)) :=
    funext hden
  rw [hfn]
  exact aligned_periodic_density_tendsto_one.comp hindex

/-- One actual aperiodic Toeplitz generator supplies all source regularity
clauses and generates exactly the actual compact minimal balanced subshift. -/
theorem exists_balanced_regular_toeplitz_generator :
    ∃ y : ℤ → Bool, y ∈ balancedSubshift.carrier ∧ HasPeriodicCoordinates y ∧
      (∀ p : ℕ, 0 < p → shift (p : ℤ) y ≠ y) ∧
      closure (Set.range (fun g : ℤ => shift g y)) = balancedSubshift.carrier ∧
      ∃ P : PeriodStructure y, Tendsto P.skeletonDensity atTop (𝓝 1) := by
  let y : BalancedPoint := ⟨alignedPeriodicPoint.1, alignedPeriodicPoint_mem⟩
  exact ⟨y.1, y.2, alignedPeriodicPoint.2.2,
    (fun p hp => balanced_no_positive_period y hp), balanced_orbit_closure y,
    aligned_has_regular_period_structure⟩

end D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
