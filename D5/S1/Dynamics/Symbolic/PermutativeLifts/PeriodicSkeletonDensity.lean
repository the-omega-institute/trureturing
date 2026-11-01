/- GID: D5/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity
   generality: G
   mirror-B: D5/B/S1/Dynamics/Symbolic/PermutativeLifts/PeriodicSkeletonDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual periodic-skeleton phase densities and balanced density exhaustion. -/

import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedMinimal
import D5.S1.Dynamics.Symbolic.PermutativeLifts.SparseDisagreement
import Mathlib.Analysis.SpecificLimits.Basic

/-! The periodic skeleton uses the actual signed coordinate condition at a
positive period. Its density is the number of periodic residue classes divided
by the period. The balanced estimates below do not claim that the chosen
heights are essential periods, or that a source period structure is supplied.
Public theorem escape registrations remain unfinished under the same-problem
audit issue https://github.com/the-omega-institute/trureturing/issues/24726. -/

set_option autoImplicit false

open Set SymbolicDynamics.FullShift Filter
open scoped Topology

namespace D5.S1.Dynamics.Symbolic.PermutativeLifts

namespace PeriodicSkeleton

/-- Actual period-p coordinate classes, with every integer multiple allowed. -/
noncomputable def phases (y : ℤ → Bool) (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun j =>
    ∀ k : ℤ, y ((j.val : ℤ) + k * (p : ℤ)) = y (j.val : ℤ)

/-- The source's normalized periodic-skeleton count on one complete period. -/
noncomputable def density (y : ℤ → Bool) (p : ℕ) [NeZero p] : ℝ :=
  ((phases y p).card : ℝ) / (p : ℝ)

/-- A skeleton contains at most all residue classes. -/
theorem density_le_one (y : ℤ → Bool) (p : ℕ) [NeZero p] : density y p ≤ 1 := by
  classical
  have hc : (phases y p).card ≤ p := by
    calc
      _ ≤ (Finset.univ : Finset (ZMod p)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = p := by simp
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  apply (div_le_one hp).mpr
  exact_mod_cast hc

end PeriodicSkeleton

namespace Balanced

local instance (n : ℕ) : NeZero (height n) := ⟨Nat.ne_of_gt (height_pos n)⟩

/-- Every actually shared word column is a periodic coordinate class of the
same aligned compact-limit point, not just a periodic word approximation. -/
theorem common_phases_subset_periodic_phases (n : ℕ) :
    (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
      (balancedWord_length n))ᶜ ⊆
      PeriodicSkeleton.phases alignedPeriodicPoint.1 (height n) := by
  classical
  intro j hj
  have hcommon : (balancedWord n false)[j.val]'(by rw [balancedWord_length]; exact j.val_lt) =
      (balancedWord n true)[j.val]'(by rw [balancedWord_length]; exact j.val_lt) := by
    simpa only [Finset.mem_compl, SparseDisagreement.wordDisagreements,
      Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
  obtain ⟨x, hzero, hx⟩ := alignedPeriodicPoint.2.1 n
  have hoff : (x.1 (j.val : ℤ)).2.val = j.val := by
    have hp := tiled_offset_aligned (balancedWord n) (height n) (balancedWord_length n)
      (height_pos n) x hzero (j.val : ℤ)
    have hjlt : (j.val : ℤ) < (height n : ℤ) := by exact_mod_cast j.val_lt
    rw [Int.emod_eq_of_lt (by omega) hjlt] at hp
    omega
  have hc : (balancedWord n false).get ⟨(x.1 (j.val : ℤ)).2.val, by
        simpa only [balancedWord_length] using (x.1 (j.val : ℤ)).2.isLt⟩ =
      (balancedWord n true).get ⟨(x.1 (j.val : ℤ)).2.val, by
        simpa only [balancedWord_length] using (x.1 (j.val : ℤ)).2.isLt⟩ := by
    simpa only [List.get_eq_getElem, hoff] using hcommon
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hx]
  exact tiled_common_column_periodic (balancedWord n) (height n) (balancedWord_length n)
    (height_pos n) x (j.val : ℤ) hc

/-- The actual periodic classes leave at most the known word-disagreement
count of holes. No converse or essential-period assertion is used. -/
theorem aligned_periodic_phases_card_lower_bound (n : ℕ) :
    height n ≤ (PeriodicSkeleton.phases alignedPeriodicPoint.1 (height n)).card +
      disagreementCount n := by
  classical
  have hc := Finset.card_le_card (common_phases_subset_periodic_phases n)
  have hm := SparseDisagreement.wordDisagreements_card (balancedWord n) (height n)
    (balancedWord_length n)
  change _ = disagreementCount n at hm
  have hd : (SparseDisagreement.wordDisagreements (balancedWord n) (height n)
      (balancedWord_length n)).card ≤ height n := by
    calc
      _ ≤ (Finset.univ : Finset (ZMod (height n))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = height n := by simp
  rw [Finset.card_compl, hm] at hc
  simp only [ZMod.card] at hc
  rw [hm] at hd
  omega

/-- The actual skeleton density is at least 1 minus the exact 3^(-n)
word-disagreement fraction. All signed multiples occur in its definition. -/
theorem aligned_periodic_density_lower_bound (n : ℕ) :
    1 - (1 / 3 : ℝ) ^ n ≤ PeriodicSkeleton.density alignedPeriodicPoint.1 (height n) := by
  have hh : 0 < (height n : ℝ) := by exact_mod_cast height_pos n
  have hd : (disagreementCount n : ℝ) / (height n : ℝ) = (1 / 3 : ℝ) ^ n := by
    have hq := congrArg (fun q : ℚ => (q : ℝ)) (disagreement_fraction n)
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_pow, Rat.cast_one,
      Rat.cast_ofNat] using hq
  have hc : (height n : ℝ) ≤
      ((PeriodicSkeleton.phases alignedPeriodicPoint.1 (height n)).card : ℝ) +
      (disagreementCount n : ℝ) := by
    exact_mod_cast aligned_periodic_phases_card_lower_bound n
  rw [← hd]
  apply (le_div_iff₀ hh).mpr
  have hm := div_mul_cancel₀ (disagreementCount n : ℝ) (ne_of_gt hh)
  nlinarith

/-- The actual aligned point's normalized periodic skeletons exhaust density
one along the unbounded divisible balanced height scale. -/
theorem aligned_periodic_density_tendsto_one :
    Tendsto (fun n : ℕ => PeriodicSkeleton.density alignedPeriodicPoint.1 (height n))
      atTop (𝓝 1) := by
  have hp : Tendsto (fun n : ℕ => (1 / 3 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hl : Tendsto (fun n : ℕ => 1 - (1 / 3 : ℝ) ^ n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
    aligned_periodic_density_lower_bound
    (fun n => PeriodicSkeleton.density_le_one alignedPeriodicPoint.1 (height n))

/-- One actual nonperiodic Toeplitz generator has periodic-skeleton density
converging to one and generates the exact compact minimal subshift. -/
theorem exists_balanced_toeplitz_generator_with_density :
    ∃ y : ℤ → Bool, y ∈ balancedSubshift.carrier ∧ HasPeriodicCoordinates y ∧
      (∀ p : ℕ, 0 < p → shift (p : ℤ) y ≠ y) ∧
      closure (Set.range (fun g : ℤ => shift g y)) = balancedSubshift.carrier ∧
      Tendsto (fun n : ℕ => PeriodicSkeleton.density y (height n)) atTop (𝓝 1) := by
  let y : BalancedPoint := ⟨alignedPeriodicPoint.1, alignedPeriodicPoint_mem⟩
  exact ⟨y.1, y.2, alignedPeriodicPoint.2.2,
    (fun _ hp => balanced_no_positive_period y hp), balanced_orbit_closure y,
    aligned_periodic_density_tendsto_one⟩

end Balanced

end D5.S1.Dynamics.Symbolic.PermutativeLifts
