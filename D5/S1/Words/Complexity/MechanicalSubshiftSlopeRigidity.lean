/- GID: D5/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/MechanicalSubshiftSlopeRigidity
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   digest: Mechanical-subshift membership preserves true-letter density, so equal subshifts have equal slopes. -/

import D5.S1.Words.Complexity.SubshiftHausdorffDimension
import D5.S1.Words.Mechanical.MechanicalDensity

namespace D5.S1.Words.Complexity.MechanicalSubshiftSlopeRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S1.Words.Complexity
open D5.S1.Words.Complexity.SubshiftHausdorffDimension
open D5.S1.Words.Mechanical
open Filter

noncomputable section

/-- The number of true letters in the length-`n` prefix of an infinite Boolean word. -/
def wordPrefixTrueCount (y : ℕ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun i => y i = true).card

/-- Every member of a lower-mechanical-word subshift inherits discrepancy below one. -/
theorem mechanical_wordSubshift_member_true_discrepancy {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {y : ℕ → Bool}
    (hy : y ∈ wordSubshift (lowerMechanicalWord α ρ)) (n : ℕ) :
    |(wordPrefixTrueCount y n : ℝ) - (n : ℝ) * α| < 1 := by
  obtain ⟨i, hi⟩ := mem_wordFactorSet.mp (hy n)
  have hcount : wordPrefixTrueCount y n = lowerMechanicalWindowTrueCount α ρ i n := by
    unfold wordPrefixTrueCount lowerMechanicalWindowTrueCount
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hletter := congrFun hi ⟨k, hklt⟩
    simpa only [wordFactor] using hletter ▸ Iff.rfl
  rw [hcount]
  exact lower_mechanical_window_true_discrepancy hα0 hα1 i n

/-- Every member of a lower-mechanical-word subshift has true-letter density equal to its slope. -/
theorem mechanical_wordSubshift_member_true_density {α ρ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) {y : ℕ → Bool}
    (hy : y ∈ wordSubshift (lowerMechanicalWord α ρ)) :
    Tendsto (fun n : ℕ => (wordPrefixTrueCount y n : ℝ) / n) atTop (nhds α) := by
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlower : Tendsto (fun n : ℕ => α - (1 : ℝ) / n) atTop (nhds α) := by
    simpa using tendsto_const_nhds.sub hzero
  have hupper : Tendsto (fun n : ℕ => α + (1 : ℝ) / n) atTop (nhds α) := by
    simpa using tendsto_const_nhds.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdisc := mechanical_wordSubshift_member_true_discrepancy hα0 hα1 hy n
    rw [abs_lt] at hdisc
    have hl : (n : ℝ) * α - 1 ≤ (wordPrefixTrueCount y n : ℝ) := by
      linarith
    calc
      α - (1 : ℝ) / n = ((n : ℝ) * α - 1) / n := by field_simp
      _ ≤ (wordPrefixTrueCount y n : ℝ) / n := (div_le_div_iff_of_pos_right hn_pos).2 hl
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hdisc := mechanical_wordSubshift_member_true_discrepancy hα0 hα1 hy n
    rw [abs_lt] at hdisc
    have hu : (wordPrefixTrueCount y n : ℝ) ≤ (n : ℝ) * α + 1 := by
      linarith
    calc
      (wordPrefixTrueCount y n : ℝ) / n ≤ ((n : ℝ) * α + 1) / n :=
        (div_le_div_iff_of_pos_right hn_pos).2 hu
      _ = α + (1 : ℝ) / n := by field_simp

/-- Equality of lower-mechanical-word subshifts forces equality of their slopes. -/
theorem mechanical_wordSubshift_slope_eq_of_eq {α β ρ σ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hsubshift : wordSubshift (lowerMechanicalWord α ρ) =
      wordSubshift (lowerMechanicalWord β σ)) :
    α = β := by
  have hself : lowerMechanicalWord α ρ ∈ wordSubshift (lowerMechanicalWord α ρ) :=
    self_mem_wordSubshift _
  have hother : lowerMechanicalWord α ρ ∈ wordSubshift (lowerMechanicalWord β σ) := by
    rw [← hsubshift]
    exact hself
  exact tendsto_nhds_unique
    (mechanical_wordSubshift_member_true_density hα0 hα1 hself)
    (mechanical_wordSubshift_member_true_density hβ0 hβ1 hother)

#print axioms mechanical_wordSubshift_member_true_discrepancy
#print axioms mechanical_wordSubshift_member_true_density
#print axioms mechanical_wordSubshift_slope_eq_of_eq

end

end D5.S1.Words.Complexity.MechanicalSubshiftSlopeRigidity
