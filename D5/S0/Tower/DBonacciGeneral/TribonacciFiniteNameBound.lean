/- GID: D5/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound
   generality: I
   mirror-B: D5/B/S0/Tower/DBonacciGeneral/TribonacciFiniteNameBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Terminating Tribonacci names have zero survivor liminf and satisfy the champion bound. -/

import D5.S0.Tower.DBonacciGeneral.TribonacciGlobalBound

namespace D5.S0.Tower.DBonacciGeneral.TribonacciFiniteNameBound

open D5.S0.Tower.DBonacciGeneral.ChampionValue
open D5.S0.Tower.Tribonacci.Substitution
open D5.S0.Tower.Tribonacci.Survivor
open D5.S0.Tower.Tribonacci.Values

local notation "t" => tribonacciConstant

/-- The arithmetic carrier of reals represented by a terminating admissible
Tribonacci name. -/
def tribonacciFiniteNameCarrier : Set Real :=
  {x | ∃ Q, x ∈ tribonacciNameGrid Q}

/-- Every finite grid is part of the terminating-name carrier. -/
theorem tribonacci_name_grid_subset_finite_name_carrier (Q : Nat) :
    tribonacciNameGrid Q ⊆ tribonacciFiniteNameCarrier := by
  intro x hx
  exact ⟨Q, hx⟩

/-- Appending a zero digit embeds each finite grid into its successor. -/
theorem tribonacci_name_grid_subset_succ (Q : Nat) :
    tribonacciNameGrid Q ⊆ tribonacciNameGrid (Q + 1) := by
  rintro x ⟨i, rfl⟩
  exact ⟨levelEmbedding Q i, levelEmbedding_value Q i⟩

/-- A terminating name remains present after any number of zero extensions. -/
theorem mem_tribonacci_name_grid_add (Q n : Nat) (x : Real)
    (hx : x ∈ tribonacciNameGrid Q) :
    x ∈ tribonacciNameGrid (Q + n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      simpa [Nat.add_assoc] using
        (tribonacci_name_grid_subset_succ (Q + n)) ih

/-- Survivor distance vanishes exactly at a finite grid point. -/
theorem tribonacci_survivor_eq_zero_of_mem (Q : Nat) (x : Real)
    (hx : x ∈ tribonacciNameGrid Q) :
    tribonacciSurvivor Q x = 0 := by
  unfold tribonacciSurvivor
  rw [Metric.infDist_zero_of_mem hx, mul_zero]

/-- Every terminating name has exact survivor liminf zero. -/
theorem tribonacci_finite_name_liminf (x : Real)
    (hx : x ∈ tribonacciFiniteNameCarrier) :
    Filter.liminf (fun Q => tribonacciSurvivor Q x) Filter.atTop = 0 := by
  obtain ⟨Q, hQ⟩ := hx
  have hzero (n : Nat) : tribonacciSurvivor (Q + n) x = 0 :=
    tribonacci_survivor_eq_zero_of_mem (Q + n) x
      (mem_tribonacci_name_grid_add Q n x hQ)
  have heventuallyZero :
      (fun q => tribonacciSurvivor q x) =ᶠ[Filter.atTop] (fun _ => 0) := by
    filter_upwards [Filter.eventually_ge_atTop Q] with q hq
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hq
    exact hzero n
  exact (tendsto_const_nhds.congr' heventuallyZero.symm).liminf_eq

/-- Hence the corrected Tribonacci champion value bounds the liminf on the
terminating-name carrier. -/
theorem tribonacci_finite_name_liminf_upper_bound (x : Real)
    (hx : x ∈ tribonacciFiniteNameCarrier) :
    Filter.liminf (fun Q => tribonacciSurvivor Q x) Filter.atTop ≤
      championValue t := by
  rw [tribonacci_finite_name_liminf x hx, championValue_tribonacciConstant]
  simpa [zpow_neg] using
    D5.S0.Tower.Tribonacci.ChampionOrbit.tribonacci_champion_low_pos.le

end D5.S0.Tower.DBonacciGeneral.TribonacciFiniteNameBound
