/- GID: D5/S0/Tower/MetricGeometry/RadixGridDistance
   generality: G
   mirror-B: D5/B/S0/Tower/MetricGeometry/RadixGridDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Radix rounding distance equals metric distance to the radix grid. -/

import D5.S0.Tower.ConstantArms
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/- Library-search audit trail (2026-08-15):
   * Repository searches found `radixGrid`, `radixDistance`, and `binary_arm`
     in `ConstantArms`, but no public theorem connecting the rounding formula
     to `Metric.infDist` on the grid.
   * Pinned mathlib provides and the proofs below apply `Metric.le_infDist`,
     `Metric.infDist_le_dist_of_mem`, `round_le`, `Int.cast_abs`, and
     `Nat.Prime.dvd_of_dvd_pow`; no complete radix-grid bridge was found.
   * Loogle returned the generic infimum-distance API but no theorem for this
     grid. LeanSearch returned `round_le`, AddCircle norm formulas, and ZMod
     minimum-representative lemmas, but no full-statement match. -/

namespace D5.S0.Tower.MetricGeometry.RadixGridDistance

open D5.S0.Tower.ConstantArms

/-- Rounding after radix scaling realizes the metric distance to the radix grid. -/
theorem radixDistance_eq_infDist (b Q : Nat) (hb : b ≠ 0) (x : Real) :
    radixDistance b Q x = Metric.infDist x (radixGrid b Q) := by
  have hscale : (0 : Real) < (b : Real) ^ Q :=
    pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hb)) Q
  have hgrid : (radixGrid b Q).Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨0, by simp⟩
  have hnormalize (m : Int) :
      |(b : Real) ^ Q * x - (m : Real)| / (b : Real) ^ Q =
        |x - (m : Real) / (b : Real) ^ Q| := by
    calc
      |(b : Real) ^ Q * x - (m : Real)| / (b : Real) ^ Q =
          |(b : Real) ^ Q * x - (m : Real)| / |(b : Real) ^ Q| := by
            rw [abs_of_pos hscale]
      _ = |((b : Real) ^ Q * x - (m : Real)) / (b : Real) ^ Q| := by
            rw [abs_div]
      _ = |x - (m : Real) / (b : Real) ^ Q| := by
            congr 1
            field_simp
  apply le_antisymm
  · rw [Metric.le_infDist hgrid]
    intro y hy
    rcases hy with ⟨m, rfl⟩
    rw [radixDistance, Real.dist_eq]
    exact (div_le_div_of_nonneg_right (round_le ((b : Real) ^ Q * x) m) hscale.le).trans_eq
      (hnormalize m)
  · let m : Int := round ((b : Real) ^ Q * x)
    calc
      Metric.infDist x (radixGrid b Q) ≤
          dist x ((m : Real) / (b : Real) ^ Q) := by
        apply Metric.infDist_le_dist_of_mem
        exact ⟨m, rfl⟩
      _ = |x - (m : Real) / (b : Real) ^ Q| := Real.dist_eq _ _
      _ = |(b : Real) ^ Q * x - (m : Real)| / (b : Real) ^ Q := (hnormalize m).symm
      _ = radixDistance b Q x := by rfl

/-- The distance from one third to an arbitrary binary-grid point has the
integer numerator appearing in Proposition 4.2. -/
theorem binary_point_distance_formula (Q : Nat) (m : Int) :
    |(1 : Real) / 3 - (m : Real) / (2 : Real) ^ Q| =
      ((|((2 ^ Q : Nat) : Int) - 3 * m| : Int) : Real) /
        (3 * (2 : Real) ^ Q) := by
  have hden : (0 : Real) < 3 * (2 : Real) ^ Q :=
    mul_pos (by norm_num) (pow_pos (by norm_num) Q)
  rw [Int.cast_abs, ← abs_of_pos hden, ← abs_div]
  congr 1
  field_simp
  push_cast
  ring

/-- No power of two is zero modulo three. -/
theorem binary_pow_mod_three_ne_zero (Q : Nat) : 2 ^ Q % 3 ≠ 0 := by
  intro hzero
  have hdvd : 3 ∣ 2 ^ Q := Nat.dvd_of_mod_eq_zero hzero
  have : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hdvd
  norm_num at this

/-- The binary numerator residual attains absolute value one, and no integer
choice has a smaller absolute residual. -/
theorem binary_integer_residual_minimum (Q : Nat) :
    (∃ m : Int, |((2 ^ Q : Nat) : Int) - 3 * m| = 1) ∧
      ∀ m : Int, 1 ≤ |((2 ^ Q : Nat) : Int) - 3 * m| := by
  have hattain : ∃ m : Int,
      ((2 ^ Q : Nat) : Int) - 3 * m = 1 ∨
        ((2 ^ Q : Nat) : Int) - 3 * m = -1 := by
    induction Q with
    | zero => exact ⟨0, by norm_num⟩
    | succ Q ih =>
        rcases ih with ⟨m, hm | hm⟩
        · refine ⟨2 * m + 1, Or.inr ?_⟩
          push_cast
          rw [pow_succ]
          push_cast at hm
          omega
        · refine ⟨2 * m - 1, Or.inl ?_⟩
          push_cast
          rw [pow_succ]
          push_cast at hm
          omega
  constructor
  · rcases hattain with ⟨m, hm | hm⟩
    · exact ⟨m, by rw [hm]; norm_num⟩
    · exact ⟨m, by rw [hm]; norm_num⟩
  · intro m
    have hne : ((2 ^ Q : Nat) : Int) - 3 * m ≠ 0 := by
      intro hzero
      have hdvdInt : (3 : Int) ∣ ((2 ^ Q : Nat) : Int) := by
        use m
        omega
      have hdvdNat : 3 ∣ 2 ^ Q := by exact_mod_cast hdvdInt
      exact binary_pow_mod_three_ne_zero Q (Nat.mod_eq_zero_of_dvd hdvdNat)
    have hpos : (0 : Int) < |((2 ^ Q : Nat) : Int) - 3 * m| := abs_pos.mpr hne
    omega

/-- At every positive level, the binary one-third arm is the actual metric
distance to the binary radix grid, in both normalized and unscaled forms. -/
theorem binary_grid_distance (Q : Nat) (hQ : 1 ≤ Q) :
    (2 : Real) ^ Q * Metric.infDist (1 / 3) (radixGrid 2 Q) = 1 / 3 ∧
      Metric.infDist (1 / 3) (radixGrid 2 Q) =
        1 / (3 * (2 : Real) ^ Q) := by
  have hscaled :
      (2 : Real) ^ Q * Metric.infDist (1 / 3) (radixGrid 2 Q) = 1 / 3 := by
    rw [← radixDistance_eq_infDist 2 Q (by norm_num) (1 / 3)]
    exact ConstantArms.binary_arm Q hQ
  refine ⟨hscaled, ?_⟩
  have hpow : (2 : Real) ^ Q ≠ 0 := pow_ne_zero Q (by norm_num)
  rw [← div_div]
  apply (eq_div_iff hpow).2
  simpa [mul_comm] using hscaled

/-- All arithmetic and metric clauses used by the binary constant-arm
proposition, packaged under one coverage declaration. -/
theorem binary_constant_arm_clauses (Q : Nat) (hQ : 1 ≤ Q) :
    Nat.Coprime 3 2 ∧
      (∀ m : Int,
        |(1 : Real) / 3 - (m : Real) / (2 : Real) ^ Q| =
          ((|((2 ^ Q : Nat) : Int) - 3 * m| : Int) : Real) /
            (3 * (2 : Real) ^ Q)) ∧
      2 ^ Q % 3 ≠ 0 ∧
      ((∃ m : Int, |((2 ^ Q : Nat) : Int) - 3 * m| = 1) ∧
        ∀ m : Int, 1 ≤ |((2 ^ Q : Nat) : Int) - 3 * m|) ∧
      ((2 : Real) ^ Q * Metric.infDist (1 / 3) (radixGrid 2 Q) = 1 / 3 ∧
        Metric.infDist (1 / 3) (radixGrid 2 Q) =
          1 / (3 * (2 : Real) ^ Q)) := by
  refine ⟨Nat.coprime_two_right.mpr (by decide), ?_⟩
  exact ⟨binary_point_distance_formula Q, binary_pow_mod_three_ne_zero Q,
    binary_integer_residual_minimum Q, binary_grid_distance Q hQ⟩

end D5.S0.Tower.MetricGeometry.RadixGridDistance
