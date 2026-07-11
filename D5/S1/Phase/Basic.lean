/- GID: D5/S1/Phase/Basic
   generality: I
   mirror-B: D5/B/S1/Phase/Basic
   mirror-E: none(waiver:algebraically-proved)
   anchors: [GICT-v3.6-I.1-definition-1.4]
   digest: Integer golden-ratio phases form an injective additive orbit on the unit circle. -/

import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Instances.AddCircle.Defs

namespace D5.S1.Phase

/-- The phase of an integer under rotation by the golden ratio modulo one. -/
noncomputable def goldenPhase (n : ℤ) : AddCircle (1 : ℝ) :=
  ((n : ℝ) * Real.goldenRatio : ℝ)

@[simp] theorem goldenPhase_zero : goldenPhase 0 = 0 := by simp [goldenPhase]

@[simp] theorem goldenPhase_add (n m : ℤ) :
    goldenPhase (n + m) = goldenPhase n + goldenPhase m := by
  simp [goldenPhase, add_mul]

@[simp] theorem goldenPhase_neg (n : ℤ) : goldenPhase (-n) = -goldenPhase n := by
  simp [goldenPhase]

theorem goldenPhase_injective : Function.Injective goldenPhase := by
  intro n m hnm
  have hzero : goldenPhase (n - m) = 0 := by
    change goldenPhase (n + -m) = 0
    rw [goldenPhase_add, goldenPhase_neg, hnm, add_neg_cancel]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  by_contra hne
  have hsub : n - m ≠ 0 := sub_ne_zero.mpr hne
  have hratio : Real.goldenRatio =
      ((k : ℤ) : ℝ) / (((n - m : ℤ) : ℝ)) := by
    apply (eq_div_iff (Int.cast_ne_zero.mpr hsub)).2
    simpa [goldenPhase, mul_comm] using hk.symm
  exact Real.goldenRatio_irrational.ne_rational k (n - m) hratio

end D5.S1.Phase
