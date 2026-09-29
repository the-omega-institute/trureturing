/- GID: D5/S3/Estimation/TimeArrow/SinglePeakPathCurrent
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/SinglePeakPathCurrent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single-peak parity path log-likelihood ratios are one net current plus endpoints. -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent

open Finset

/-- The three regions of a single-peak parity kernel: the peak state, the other states of the
peak's parity class, and the opposite parity class. -/
inductive Region
  | peak
  | bulk
  | opposite
  deriving DecidableEq

section Kernel

variable {X : Type*}

open Classical in
/-- The region of a state, read from its parity sign and the peak position. -/
noncomputable def region (χ : X → ℝ) (z : X) (x : X) : Region :=
  if x = z then Region.peak else if χ x = 1 then Region.bulk else Region.opposite

/-- The single-peak profile: value `r` at the peak, `-q` on the rest of the peak's parity class,
and zero on the opposite class. -/
noncomputable def profile (χ : X → ℝ) (z : X) (r q : ℝ) (x : X) : ℝ :=
  match region χ z x with
  | Region.peak => r
  | Region.bulk => -q
  | Region.opposite => 0

/-- The parity kernel `P(x,y) = (1 + χ(x) χ(y) b(x)) / N` with the single-peak profile `b`. -/
noncomputable def kernel (χ : X → ℝ) (z : X) (r q N : ℝ) (x y : X) : ℝ :=
  (1 + χ x * χ y * profile χ z r q x) / N

/-- The forward law of the path `x 0, …, x T` started from the uniform mass `1 / N`. -/
noncomputable def forwardLaw (P : X → X → ℝ) (N : ℝ) (x : ℕ → X) (T : ℕ) : ℝ :=
  (1 / N) * ∏ t ∈ range T, P (x t) (x (t + 1))

/-- The law of the time-reversed chain evaluated on the same path. -/
noncomputable def reverseLaw (P : X → X → ℝ) (N : ℝ) (x : ℕ → X) (T : ℕ) : ℝ :=
  (1 / N) * ∏ t ∈ range T, P (x (t + 1)) (x t)

end Kernel

section Counts

variable {X : Type*}

/-- The number of transitions of the path from region `U` to region `V` in the first `T`
steps. -/
def transitions (ρ : X → Region) (x : ℕ → X) (T : ℕ) (U V : Region) : ℕ :=
  ((range T).filter fun t => ρ (x t) = U ∧ ρ (x (t + 1)) = V).card

/-- The endpoint difference `1[Y_0 = U] - 1[Y_T = U]`. -/
def endpointDefect (ρ : X → Region) (x : ℕ → X) (T : ℕ) (U : Region) : ℝ :=
  (if ρ (x 0) = U then 1 else 0) - (if ρ (x T) = U then 1 else 0)

end Counts

/-- The log ratio assigned to a directed region transition. -/
def regionWeight (a b c : ℝ) : Region → Region → ℝ
  | Region.peak, Region.bulk => a
  | Region.bulk, Region.peak => -a
  | Region.bulk, Region.opposite => b
  | Region.opposite, Region.bulk => -b
  | Region.opposite, Region.peak => c
  | Region.peak, Region.opposite => -c
  | _, _ => 0

/-- Potential for the three-region cycle. -/
private def potential (A B : ℝ) : Region → ℝ
  | Region.peak => 0
  | Region.bulk => A
  | Region.opposite => A + B

private theorem regionWeight_eq_potential (A B C : ℝ) (u v : Region) :
    regionWeight A B C u v =
      potential A B v - potential A B u +
        (A + B + C) * ((if u = Region.opposite ∧ v = Region.peak then 1 else 0) -
          (if u = Region.peak ∧ v = Region.opposite then 1 else 0)) := by
  cases u <;> cases v <;> simp [regionWeight, potential] <;> ring

private theorem indicator_sum (U : Region) :
    (if U = Region.peak then (1 : ℝ) else 0) + (if U = Region.bulk then 1 else 0) +
      (if U = Region.opposite then 1 else 0) = 1 := by
  cases U <;> simp

/-- Along any finite path, the summed region weights are the cycle affinity times the net
opposite-to-peak current plus two endpoint terms. -/
private theorem sum_regionWeight_eq_current {X : Type*} (ρ : X → Region) (A B C : ℝ) (x : ℕ → X)
    (T : ℕ) :
    ∑ t ∈ range T, regionWeight A B C (ρ (x t)) (ρ (x (t + 1))) =
      (A + B + C) *
          ((transitions ρ x T Region.opposite Region.peak : ℝ) -
            transitions ρ x T Region.peak Region.opposite) +
        A * endpointDefect ρ x T Region.peak - B * endpointDefect ρ x T Region.opposite := by
  have hsum : ∀ T : ℕ,
      ∑ t ∈ range T, regionWeight A B C (ρ (x t)) (ρ (x (t + 1))) =
        potential A B (ρ (x T)) - potential A B (ρ (x 0)) +
          (A + B + C) *
            ((transitions ρ x T Region.opposite Region.peak : ℝ) -
              transitions ρ x T Region.peak Region.opposite) := by
    intro T
    induction T with
    | zero => simp [transitions]
    | succ T ih =>
        have hcount : ∀ U V : Region,
            (transitions ρ x (T + 1) U V : ℝ) = transitions ρ x T U V +
              (if ρ (x T) = U ∧ ρ (x (T + 1)) = V then 1 else 0) := by
          intro U V
          unfold transitions
          rw [range_add_one, filter_insert]
          split_ifs with h
          · rw [card_insert_of_notMem (by simp)]
            push_cast
            ring
          · simp
        rw [sum_range_succ, ih, regionWeight_eq_potential, hcount, hcount]
        ring
  rw [hsum]
  have hpot : ∀ U : Region, potential A B U =
      A * ((if U = Region.bulk then 1 else 0) + (if U = Region.opposite then 1 else 0)) +
        B * (if U = Region.opposite then 1 else 0) := by
    intro U
    cases U <;> simp [potential]
  have h0 := indicator_sum (ρ (x 0))
  have hT := indicator_sum (ρ (x T))
  simp only [endpointDefect, hpot]
  linear_combination A * hT - A * h0

/-- **Single-current form of the path likelihood ratio.** For the single-peak parity kernel with
peak value `r`, bulk value `-q` and zero on the opposite class, the log ratio of the forward and
time-reversed laws of every finite path equals `(A + B₀ + C) J + A Δ_H - B₀ Δ_Z`, where `J` is
the net number of opposite-to-peak transitions, `A = log ((1 + r) / (1 - q))`,
`B₀ = log (1 + q)` and `C = -log (1 - r)`. -/
theorem log_forward_div_reverse_eq_current {X : Type*}
    (χ : X → ℝ) (hχ : ∀ x, χ x = 1 ∨ χ x = -1) (z : X) (hz : χ z = 1)
    (r q N : ℝ) (hr : |r| < 1) (hq : |q| < 1) (hN : 0 < N) (T : ℕ) (x : ℕ → X) :
    Real.log (forwardLaw (kernel χ z r q N) N x T / reverseLaw (kernel χ z r q N) N x T) =
      (Real.log ((1 + r) / (1 - q)) + Real.log (1 + q) - Real.log (1 - r)) *
          ((transitions (region χ z) x T Region.opposite Region.peak : ℝ) -
            transitions (region χ z) x T Region.peak Region.opposite) +
        Real.log ((1 + r) / (1 - q)) * endpointDefect (region χ z) x T Region.peak -
          Real.log (1 + q) * endpointDefect (region χ z) x T Region.opposite := by
  obtain ⟨hr1, hr2⟩ := abs_lt.mp hr
  obtain ⟨hq1, hq2⟩ := abs_lt.mp hq
  -- the region fixes the sign and the profile value
  have hsign : ∀ y, region χ z y ≠ Region.opposite → χ y = 1 := by
    intro y hy
    by_cases h1 : y = z
    · rw [h1]; exact hz
    · by_contra h2
      exact hy (by simp [region, h1, h2])
  have hsign' : ∀ y, region χ z y = Region.opposite → χ y = -1 := by
    intro y hy
    refine (hχ y).resolve_left fun h2 => ?_
    by_cases h1 : y = z <;> simp [region, h1, h2] at hy
  have hprof : ∀ y, profile χ z r q y =
      match region χ z y with
      | Region.peak => r
      | Region.bulk => -q
      | Region.opposite => 0 := fun y => rfl
  -- every transition probability is positive, and its log ratio is a region weight
  have hpos : ∀ u v : X, 0 < kernel χ z r q N u v := by
    intro u v
    unfold kernel
    apply div_pos _ hN
    rw [hprof u]
    rcases hχ u with hu | hu <;> rcases hχ v with hv | hv <;>
      rcases region χ z u with _ | _ | _ <;> simp only [hu, hv] <;> nlinarith
  have hkey : ∀ u v : X,
      Real.log (kernel χ z r q N u v / kernel χ z r q N v u) =
        regionWeight (Real.log ((1 + r) / (1 - q))) (Real.log (1 + q)) (-Real.log (1 - r))
          (region χ z u) (region χ z v) := by
    intro u v
    unfold kernel
    rw [div_div_div_cancel_right₀ hN.ne', hprof u, hprof v, mul_comm (χ v) (χ u)]
    have h1r : (0 : ℝ) < 1 - r := by linarith
    have h1q : (0 : ℝ) < 1 + q := by linarith
    have h1q' : (0 : ℝ) < 1 - q := by linarith
    have h1r' : (0 : ℝ) < 1 + r := by linarith
    rcases hu : region χ z u with _ | _ | _ <;> rcases hv : region χ z v with _ | _ | _
    · simp [regionWeight]
    · rw [hsign u (by rw [hu]; decide), hsign v (by rw [hv]; decide)]
      simp [regionWeight, sub_eq_add_neg]
    · rw [hsign u (by rw [hu]; decide), hsign' v hv]
      simp [regionWeight, sub_eq_add_neg]
    · rw [hsign u (by rw [hu]; decide), hsign v (by rw [hv]; decide)]
      simp only [regionWeight, one_mul, mul_neg, mul_one]
      rw [← Real.log_inv, inv_div, sub_eq_add_neg]
    · simp [regionWeight]
    · rw [hsign u (by rw [hu]; decide), hsign' v hv]
      simp [regionWeight]
    · rw [hsign' u hu, hsign v (by rw [hv]; decide)]
      simp [regionWeight, sub_eq_add_neg, Real.log_inv]
    · rw [hsign' u hu, hsign v (by rw [hv]; decide)]
      simp [regionWeight, Real.log_inv]
    · simp [regionWeight]
  have hratio : forwardLaw (kernel χ z r q N) N x T / reverseLaw (kernel χ z r q N) N x T =
      ∏ t ∈ range T,
        (kernel χ z r q N (x t) (x (t + 1)) / kernel χ z r q N (x (t + 1)) (x t)) := by
    unfold forwardLaw reverseLaw
    rw [mul_div_mul_left _ _ (by positivity), prod_div_distrib]
  rw [hratio, Real.log_prod (fun t _ => (div_pos (hpos _ _) (hpos _ _)).ne')]
  simp_rw [hkey]
  rw [sum_regionWeight_eq_current]
  ring

/-- On the `d`-dimensional sign hypercube, the product of the coordinates takes only the values
`1` and `-1`, and the all-ones vertex has sign `1`; these are the hypotheses on `χ` and `z`. -/
example (d : ℕ) :
    (∀ y : Fin d → ℤˣ,
        (((∏ j, y j : ℤˣ) : ℤ) : ℝ) = 1 ∨ (((∏ j, y j : ℤˣ) : ℤ) : ℝ) = -1) ∧
      (((∏ _j : Fin d, (1 : ℤˣ) : ℤˣ) : ℤ) : ℝ) = 1 := by
  refine ⟨fun y => ?_, by simp⟩
  rcases Int.units_eq_one_or (∏ j, y j) with h | h <;> simp [h]

#print axioms log_forward_div_reverse_eq_current

end D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
