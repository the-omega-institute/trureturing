/- GID: D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation
   generality: G
   mirror-B: D5/B/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reflection pairing cancels odd linear jets while preserving quadratic information in the even channel. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.CompletionDynamics.ObserverJet.PairedOddJetCancellation

/-- Reflection-even channel of a scalar observer profile. -/
def evenChannel (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  (f h + f (-h)) / 2

/-- Reflection-odd channel of a scalar observer profile. -/
def oddChannel (f : ℝ → ℝ) (h : ℝ) : ℝ :=
  (f h - f (-h)) / 2

/-- Every profile decomposes exactly into its paired even and odd channels. -/
theorem even_add_odd_eq (f : ℝ → ℝ) (h : ℝ) :
    evenChannel f h + oddChannel f h = f h := by
  unfold evenChannel oddChannel
  ring

/-- The paired even channel is invariant under reflection. -/
theorem even_channel_neg (f : ℝ → ℝ) (h : ℝ) :
    evenChannel f (-h) = evenChannel f h := by
  unfold evenChannel
  ring

/-- The paired odd channel changes sign under reflection. -/
theorem odd_channel_neg (f : ℝ → ℝ) (h : ℝ) :
    oddChannel f (-h) = -oddChannel f h := by
  unfold oddChannel
  ring

/-- A first-order signed jet vanishes after pairing in the even channel. -/
theorem linear_jet_even_channel_zero (v h : ℝ) :
    evenChannel (fun u : ℝ => v * u) h = 0 := by
  unfold evenChannel
  ring

/-- The same first-order jet is retained exactly in the odd channel. -/
theorem linear_jet_odd_channel (v h : ℝ) :
    oddChannel (fun u : ℝ => v * u) h = v * h := by
  unfold oddChannel
  ring

/-- Squaring a reflected tangent removes its sign. -/
theorem reflected_tangent_square (v : ℝ) :
    (-v) ^ 2 = v ^ 2 := by
  ring

/-- A quadratic jet survives reflection pairing in the even channel. -/
theorem quadratic_jet_even_channel (v h : ℝ) :
    evenChannel (fun u : ℝ => (v * u) ^ 2) h = (v * h) ^ 2 := by
  unfold evenChannel
  ring

/-- A quadratic jet has zero odd component. -/
theorem quadratic_jet_odd_channel_zero (v h : ℝ) :
    oddChannel (fun u : ℝ => (v * u) ^ 2) h = 0 := by
  unfold oddChannel
  ring

/-- Direct vector-pair version of first-order cancellation. -/
theorem paired_tangent_average_zero (v : ℝ) :
    (v + (-v)) / 2 = 0 := by
  ring

/-- The second moment of a reflected tangent pair is the original square. -/
theorem paired_tangent_second_moment (v : ℝ) :
    (v ^ 2 + (-v) ^ 2) / 2 = v ^ 2 := by
  ring

/-- Vanishing of the even linear channel does not force the tangent to vanish. -/
example :
    evenChannel (fun u : ℝ => u) 1 = 0 ∧ (1 : ℝ) ≠ 0 := by
  norm_num [evenChannel]

#print axioms even_add_odd_eq
#print axioms even_channel_neg
#print axioms odd_channel_neg
#print axioms linear_jet_even_channel_zero
#print axioms linear_jet_odd_channel
#print axioms reflected_tangent_square
#print axioms quadratic_jet_even_channel
#print axioms quadratic_jet_odd_channel_zero
#print axioms paired_tangent_average_zero
#print axioms paired_tangent_second_moment

end D5.S3.CompletionDynamics.ObserverJet.PairedOddJetCancellation
