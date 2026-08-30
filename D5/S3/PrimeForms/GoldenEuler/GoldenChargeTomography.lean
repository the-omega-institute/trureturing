/- GID: D5/S3/PrimeForms/GoldenEuler/GoldenChargeTomography
   generality: G
   mirror-B: D5/B/S3/PrimeForms/GoldenEuler/GoldenChargeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Neutral and quadratic charge channels invert exactly to split and inert channels by the C2 Fourier transform. -/

import Mathlib

/-!
This is the finite `C2` tomography underlying the pair of channels
`1` and `chi_5`. It is an algebraic reconstruction theorem. Analytic
statements about Dirichlet L-functions and their zeros are separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.GoldenEuler.GoldenChargeTomography

/-- Neutral channel of a split/inert pair. -/
def neutralChannel (split inert : ℝ) : ℝ := split + inert

/-- Quadratic charge channel of a split/inert pair. -/
def chargeChannel (split inert : ℝ) : ℝ := split - inert

/-- Recover the split component from neutral and charge channels. -/
def splitFromChannels (neutral charge : ℝ) : ℝ :=
  (neutral + charge) / 2

/-- Recover the inert component from neutral and charge channels. -/
def inertFromChannels (neutral charge : ℝ) : ℝ :=
  (neutral - charge) / 2

/-- Exact inverse Fourier reconstruction of the split channel. -/
theorem split_channel_reconstruction (split inert : ℝ) :
    splitFromChannels (neutralChannel split inert)
      (chargeChannel split inert) = split := by
  unfold splitFromChannels neutralChannel chargeChannel
  ring

/-- Exact inverse Fourier reconstruction of the inert channel. -/
theorem inert_channel_reconstruction (split inert : ℝ) :
    inertFromChannels (neutralChannel split inert)
      (chargeChannel split inert) = inert := by
  unfold inertFromChannels neutralChannel chargeChannel
  ring

/-- Split indicator extracted from a quadratic charge value. -/
def splitIndicator (charge : ℝ) : ℝ := (1 + charge) / 2

/-- Inert indicator extracted from a quadratic charge value. -/
def inertIndicator (charge : ℝ) : ℝ := (1 - charge) / 2

/-- The two indicators form a partition of the unramified unit mass. -/
theorem split_add_inert_indicator (charge : ℝ) :
    splitIndicator charge + inertIndicator charge = 1 := by
  unfold splitIndicator inertIndicator
  ring

/-- Their signed difference recovers the charge. -/
theorem split_sub_inert_indicator (charge : ℝ) :
    splitIndicator charge - inertIndicator charge = charge := by
  unfold splitIndicator inertIndicator
  ring

@[simp] theorem split_indicator_pos_charge : splitIndicator 1 = 1 := by
  norm_num [splitIndicator]

@[simp] theorem inert_indicator_pos_charge : inertIndicator 1 = 0 := by
  norm_num [inertIndicator]

@[simp] theorem split_indicator_neg_charge : splitIndicator (-1) = 0 := by
  norm_num [splitIndicator]

@[simp] theorem inert_indicator_neg_charge : inertIndicator (-1) = 1 := by
  norm_num [inertIndicator]

#print axioms split_channel_reconstruction
#print axioms inert_channel_reconstruction
#print axioms split_add_inert_indicator
#print axioms split_sub_inert_indicator

end D5.S3.PrimeForms.GoldenEuler.GoldenChargeTomography
