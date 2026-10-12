/- GID: D5/S3/Estimation/TimeArrow/RectangleHypergeometricMaxAtom
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/RectangleHypergeometricMaxAtom
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Balanced hypergeometric margins give a uniform inverse-square-root atom bound. -/

import D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge
import Mathlib.Data.Finset.Max

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
noncomputable section

open private
  D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge.hypergeometric_balanced_central_atom
from D5.S3.Estimation.TimeArrow.NativeCalibratedArithmeticBridge

set_option quotPrecheck false in
local notation "W" => fun N R U t : ℕ => R.choose t * (N-R).choose (U-t)

set_option quotPrecheck false in
local notation "H" => fun N R U t : ℕ => if t ≤ U then
  ((R.choose t : ℝ) * ((N-R).choose (U-t) : ℝ)) / (N.choose U : ℝ) else 0

/-- Cross multiplication remains valid at the lower support boundary. -/
private theorem adjacent_cross {N R U t : ℕ} (hR : R ≤ N) (htR : t ≤ R)
    (htU : t < U) (hcell : U-t ≤ N-R+1) :
    (W N R U (t+1) : ℝ) * (t+1) * ((N : ℝ)-R+t+1-U) =
      (W N R U t : ℝ) * ((R : ℝ)-t) * ((U : ℝ)-t) := by
  have ha := Nat.choose_succ_right_eq R t
  have hb := Nat.choose_succ_right_eq (N-R) (U-t-1)
  have hk : U-t-1+1 = U-t := by omega
  have hs : U-(t+1) = U-t-1 := by omega
  rw [hk] at hb
  have hc : U-t-1 ≤ N-R := by omega
  have haR : (R.choose (t+1) : ℝ) * (t+1) =
      (R.choose t : ℝ) * ((R : ℝ)-t) := by
    exact_mod_cast (by simpa only [Nat.cast_sub htR] using
      (show (R.choose (t+1) : ℝ) * ((t+1 : ℕ) : ℝ) =
        (R.choose t : ℝ) * ((R-t : ℕ) : ℝ) by exact_mod_cast ha))
  have hbR : ((N-R).choose (U-(t+1)) : ℝ) * ((N : ℝ)-R+t+1-U) =
      ((N-R).choose (U-t) : ℝ) * ((U : ℝ)-t) := by
    have hb' : ((N-R).choose (U-t) : ℝ) * ((U-t : ℕ) : ℝ) =
        ((N-R).choose (U-t-1) : ℝ) * ((N-R-(U-t-1) : ℕ) : ℝ) := by
      exact_mod_cast hb
    rw [Nat.cast_sub htU.le, Nat.cast_sub hc, Nat.cast_sub hR,
      Nat.cast_sub (by omega : 1 ≤ U-t), Nat.cast_sub htU.le] at hb'
    rw [hs]
    push_cast at hb'
    nlinarith [hb']
  push_cast
  calc
    _ = ((R.choose (t+1) : ℝ) * (t+1)) *
        (((N-R).choose (U-(t+1)) : ℝ) * ((N : ℝ)-R+t+1-U)) := by ring
    _ = ((R.choose t : ℝ) * ((R : ℝ)-t)) *
        (((N-R).choose (U-t) : ℝ) * ((U : ℝ)-t)) := by rw [haR, hbR]
    _ = _ := by ring

end
end D5.S3.Estimation.TimeArrow.RectangleHypergeometricMaxAtom
