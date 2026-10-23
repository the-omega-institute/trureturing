/- GID: D5/S3/Geometry/Hyperideal/LocalMismatchCertificate
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LocalMismatchCertificate
   mirror-E: none(waiver:finite-local-certificate)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.claim; result=D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.result; claim=D5/S3/Geometry/Hyperideal/LocalMismatchCertificate.claim
   digest: An exact local certificate permits different flat pi-edge labels on equal shared-face lengths. -/

import D5.S3.Geometry.Hyperideal.FourCycleEnvelopes
import Mathlib.Tactic

/-!
An exact local certificate permits different flat pi-edge labels on equal
shared-face lengths. Only the finite arithmetic witness is formalized.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Geometry.Hyperideal.LocalMismatchCertificate

open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

/- The coordinate order is (12, 13, 14, 34, 24, 23). -/
def sigma : Fin 6 → ℝ := ![2, 2, 2, 20, 2, 2]

def tau : Fin 6 → ℝ := ![2, 2, 2, 2, 20, 2]

def sigmaPi : List (Nat × Nat) := [(12, 34)]

def tauPi : List (Nat × Nat) := [(13, 24)]

/- This is the finite assertion that the displayed local mismatch cannot occur. -/
def claim : Prop :=
  ¬ (
    sigma 0 = tau 0 ∧
    sigma 1 = tau 1 ∧
    sigma 5 = tau 5 ∧
    sigmaPi ≠ tauPi ∧
    cosine (sigma 0) (sigma 1) (sigma 2) (sigma 3) (sigma 4) (sigma 5) =
      -(4 / 3 : ℝ) ∧
    cosine (tau 0) (tau 1) (tau 2) (tau 4) (tau 3) (tau 5) =
      -(4 / 3 : ℝ) ∧
    cosine 20 2 2 2 2 2 = -(10 / 9 : ℝ) ∧
    (7 : ℝ) < 8)

/- The finite certificate refutes the claim that equal shared-face lengths force
   equal flat pi-edge labels. It carries no global gluing or manifold claim. -/
theorem result : ¬ claim := by
  intro h
  have h27 : Real.sqrt (27 : ℝ) * Real.sqrt 27 = 27 := by
    simpa [pow_two] using (Real.sq_sqrt (show (0 : ℝ) ≤ 27 by norm_num))
  have h567 : Real.sqrt (567 : ℝ) * Real.sqrt 567 = 567 := by
    simpa [pow_two] using (Real.sq_sqrt (show (0 : ℝ) ≤ 567 by norm_num))
  have h27ne : Real.sqrt (27 : ℝ) ≠ 0 := by positivity
  have h567ne : Real.sqrt (567 : ℝ) ≠ 0 := by positivity
  have hfirst : -36 / Real.sqrt 27 / Real.sqrt 27 = -(4 / 3 : ℝ) := by
    field_simp [h27ne]
    nlinarith [h27]
  have hbig : -630 / Real.sqrt 567 / Real.sqrt 567 = -(10 / 9 : ℝ) := by
    field_simp [h567ne]
    nlinarith [h567]
  apply h
  norm_num [sigma, tau, sigmaPi, tauPi, cosine, numerator, rad, hfirst, hbig]

#print axioms result

end D5.S3.Geometry.Hyperideal.LocalMismatchCertificate
