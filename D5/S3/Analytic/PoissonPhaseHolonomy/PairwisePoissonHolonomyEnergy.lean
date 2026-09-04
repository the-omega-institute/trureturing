/- GID: D5/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy
   generality: G
   mirror-B: D5/B/S3/Analytic/PoissonPhaseHolonomy/PairwisePoissonHolonomyEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Poisson phase energy is nonnegative, detects equal heights, and is shift invariant. -/

/- Ported in part from TauCetiProject/TauCeti commit
   bbd2f34ff81c827b099c0c58d05372c6091ac050, files
   `TauCeti/MeasureTheory/Integral/ExpDecay.lean` and
   `TauCeti/Analysis/Fourier/ExpNegAbs.lean`.
   Modified by trureturing on 2026-09-02 for Lean/mathlib v4.33.0 and local routing.

   Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
   Released under Apache 2.0 license as described below.
   SPDX-License-Identifier: Apache-2.0

   Retirement condition: replace the two ported lemmas with direct imports when this
   repository's pinned mathlib contains equivalent declarations. -/

/-
Apache License
Version 2.0, January 2004
http://www.apache.org/licenses/

TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

1. Definitions.

"License" shall mean the terms and conditions for use, reproduction, and
distribution as defined by Sections 1 through 9 of this document.

"Licensor" shall mean the copyright owner or entity authorized by the copyright
owner that is granting the License.

"Legal Entity" shall mean the union of the acting entity and all other entities
that control, are controlled by, or are under common control with that entity.
For the purposes of this definition, "control" means (i) the power, direct or
indirect, to cause the direction or management of such entity, whether by
contract or otherwise, or (ii) ownership of fifty percent (50%) or more of the
outstanding shares, or (iii) beneficial ownership of such entity.

"You" (or "Your") shall mean an individual or Legal Entity exercising
permissions granted by this License.

"Source" form shall mean the preferred form for making modifications, including
but not limited to software source code, documentation source, and configuration
files.

"Object" form shall mean any form resulting from mechanical transformation or
translation of a Source form, including but not limited to compiled object code,
generated documentation, and conversions to other media types.

"Work" shall mean the work of authorship, whether in Source or Object form, made
available under the License, as indicated by a copyright notice that is included
in or attached to the work.

"Derivative Works" shall mean any work, whether in Source or Object form, that is
based on (or derived from) the Work and for which the editorial revisions,
annotations, elaborations, or other modifications represent, as a whole, an
original work of authorship. Derivative Works shall not include works that remain
separable from, or merely link (or bind by name) to the interfaces of, the Work
and Derivative Works thereof.

"Contribution" shall mean any work of authorship, including the original version
of the Work and any modifications or additions to that Work or Derivative Works,
that is intentionally submitted to Licensor for inclusion in the Work by the
copyright owner or by an individual or Legal Entity authorized to submit on
behalf of the copyright owner. "Submitted" means any form of electronic, verbal,
or written communication sent to the Licensor or its representatives, excluding
communication conspicuously marked or otherwise designated in writing as "Not a
Contribution."

"Contributor" shall mean Licensor and any individual or Legal Entity on behalf
of whom a Contribution has been received and subsequently incorporated within
the Work.

2. Grant of Copyright License. Subject to the terms and conditions of this
License, each Contributor hereby grants to You a perpetual, worldwide,
non-exclusive, no-charge, royalty-free, irrevocable copyright license to
reproduce, prepare Derivative Works of, publicly display, publicly perform,
sublicense, and distribute the Work and such Derivative Works in Source or
Object form.

3. Grant of Patent License. Subject to the terms and conditions of this License,
each Contributor hereby grants to You a perpetual, worldwide, non-exclusive,
no-charge, royalty-free, irrevocable (except as stated in this section) patent
license to make, have made, use, offer to sell, sell, import, and otherwise
transfer the Work, where such license applies only to those patent claims
licensable by such Contributor that are necessarily infringed by their
Contribution(s) alone or by combination of their Contribution(s) with the Work
to which such Contribution(s) was submitted. If You institute patent litigation
against any entity alleging that the Work or a Contribution incorporated within
the Work constitutes direct or contributory patent infringement, then any patent
licenses granted to You under this License for that Work shall terminate as of
the date such litigation is filed.

4. Redistribution. You may reproduce and distribute copies of the Work or
Derivative Works thereof in any medium, with or without modifications, and in
Source or Object form, provided that You meet the following conditions:

(a) You must give any other recipients of the Work or Derivative Works a copy of
this License; and

(b) You must cause any modified files to carry prominent notices stating that
You changed the files; and

(c) You must retain, in the Source form of any Derivative Works that You
distribute, all copyright, patent, trademark, and attribution notices from the
Source form of the Work, excluding those notices that do not pertain to any part
of the Derivative Works; and

(d) If the Work includes a NOTICE text file as part of its distribution, then
any Derivative Works that You distribute must include a readable copy of the
attribution notices contained within such NOTICE file. The contents of the
NOTICE file are for informational purposes only and do not modify the License.

You may add Your own copyright statement to Your modifications and may provide
additional or different license terms and conditions for use, reproduction, or
distribution of Your modifications, provided that Your use, reproduction, and
distribution of the Work otherwise complies with the conditions stated in this
License.

5. Submission of Contributions. Unless You explicitly state otherwise, any
Contribution intentionally submitted for inclusion in the Work by You to the
Licensor shall be under the terms and conditions of this License, without any
additional terms or conditions.

6. Trademarks. This License does not grant permission to use the trade names,
trademarks, service marks, or product names of the Licensor, except as required
for reasonable and customary use in describing the origin of the Work and
reproducing the content of the NOTICE file.

7. Disclaimer of Warranty. Unless required by applicable law or agreed to in
writing, Licensor provides the Work (and each Contributor provides its
Contributions) on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
KIND, either express or implied, including, without limitation, any warranties
or conditions of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
PARTICULAR PURPOSE. You are solely responsible for determining the
appropriateness of using or redistributing the Work and assume any risks
associated with Your exercise of permissions under this License.

8. Limitation of Liability. In no event and under no legal theory, whether in
tort, contract, or otherwise, unless required by applicable law or agreed to in
writing, shall any Contributor be liable to You for damages, including any
direct, indirect, special, incidental, or consequential damages arising as a
result of this License or out of the use or inability to use the Work.

9. Accepting Warranty or Additional Liability. While redistributing the Work or
Derivative Works thereof, You may choose to offer, and charge a fee for,
acceptance of support, warranty, indemnity, or other liability obligations and/or
rights consistent with this License. In accepting such obligations, You may act
only on Your own behalf and on Your sole responsibility, not on behalf of any
other Contributor, and only if You agree to indemnify, defend, and hold each
Contributor harmless for any liability incurred by, or claims asserted against,
such Contributor by reason of your accepting any such warranty or additional
liability.

END OF TERMS AND CONDITIONS

APPENDIX: How to apply the Apache License to your work.

Copyright [yyyy] [name of copyright owner]

Licensed under the Apache License, Version 2.0 (the "License"); you may not use
this file except in compliance with the License. You may obtain a copy of the
License at http://www.apache.org/licenses/LICENSE-2.0 . Unless required by
applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
KIND, either express or implied. See the License for the specific language
governing permissions and limitations under the License.
-/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.PoissonPhaseHolonomy.PairwisePoissonHolonomyEnergy

open MeasureTheory Set

noncomputable section

/-- The source quantity `a_ij`, the sum of the two positive transverse depths. -/
def poissonTransverseDepthSum (deltaI deltaJ : ℝ) : ℝ :=
  deltaI + deltaJ

/-- The source quantity `d_ij`, the relative phase height `gamma_j - gamma_i`. -/
def poissonHeightDifference (gammaI gammaJ : ℝ) : ℝ :=
  gammaJ - gammaI

/-- The explicit Poisson phase-swap curvature from source equation (1391.3). -/
noncomputable def pairwisePoissonSwapCurvature
    (deltaI deltaJ gammaI gammaJ k : ℝ) : ℂ :=
  (2 : ℂ) * Complex.I *
    (Real.exp
      (-(poissonTransverseDepthSum deltaI deltaJ * |k|)) : ℂ) *
    (Real.sin (k * poissonHeightDifference gammaI gammaJ) : ℂ)

/-- The source energy `(1 / (2*pi)) integral_R |R_ij(k)|^2 dk`. -/
noncomputable def poissonPhaseHolonomyEnergy
    (deltaI deltaJ gammaI gammaJ : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ k : ℝ,
      Complex.normSq
        (pairwisePoissonSwapCurvature deltaI deltaJ gammaI gammaJ k)

/- The following two lemmas are the adapted TauCeti leaves named in the
   provenance and license block above. -/

/-- The two-sided real exponential is integrable at every positive rate. -/
private theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-(a * |x|))) := by
  have hIic : IntegrableOn (fun x : ℝ => Real.exp (-(a * |x|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun (fun x hx => ?_)
      measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.mp hx)]
    ring_nf
  have hIoi : IntegrableOn (fun x : ℝ => Real.exp (-(a * |x|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hx)]
    ring_nf
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- The Lorentzian pairing of a two-sided exponential with a complex oscillation. -/
private theorem integral_exp_mul_I_mul_exp_neg_mul_abs
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ,
        Complex.exp ((b : ℂ) * x * Complex.I) *
          (Real.exp (-(a * |x|)) : ℂ)) =
      ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hreIic : ((a : ℂ) + b * Complex.I).re = a := by simp
  have hreIoi : (-(a : ℂ) + b * Complex.I).re = -a := by simp
  have key : ∀ c x : ℝ,
      Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (c * x) : ℂ) =
        Complex.exp (((c : ℂ) + b * Complex.I) * x) := by
    intro c x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hIic : EqOn
      (fun x : ℝ =>
        Complex.exp ((b : ℂ) * x * Complex.I) *
          (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ => Complex.exp (((a : ℂ) + b * Complex.I) * x))
      (Iic 0) := by
    intro x hx
    have hxa : -(a * |x|) = a * x := by
      rw [abs_of_nonpos (mem_Iic.mp hx)]
      ring
    simpa only [hxa] using key a x
  have hIoi : EqOn
      (fun x : ℝ =>
        Complex.exp ((b : ℂ) * x * Complex.I) *
          (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ => Complex.exp ((-(a : ℂ) + b * Complex.I) * x))
      (Ioi 0) := by
    intro x hx
    have hxa : -(a * |x|) = -a * x := by
      rw [abs_of_pos (mem_Ioi.mp hx)]
      ring
    simpa only [hxa, Complex.ofReal_neg] using key (-a) x
  have hint : Integrable
      (fun x : ℝ =>
        Complex.exp ((b : ℂ) * x * Complex.I) *
          (Real.exp (-(a * |x|)) : ℂ)) :=
    ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
      (.of_forall fun x => by simp [Complex.norm_exp])
  have hneIic : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hreIic
    exact ha.ne' (by simpa using hreIic.symm)
  have hneIoi : -(a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hreIoi
    simp only [Complex.zero_re] at hreIoi
    exact ha.ne' (by linarith)
  have hsq : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn,
    setIntegral_congr_fun measurableSet_Iic hIic,
    setIntegral_congr_fun measurableSet_Ioi hIoi,
    integral_exp_mul_complex_Iic (by rw [hreIic]; exact ha),
    integral_exp_mul_complex_Ioi (by rw [hreIoi]; linarith)]
  have hprod :
      ((a : ℂ) + b * Complex.I) * (-(a : ℂ) + b * Complex.I) =
        -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have hdenom : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have h : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsq.ne'
    push_cast at h
    exact h
  rw [Complex.ofReal_div]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (-2 * (a : ℂ)) * hprod

private theorem damped_cosine_integral
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Real.exp (-(a * |x|)) * Real.cos (b * x)) =
      2 * a / (a ^ 2 + b ^ 2) := by
  let f : ℝ → ℂ := fun x =>
    Complex.exp ((b : ℂ) * x * Complex.I) *
      (Real.exp (-(a * |x|)) : ℂ)
  have hf : Integrable f := by
    dsimp only [f]
    exact ((integrable_exp_neg_mul_abs ha).ofReal).bdd_mul (c := 1) (by fun_prop)
      (.of_forall fun x => by simp [Complex.norm_exp])
  calc
    (∫ x : ℝ, Real.exp (-(a * |x|)) * Real.cos (b * x)) =
        ∫ x : ℝ, (f x).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [f]
      rw [show (b : ℂ) * (x : ℂ) * Complex.I =
          ((b * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp only [Complex.mul_re, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      ring
    _ = (∫ x : ℝ, f x).re := integral_re hf
    _ = _ := by
      rw [show (∫ x : ℝ, f x) =
          ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) by
        simpa only [f] using integral_exp_mul_I_mul_exp_neg_mul_abs ha b]
      norm_cast

private theorem damped_sine_sq_integral
    {a : ℝ} (ha : 0 < a) (d : ℝ) :
    (∫ x : ℝ,
        Real.exp (-((2 * a) * |x|)) * Real.sin (x * d) ^ 2) =
      d ^ 2 / (2 * a * (a ^ 2 + d ^ 2)) := by
  have hTwoA : 0 < 2 * a := by positivity
  have hExp : Integrable (fun x : ℝ => Real.exp (-((2 * a) * |x|))) :=
    integrable_exp_neg_mul_abs hTwoA
  have hCos : Integrable
      (fun x : ℝ => Real.exp (-((2 * a) * |x|)) * Real.cos ((2 * d) * x)) := by
    exact hExp.mul_bdd (c := 1) (by fun_prop)
      (.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one ((2 * d) * x))
  have hExpValue :
      (∫ x : ℝ, Real.exp (-((2 * a) * |x|))) = 1 / a := by
    calc
      (∫ x : ℝ, Real.exp (-((2 * a) * |x|))) =
          2 * (2 * a) / ((2 * a) ^ 2) := by
        simpa using damped_cosine_integral hTwoA 0
      _ = 1 / a := by
        field_simp [ha.ne']
  have hCosValue :
      (∫ x : ℝ,
          Real.exp (-((2 * a) * |x|)) * Real.cos ((2 * d) * x)) =
        a / (a ^ 2 + d ^ 2) := by
    rw [damped_cosine_integral hTwoA (2 * d)]
    have hdenom : a ^ 2 + d ^ 2 ≠ 0 := by positivity
    field_simp [ha.ne', hdenom]
  calc
    (∫ x : ℝ,
        Real.exp (-((2 * a) * |x|)) * Real.sin (x * d) ^ 2) =
        ∫ x : ℝ,
          (1 / 2 : ℝ) * Real.exp (-((2 * a) * |x|)) -
            (1 / 2 : ℝ) *
              (Real.exp (-((2 * a) * |x|)) * Real.cos ((2 * d) * x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Real.sin_sq_eq_half_sub]
      ring
    _ = (1 / 2 : ℝ) * (1 / a) -
        (1 / 2 : ℝ) * (a / (a ^ 2 + d ^ 2)) := by
      rw [integral_sub (hExp.const_mul _) (hCos.const_mul _),
        integral_const_mul, integral_const_mul, hExpValue, hCosValue]
    _ = _ := by
      have hdenom : a ^ 2 + d ^ 2 ≠ 0 := by positivity
      field_simp [ha.ne', hdenom]
      ring

private theorem pairwise_curvature_normSq
    (deltaI deltaJ gammaI gammaJ k : ℝ) :
    Complex.normSq
        (pairwisePoissonSwapCurvature deltaI deltaJ gammaI gammaJ k) =
      4 *
        (Real.exp
            (-((2 * poissonTransverseDepthSum deltaI deltaJ) * |k|)) *
          Real.sin (k * poissonHeightDifference gammaI gammaJ) ^ 2) := by
  have hExp :
      Real.exp
          (-(poissonTransverseDepthSum deltaI deltaJ * |k|)) *
        Real.exp
          (-(poissonTransverseDepthSum deltaI deltaJ * |k|)) =
      Real.exp
        (-((2 * poissonTransverseDepthSum deltaI deltaJ) * |k|)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [pairwisePoissonSwapCurvature, Complex.normSq_mul,
    Complex.normSq_ofNat, Complex.normSq_I, Complex.normSq_ofReal]
  rw [hExp]
  ring

/-- The integral energy has the rational Poisson phase-holonomy closed form. -/
theorem poisson_phase_holonomy_energy_closed_form
    (deltaI deltaJ gammaI gammaJ : ℝ)
    (hDeltaI : 0 < deltaI) (hDeltaJ : 0 < deltaJ) :
    poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ =
      poissonHeightDifference gammaI gammaJ ^ 2 /
        (Real.pi * poissonTransverseDepthSum deltaI deltaJ *
          (poissonTransverseDepthSum deltaI deltaJ ^ 2 +
            poissonHeightDifference gammaI gammaJ ^ 2)) := by
  have hDepth : 0 < poissonTransverseDepthSum deltaI deltaJ := by
    simp only [poissonTransverseDepthSum]
    linarith
  rw [poissonPhaseHolonomyEnergy]
  have hIntegral := damped_sine_sq_integral hDepth
    (poissonHeightDifference gammaI gammaJ)
  rw [show (∫ k : ℝ,
        Complex.normSq
          (pairwisePoissonSwapCurvature deltaI deltaJ gammaI gammaJ k)) =
      ∫ k : ℝ,
        4 *
          (Real.exp
              (-((2 * poissonTransverseDepthSum deltaI deltaJ) * |k|)) *
            Real.sin (k * poissonHeightDifference gammaI gammaJ) ^ 2) by
    apply integral_congr_ae
    exact .of_forall (pairwise_curvature_normSq deltaI deltaJ gammaI gammaJ)]
  rw [integral_const_mul, hIntegral]
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hDepthNe : poissonTransverseDepthSum deltaI deltaJ ≠ 0 := hDepth.ne'
  have hSumSq :
      poissonTransverseDepthSum deltaI deltaJ ^ 2 +
          poissonHeightDifference gammaI gammaJ ^ 2 ≠ 0 := by
    positivity
  field_simp [hPi, hDepthNe, hSumSq]
  ring

/-- Poisson phase-holonomy energy: closed form, positivity, zero detection,
and invariance under every common phase-height translation. -/
theorem pairwise_poisson_holonomy_energy
    (deltaI deltaJ gammaI gammaJ : ℝ)
    (hDeltaI : 0 < deltaI) (hDeltaJ : 0 < deltaJ) :
    poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ =
        poissonHeightDifference gammaI gammaJ ^ 2 /
          (Real.pi * poissonTransverseDepthSum deltaI deltaJ *
            (poissonTransverseDepthSum deltaI deltaJ ^ 2 +
              poissonHeightDifference gammaI gammaJ ^ 2)) ∧
    0 ≤ poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ ∧
    (poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ = 0 →
      gammaI = gammaJ) ∧
    (gammaI = gammaJ →
      poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ = 0) ∧
    ∀ c : ℝ,
      poissonPhaseHolonomyEnergy deltaI deltaJ (gammaI + c) (gammaJ + c) =
        poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ := by
  have hDepth : 0 < poissonTransverseDepthSum deltaI deltaJ := by
    simp only [poissonTransverseDepthSum]
    linarith
  have hFormula := poisson_phase_holonomy_energy_closed_form
    deltaI deltaJ gammaI gammaJ hDeltaI hDeltaJ
  refine ⟨hFormula, ?_, ?_, ?_, ?_⟩
  · rw [hFormula]
    positivity
  · intro hZero
    rw [hFormula] at hZero
    have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hDepthNe : poissonTransverseDepthSum deltaI deltaJ ≠ 0 := hDepth.ne'
    have hSumSq :
        poissonTransverseDepthSum deltaI deltaJ ^ 2 +
            poissonHeightDifference gammaI gammaJ ^ 2 ≠ 0 := by
      positivity
    have hDifferenceSq : poissonHeightDifference gammaI gammaJ ^ 2 = 0 := by
      exact (div_eq_zero_iff.mp hZero).resolve_right
        (mul_ne_zero (mul_ne_zero hPi hDepthNe) hSumSq)
    simp only [poissonHeightDifference] at hDifferenceSq
    nlinarith
  · intro hEqual
    rw [hFormula]
    simp [poissonHeightDifference, hEqual]
  · intro c
    rw [poisson_phase_holonomy_energy_closed_form
      deltaI deltaJ (gammaI + c) (gammaJ + c) hDeltaI hDeltaJ,
      hFormula]
    simp only [poissonHeightDifference]
    ring

private example
    (deltaI deltaJ gammaI gammaJ : ℝ)
    (hDeltaI : 0 < deltaI) (hDeltaJ : 0 < deltaJ)
    (hEnergy : poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ = 0) :
    gammaI = gammaJ := by
  exact (pairwise_poisson_holonomy_energy
    deltaI deltaJ gammaI gammaJ hDeltaI hDeltaJ).2.2.1 hEnergy

private example
    (deltaI deltaJ gammaI gammaJ : ℝ)
    (hDeltaI : 0 < deltaI) (hDeltaJ : 0 < deltaJ) :
    poissonPhaseHolonomyEnergy deltaI deltaJ (gammaI + 1) (gammaJ + 1) =
      poissonPhaseHolonomyEnergy deltaI deltaJ gammaI gammaJ := by
  exact (pairwise_poisson_holonomy_energy
    deltaI deltaJ gammaI gammaJ hDeltaI hDeltaJ).2.2.2.2 1

private example :
    0 < poissonPhaseHolonomyEnergy 1 1 0 1 := by
  rw [poisson_phase_holonomy_energy_closed_form 1 1 0 1 (by norm_num) (by norm_num)]
  norm_num [poissonHeightDifference, poissonTransverseDepthSum]
  positivity

#print axioms poisson_phase_holonomy_energy_closed_form
#print axioms pairwise_poisson_holonomy_energy

end

end D5.S3.Analytic.PoissonPhaseHolonomy.PairwisePoissonHolonomyEnergy
