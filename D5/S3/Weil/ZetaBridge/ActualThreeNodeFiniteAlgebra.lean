/- GID: D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: none
   digest: Exact physical three-node finite trace and determinant polynomials retain both arithmetic branches. -/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteAlgebra

def U (g mu a r : ℝ) : ℝ :=
  18 * (g ^ 2 + mu) + 12 * g * a * r +
    (8 * a ^ 2 / 3 - 4 * (g ^ 2 + mu)) * r ^ 2 -
    2 * g * a * r ^ 3 + 2 * (g ^ 2 + mu) * r ^ 4 / 5

def T (g mu a r : ℝ) : ℝ :=
  6 * g * a * r + (8 * a ^ 2 / 3 + 4 * (g ^ 2 + mu)) * r ^ 2 +
    g * a * r ^ 3 - 4 * (g ^ 2 + mu) * r ^ 4 / 5

def C (g mu a r : ℝ) : ℝ :=
  8 * a ^ 2 * r ^ 2 / 3 + 4 * g * a * r ^ 3 +
    8 * (g ^ 2 + mu) * r ^ 4 / 5

def O (g mu a r : ℝ) : ℝ :=
  4 * a ^ 2 + 4 * g * a * r + 4 * (g ^ 2 + mu) * r ^ 2 / 3

def evenDet (g mu a r : ℝ) : ℝ :=
  U g mu a r / 3 * (C g mu a r / 6) -
    (T g mu a r / Real.sqrt 18) ^ 2

lemma finite_trace_identity (g mu a r : ℝ) :
    U g mu a r / 3 + C g mu a r / 6 =
      6 * (g ^ 2 + mu) + 4 * g * a * r +
        4 / 3 * (a ^ 2 - (g ^ 2 + mu)) * r ^ 2 +
        2 * (g ^ 2 + mu) * r ^ 4 / 5 := by
  dsimp [U, C]
  ring

lemma finite_determinant_identity (g mu a r : ℝ) :
    evenDet g mu a r =
      (2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3) * r ^ 2 +
      (4 * g * a * (g ^ 2 + mu) / 3) * r ^ 3 +
      (2 * a ^ 2 * g ^ 2 - 16 * a ^ 2 * (g ^ 2 + mu) / 9 +
        32 * (g ^ 2 + mu) ^ 2 / 45) * r ^ 4 +
      (4 * g * a * (g ^ 2 + mu) / 15) * r ^ 5 +
      (a ^ 2 * (g ^ 2 + 16 * mu) / 30) * r ^ 6 := by
  have hs : (Real.sqrt (18 : ℝ)) ^ 2 = 18 := Real.sq_sqrt (by norm_num)
  simp only [evenDet, div_pow, hs]
  dsimp [U, T, C]
  ring

lemma exceptional_trace_identity (g mu r : ℝ) :
    U g mu 0 r / 3 + C g mu 0 r / 6 =
      6 * (g ^ 2 + mu) - 4 * (g ^ 2 + mu) * r ^ 2 / 3 +
        2 * (g ^ 2 + mu) * r ^ 4 / 5 := by
  rw [finite_trace_identity]
  ring

lemma exceptional_determinant_identity (g mu r : ℝ) :
    evenDet g mu 0 r = 32 * (g ^ 2 + mu) ^ 2 * r ^ 4 / 45 := by
  rw [finite_determinant_identity]
  ring

end D5.S3.Weil.ZetaBridge.ActualThreeNodeFiniteAlgebra
