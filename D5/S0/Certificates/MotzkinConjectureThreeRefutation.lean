/- GID: D5/S0/Certificates/MotzkinConjectureThreeRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/MotzkinConjectureThreeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Block, mathlib/module/Mathlib.Tactic.IntervalCases, mathlib/module/Mathlib.Tactic.NormNum]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/MotzkinConjectureThreeRefutation.claim; result=D5/S0/Certificates/MotzkinConjectureThreeRefutation.result; claim=D5/S0/Certificates/MotzkinConjectureThreeRefutation.claim
   digest: Refutes the printed universal first chain of Conjecture 3, arXiv:2502.21050v1, at r=9,n=1 even with r>=3; suspected-novel after literature search on 2026-09-10; makes no claim against a narrower author-intended proposition. -/

import D5.S0.Certificates.MotzkinConvolutionHankelRefutation
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 10000

namespace D5.S0.Certificates.MotzkinConjectureThreeRefutation

open D5.S0.Certificates.MotzkinConvolutionHankelRefutation (motzkin convolutionPower hankel)
open scoped BigOperators

/-!
The source is Wang--Zhang, arXiv:2502.21050v1, printed page 2, HTML
https://arxiv.org/html/2502.21050v1#Thmthm3. Its first chain quantifies over
all multiples of three and all n. We also impose the preceding prose's
`r >= 3`; the witness still belongs. Theorem 9's `r <= 27` does not impose
`r > 27` on the conjecture. The separate alpha clause is unnecessary.

This refutes the printed universal proposition. If the authors intended a
narrower range, this module does not assert that restricted proposition false.
Provenance: suspected-novel, searched 2026-09-10 (Asia/Singapore). The arXiv
version history lists v1 only. Exact-title and erratum searches in arXiv,
Crossref, OpenAlex and DuckDuckGo Lite found no attestation of this sign error.
The citing paper https://arxiv.org/html/2503.17187, section 3.2 and reference 24,
discusses Motzkin convolution determinants without identifying this refutation.
OpenAlex reports zero indexed citations despite that explicit reference;
the search is bounded evidence, not a claim of established priority.

The only included declarations are claim and result. All finite coefficient
proofs and elimination data are local to result. They certify a NEW numerical
obstruction
on result's live proof path (escape-witness form 2), rather than applying an
already frozen numerical theorem. All sequence/determinant definitions are
imported; the local certificate is checked by the kernel.
-/

/-- The complete first equality chain, universally quantified, with the
source's permissive contextual lower bound on r. -/
def claim : Prop :=
  ∀ r : ℕ, 3 ≤ r → r % 3 = 0 → ∀ n : ℕ,
    hankel (convolutionPower r) (r * n) =
        (-1 : ℤ) ^ n * ((n + 1 : ℕ) : ℤ) ^ (r - 1) ∧
    hankel (convolutionPower r) (r * n + 1) =
        (-1 : ℤ) ^ n * ((n + 1 : ℕ) : ℤ) ^ (r - 1)

set_option maxHeartbeats 4000000 in
-- The budget covers the finite coefficient sums and the kernel-checked matrix certificate.
/-- The eligible specialization r = 9, n = 1 contradicts a kernel-checked
integer elimination certificate: its determinant is 256, whereas the chain
requires -256. No finite positive instance is exported. -/
theorem result : ¬ claim := by
  intro h
  -- Finite coefficient certificates for the imported Cauchy-product definition.
  have power_zero (n : ℕ) :
      convolutionPower 0 n = if n = 0 then 1 else 0 := rfl
  have catalan_value_4 : catalan 4 = 14 := by decide +kernel
  have catalan_value_5 : catalan 5 = 42 := by decide +kernel
  have catalan_value_6 : catalan 6 = 132 := by decide +kernel
  have catalan_value_7 : catalan 7 = 429 := by decide +kernel
  have catalan_value_8 : catalan 8 = 1430 := by decide +kernel
  -- Normalize the seventeen finite Motzkin sums in this single certificate.
  have motzkin_values (n : ℕ) (hn : n < 17) :
      motzkin n = ([1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798, 15511, 41835, 113634, 310572,
        853467] : List ℤ).getD n 0 := by
    interval_cases n <;>
      norm_num [motzkin, Finset.sum_range_succ, Nat.choose, catalan_two, catalan_three,
        catalan_value_4, catalan_value_5, catalan_value_6, catalan_value_7, catalan_value_8]
  have power_1_values (n : ℕ) (hn : n < 17) :
      convolutionPower 1 n = ([1, 1, 2, 4, 9, 21, 51, 127, 323, 835, 2188, 5798, 15511, 41835,
        113634, 310572, 853467] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 0 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_zero, motzkin_values]
  have power_2_values (n : ℕ) (hn : n < 17) :
      convolutionPower 2 n = ([1, 2, 5, 12, 30, 76, 196, 512, 1353, 3610, 9713, 26324, 71799,
        196938, 542895, 1503312, 4179603] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 1 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_1_values, motzkin_values]
  have power_3_values (n : ℕ) (hn : n < 17) :
      convolutionPower 3 n = ([1, 3, 9, 25, 69, 189, 518, 1422, 3915, 10813, 29964, 83304, 232323,
        649845, 1822824, 5126520, 14453451] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 2 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_2_values, motzkin_values]
  have power_4_values (n : ℕ) (hn : n < 17) :
      convolutionPower 4 n = ([1, 4, 14, 44, 133, 392, 1140, 3288, 9438, 27016, 77220, 220584,
        630084, 1800384, 5147328, 14727168, 42171849] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 3 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_3_values, motzkin_values]
  have power_5_values (n : ℕ) (hn : n < 17) :
      convolutionPower 5 n = ([1, 5, 20, 70, 230, 726, 2235, 6765, 20240, 60060, 177177, 520455,
        1524120, 4453320, 12991230, 37854954, 110218905] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 4 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_4_values, motzkin_values]
  have power_6_values (n : ℕ) (hn : n < 17) :
      convolutionPower 6 n = ([1, 6, 27, 104, 369, 1242, 4037, 12804, 39897, 122694, 373581,
        1128816, 3390582, 10136556, 30192102, 89662216, 265640691] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 5 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_5_values, motzkin_values]
  have power_7_values (n : ℕ) (hn : n < 17) :
      convolutionPower 7 n = ([1, 7, 35, 147, 560, 2002, 6853, 22737, 73710, 234780, 737646,
        2292654, 7064316, 21615160, 65759570, 199117226, 600560037] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 6 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_6_values, motzkin_values]
  have power_8_values (n : ℕ) (hn : n < 17) :
      convolutionPower 8 n = ([1, 8, 44, 200, 814, 3080, 11076, 38376, 129285, 426192, 1381080,
        4414288, 13952308, 43695440, 135802120, 419367696, 1288054878] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 7 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_7_values, motzkin_values]
  have power_9_values (n : ℕ) (hn : n < 17) :
      convolutionPower 9 n = ([1, 9, 54, 264, 1143, 4563, 17199, 62127, 217242, 740554, 2473704,
        8127972, 26347110, 84448350, 268127145, 844521291, 2641866894] : List ℤ).getD n 0 := by
    change (∑ k ∈ Finset.range (n + 1), convolutionPower 8 k * motzkin (n - k)) = _
    interval_cases n <;> norm_num [Finset.sum_range_succ, power_8_values, motzkin_values]
  -- Independently generated by fraction-free elimination on [sample | identity].
  -- These data are untrusted inputs: result proves lower * sample = upper.
  let sample : Matrix (Fin 9) (Fin 9) ℤ :=
    fun i j => ([1, 9, 54, 264, 1143, 4563, 17199, 62127, 217242, 740554, 2473704, 8127972,
        26347110, 84448350, 268127145, 844521291, 2641866894] : List ℤ).getD (i.val + j.val) 0
  let lower : Matrix (Fin 9) (Fin 9) ℤ :=
    !![1, 0, 0, 0, 0, 0, 0, 0, 0;
      -9, 1, 0, 0, 0, 0, 0, 0, 0;
      -540, 222, -27, 0, 0, 0, 0, 0, 0;
      32589, -34263, 12015, -1413, 0, 0, 0, 0, 0;
      2237301, -1267002, -185895, 232308, -36855, 0, 0, 0, 0;
      163198314, -113506758, -101227482, 124165710, -42475266, 4842018, 0, 0, 0;
      -1086502059, 1082484810, 440962731, -1024137468, 530110575, -117329148, 9730854, 0, 0;
      4150189197, -1397402061, -9559392444, 6405302448, 3929619393, -5019541731, 1678841451,
        -187167357, 0;
      5152752, -6688352, -10198224, 19358784, -2766672, -10919232, 8073504, -2235648, 223344]
  let upper : Matrix (Fin 9) (Fin 9) ℤ :=
    !![1, 9, 54, 264, 1143, 4563, 17199, 62127, 217242;
      0, -27, -222, -1233, -5724, -23868, -92664, -341901, -1214624;
      0, 0, -1413, -12015, -68607, -323271, -1360800, -5315814, -19697700;
      0, 0, 0, -36855, -232308, -1092771, -4399362, -16293285, -57173040;
      0, 0, 0, 0, 4842018, 42475266, 248362767, 1190285685, 5073319980;
      0, 0, 0, 0, 0, 9730854, 117329148, 791444682, 4156761888;
      0, 0, 0, 0, 0, 0, -187167357, -1678841451, -10039231530;
      0, 0, 0, 0, 0, 0, 0, 223344, 2235648;
      0, 0, 0, 0, 0, 0, 0, 0, 256]
  have hankel_matrix : (fun i j : Fin 9 => convolutionPower 9 (i.val + j.val)) =
      sample := by
    funext i j
    exact power_9_values (i.val + j.val) (by omega)
  have lower_times_sample : lower * sample = upper := by
    dsimp only [lower, sample, upper]
    decide +kernel
  have lower_triangular : lower.IsLowerTriangular := by
    dsimp only [lower]
    decide +kernel
  have upper_triangular : upper.IsUpperTriangular := by
    dsimp only [upper]
    decide +kernel
  have det_lower : Matrix.det lower = (2769389844306214239279842796063420480 : ℤ) := by
    rw [Matrix.det_of_isLowerTriangular lower lower_triangular]
    dsimp only [lower]
    decide +kernel
  have det_upper : Matrix.det upper = (708963800142390845255639755792235642880 : ℤ) := by
    rw [Matrix.det_of_isUpperTriangular upper_triangular]
    dsimp only [upper]
    decide +kernel
  have determinants := Matrix.det_mul lower sample
  rw [lower_times_sample, det_lower, det_upper] at determinants
  have required := (h 9 (by decide) (by decide) 1).1
  change Matrix.det (fun i j : Fin 9 => convolutionPower 9 (i.val + j.val)) =
      (-1 : ℤ) ^ 1 * (2 : ℤ) ^ 8 at required
  rw [hankel_matrix] at required
  norm_num at required
  rw [required] at determinants
  norm_num at determinants

#print axioms claim
#print axioms result

end D5.S0.Certificates.MotzkinConjectureThreeRefutation
