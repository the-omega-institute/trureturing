/- GID: D5/S3/Quantum/Analysis/RefinedBMV/SingularFourth/ZeroSpectrumSigns
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform nonnegativity of the five singular Schur polynomials. -/

import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumBinding
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Uniform signs for the five factored polynomials in the four-copy
zero-spectrum Gram certificate. -/

namespace RefinedBMV.ZeroSpectrum

open RefinedBMV.DividedDifference.SparseExpansion (zeroSpectrum_matches_closed)
open RefinedBMV.ThreeBlockGram.ZeroSpectrum

noncomputable section

-- Widths and digit counts include the full static bounds on every prefix.
def SignPolynomial.degree : SignPolynomial → ℕ
  | .A | .B => 2
  | .P1 | .P2 => 4
  | .P3 => 7

def SignPolynomial.factorBound : SignPolynomial → ℤ
  | .A | .B => 40
  | .P1 | .P2 => 72
  | .P3 => 104

def SignPolynomial.width : SignPolynomial → ℕ
  | .A => 64
  | .B => 104
  | .P1 => 400
  | .P2 => 304
  | .P3 => 1152

def SignPolynomial.digits : SignPolynomial → ℕ
  | .A => 12
  | .B => 19
  | .P1 => 65
  | .P2 => 50
  | .P3 => 174

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem static_checked (k : SignPolynomial) :
    staticCheck k.groups k.degree k.factorBound k.width k.digits = true := by
  cases k <;> decide +kernel

-- The finite check uses the same grouped rate list and coefficient table as
-- the expansion identity. Each step works with one packed integer per rate.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem masks_checked_A : checkMasks 64 12 groupsA = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem masks_checked_B : checkMasks 104 19 groupsB = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem masks_checked_P1 : checkMasks 400 65 groupsP1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem masks_checked_P2 : checkMasks 304 50 groupsP2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option exponentiation.threshold 50000 in
private theorem masks_checked_P3 : checkMasks 1152 174 groupsP3 = true := by decide +kernel

private theorem masks_checked (k : SignPolynomial) :
    checkMasks k.width k.digits k.groups = true := by
  cases k
  · exact masks_checked_A
  · exact masks_checked_B
  · exact masks_checked_P1
  · exact masks_checked_P2
  · exact masks_checked_P3

theorem closed_nonneg_exp (k : SignPolynomial) (p t : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    0 ≤ k.closed p (Real.exp (-8*t)) (Real.exp (-p*t)) := by
  have h := nonneg_of_checks k.groups k.degree k.factorBound k.width k.digits
    (static_checked k) (masks_checked k) p t hp ht
  rw [zeroSpectrum_matches_closed] at h
  have hd : (0 : ℝ) < (k.denominator : ℝ) := by
    cases k <;> norm_num [SignPolynomial.denominator]
  exact nonneg_of_mul_nonneg_right h hd

/-- Uniform on the continuous closed-form parameters: integer p ≥ 1 is a
special case used for the complete homogeneous sums of the original problem. -/
theorem closed_nonneg (k : SignPolynomial) (p b : ℝ)
    (hp : 1 ≤ p) (hb : 0 < b) (hb₁ : b ≤ 1) :
    0 ≤ k.closed p b (b ^ (p/8)) := by
  let t : ℝ := -(Real.log b)/8
  have ht : 0 ≤ t := by
    dsimp [t]
    linarith [Real.log_nonpos hb.le hb₁]
  have h₁ : Real.exp (-8*t) = b := by
    rw [show -8*t = Real.log b by dsimp [t]; ring, Real.exp_log hb]
  have h₂ : Real.exp (-p*t) = b ^ (p/8) := by
    rw [Real.rpow_def_of_pos hb]
    congr 1
    dsimp [t]
    ring
  simpa only [h₁, h₂] using closed_nonneg_exp k p t hp ht

/-- All five actual signs appearing in the oracle's block Schur complements. -/
theorem all_signs (p b : ℝ) (hp : 1 ≤ p) (hb : 0 < b) (hb₁ : b ≤ 1) :
    0 ≤ Astar p b (b ^ (p/8)) ∧
    0 ≤ Bstar p b (b ^ (p/8)) ∧
    0 ≤ P1 p b (b ^ (p/8)) ∧
    0 ≤ P2 p b (b ^ (p/8)) ∧
    0 ≤ P3 p b (b ^ (p/8)) :=
  ⟨closed_nonneg .A p b hp hb hb₁, closed_nonneg .B p b hp hb hb₁,
    closed_nonneg .P1 p b hp hb hb₁, closed_nonneg .P2 p b hp hb hb₁,
    closed_nonneg .P3 p b hp hb hb₁⟩

end
end RefinedBMV.ZeroSpectrum


namespace RefinedBMV.ThreeBlockGram.ZeroSpectrum

/-- Supplies the exact scalar premise of allocation_of_signs. -/
theorem signs (p : ℕ) (hp : 0 < p) {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    Signs (p : ℝ) r (root p r) := by
  have hp₁ : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  obtain ⟨ha,hb,h1,h2,h3⟩ := RefinedBMV.ZeroSpectrum.all_signs (p : ℝ) r hp₁ hr hr₁.le
  exact ⟨ha,hb,h1,h2,h3⟩

end RefinedBMV.ThreeBlockGram.ZeroSpectrum
