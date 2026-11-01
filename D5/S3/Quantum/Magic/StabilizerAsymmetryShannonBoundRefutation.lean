/- GID: D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.claim; result=D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.result; claim=D5/S3/Quantum/Magic/StabilizerAsymmetryShannonBoundRefutation.claim
   digest: A three-qubit state refutes the Shannon branch-and-bound entropy lower bound. -/

import D5.S3.Entropy.TwoDeletionRunEntropyBounds
import D5.S3.Quantum.Entanglement.FourMUBBoundEntanglementRefutation

/-! The full-support stabilizer standard form in Section V.C of Tarabunga et al.,
arXiv:2411.05766v1, specialized to k = N and R = I. The conjecture following (69)
asserts the Shannon inequality below. Entropy is measured in nats. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation

open D5.S3.Entropy.MaxEntropy (shannonEntropy)

/-- Computational basis strings, with one binary coordinate for each qubit. -/
abbrev Bits (n : ℕ) := Fin n → ZMod 2

/-- The off-diagonal part of the source's upper-triangular matrix. -/
def IsStrictUpper {n : ℕ} (q : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ i j, ¬ i < j → q i j = 0

/-- The source stabilizer amplitude, with the source's binary quadratic exponent
represented by Mathlib's `Matrix.toQuadraticForm'`. The exponent cᵀx of i is the
integer sum of products of the representatives 0 and 1, rather than a binary-field sum. -/
def stabAmp {n : ℕ} (q : Matrix (Fin n) (Fin n) (ZMod 2)) (c : Bits n) (x : Bits n) : ℂ :=
  ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * (-1) ^ (Matrix.toQuadraticForm' q x).val *
    Complex.I ^ (∑ i, (c i).val * (x i).val)

/-- The source distribution p at k = N, R = I, indexed by the source's diagonal matrices,
represented by Mathlib's `Matrix.diagonal`. -/
def overlapProb {n : ℕ} (q : Matrix (Fin n) (Fin n) (ZMod 2)) (c : Bits n)
    (ψ : Bits n → ℂ) (d : Bits n) : ℝ :=
  Complex.normSq (∑ x, star (stabAmp (Matrix.diagonal d + q) c x) * ψ x)

/-- The source distribution q at R = I, after taking absolute amplitudes, using the
source's diagonal matrices represented by Mathlib's `Matrix.diagonal`. -/
def absProb {n : ℕ} (ψ : Bits n → ℂ) (d : Bits n) : ℝ :=
  Complex.normSq (∑ x, star (stabAmp (Matrix.diagonal d) 0 x) * (‖ψ x‖ : ℂ))

/-- The Shannon branch-and-bound lower-bound conjecture, restricted to k = N, R = I. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ψ : Bits n → ℂ, (∑ x, Complex.normSq (ψ x)) = 1 →
    ∀ (q : Matrix (Fin n) (Fin n) (ZMod 2)) (c : Bits n), IsStrictUpper q →
      shannonEntropy (absProb ψ) ≤ shannonEntropy (overlapProb q c ψ)

/-- Coordinate 0 is most significant: the values in order 000,…,111 are
(1,0,2,-1,1,0,0,1). -/
private def coeff (x : Bits 3) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then (if x 2 = 0 then 1 else 0) else (if x 2 = 0 then 2 else -1)
  else
    if x 1 = 0 then (if x 2 = 0 then 1 else 0) else (if x 2 = 0 then 0 else 1)

private def witness (x : Bits 3) : ℂ := (coeff x : ℂ) / (Real.sqrt 8 : ℂ)

private lemma sum_bits {α : Type*} [AddCommMonoid α] (f : Bits 3 → α) :
    (∑ x, f x) = f ![0, 0, 0] + f ![0, 0, 1] + f ![0, 1, 0] + f ![0, 1, 1] +
      f ![1, 0, 0] + f ![1, 0, 1] + f ![1, 1, 0] + f ![1, 1, 1] := by
  classical
  have hu : (Finset.univ : Finset (Bits 3)) =
      {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1],
        ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]} := by decide
  simp [hu, add_assoc]

private lemma witness_unit : (∑ x, Complex.normSq (witness x)) = 1 := by
  rw [sum_bits]
  delta witness coeff
  norm_num [Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

private lemma overlap_term (d x : Bits 3) :
    star (stabAmp (Matrix.diagonal d) 0 x) * witness x =
      (-1 : ℂ) ^ (Matrix.toQuadraticForm' (Matrix.diagonal d) x).val * (coeff x : ℂ) / 8 := by
  calc
    _ = (((Real.sqrt 8)⁻¹ * (Real.sqrt 8)⁻¹ : ℝ) : ℂ) *
        ((-1 : ℂ) ^ (Matrix.toQuadraticForm' (Matrix.diagonal d) x).val * (coeff x : ℂ)) := by
      delta stabAmp witness
      simp
      ring_nf
    _ = _ := by
      rw [← pow_two,
        D5.S3.Quantum.Entanglement.FourMUBBoundEntanglementRefutation.scale_sq]
      push_cast
      ring

private lemma abs_term (d x : Bits 3) :
    star (stabAmp (Matrix.diagonal d) 0 x) * (‖witness x‖ : ℂ) =
      (-1 : ℂ) ^ (Matrix.toQuadraticForm' (Matrix.diagonal d) x).val * ((|coeff x| : ℝ) : ℂ) / 8 := by
  calc
    _ = (((Real.sqrt 8)⁻¹ * (Real.sqrt 8)⁻¹ : ℝ) : ℂ) *
        ((-1 : ℂ) ^ (Matrix.toQuadraticForm' (Matrix.diagonal d) x).val * ((|coeff x| : ℝ) : ℂ)) := by
      delta stabAmp witness
      simp [abs_of_nonneg (Real.sqrt_nonneg 8)]
      ring_nf
    _ = _ := by
      rw [← pow_two,
        D5.S3.Quantum.Entanglement.FourMUBBoundEntanglementRefutation.scale_sq]
      push_cast
      ring

private lemma overlap_distribution (d : Bits 3) :
    overlapProb 0 0 witness d =
      if d 0 = 0 then (if d 1 = 0 then 1 / 4 else 0)
      else (if d 2 = 0 then 0 else 1 / 4) := by
  delta overlapProb
  simp only [add_zero, overlap_term, ← Finset.sum_div]
  rcases (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
      ∀ a : ZMod 2, a = 0 ∨ a = 1) (d 0) with h0 | h0 <;>
    rcases (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
      ∀ a : ZMod 2, a = 0 ∨ a = 1) (d 1) with h1 | h1 <;>
    rcases (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
      ∀ a : ZMod 2, a = 0 ∨ a = 1) (d 2) with h2 | h2 <;>
    delta coeff <;>
    norm_num [sum_bits, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec,
      h0, h1, h2, ZMod.val_add, ZMod.val_mul, ZMod.val_one_eq_one_mod,
      Complex.normSq_apply]

private lemma abs_distribution (d : Bits 3) :
    absProb witness d =
      if d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 0 then 9 / 16 else 1 / 16 := by
  delta absProb
  simp only [abs_term, ← Finset.sum_div]
  rcases (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
      ∀ a : ZMod 2, a = 0 ∨ a = 1) (d 0) with h0 | h0 <;>
    rcases (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
      ∀ a : ZMod 2, a = 0 ∨ a = 1) (d 1) with h1 | h1 <;>
    rcases (Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩ :
      ∀ a : ZMod 2, a = 0 ∨ a = 1) (d 2) with h2 | h2 <;>
    delta coeff <;>
    norm_num [sum_bits, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec,
      h0, h1, h2, ZMod.val_add, ZMod.val_mul, ZMod.val_one_eq_one_mod,
      Complex.normSq_apply]

private lemma overlap_entropy :
    shannonEntropy (overlapProb 0 0 witness) = 2 * Real.log 2 := by
  rw [shannonEntropy, sum_bits]
  simp only [overlap_distribution]
  norm_num [Real.negMulLog_def, Real.log_div]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  ring

private lemma abs_entropy :
    shannonEntropy (absProb witness) = 4 * Real.log 2 - (9 / 8) * Real.log 3 := by
  rw [shannonEntropy, sum_bits]
  simp only [abs_distribution]
  norm_num [Real.negMulLog_def, Real.log_div]
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, show (16 : ℝ) = 2 ^ 4 by norm_num]
  simp only [Real.log_pow]
  ring

private lemma log_gap : 9 * Real.log 3 < 16 * Real.log 2 := by
  have h := D5.S3.Entropy.TwoDeletionRunEntropyBounds.logb_three_bounds.2
  rw [Real.logb] at h
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 := (div_lt_iff₀ h2).mp h
  linarith

/-- The certified three-qubit counterexample to the source's Shannon conjecture. -/
theorem result : ¬ claim := by
  intro h
  have hb := h 3 (by decide) witness witness_unit 0 0 (by
    intro i j hij
    rfl)
  rw [abs_entropy, overlap_entropy] at hb
  linarith [log_gap]

end D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
