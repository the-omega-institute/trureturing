/- GID: D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.claim; result=D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.result; claim=D5/S3/Quantum/Fermionic/WuUnequalTemperatureCoherence.claim
   digest: A physical unequal-temperature CAR state strictly exceeds both single-mode gains. -/

import D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Rev
import OmegaBuild.Commands

/-!
# Unequal-temperature rank-one coherence for two CAR modes

The common cap is `8 * log 2`, the mode parameters are `4 * log 2` and
`8 * log 2`, and the source exponent is two. In the hole basis ordered
empty, first, second, both, the second lowering matrix has a negative
edge from both holes to the first hole. The rank-one state below exceeds
both single-mode optima at these parameters, ruling out a best-single-mode
extension of the equal-temperature formula.
-/

compile_only_with_mathlib

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Kronecker Matrix

namespace D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence

open D5.S3.Quantum.Semigroups.TwistedTwoModeOUComparison (modeJump)

private abbrev occupationToHole : Fin 2 × Fin 2 ≃ Fin 4 :=
  (Equiv.prodCongr Fin.revPerm Fin.revPerm).trans
    ((Equiv.prodComm (Fin 2) (Fin 2)).trans finProdFinEquiv)

private theorem occupationOf_empty : occupationToHole.symm 0 = (1, 1) := rfl
private theorem occupationOf_first : occupationToHole.symm 1 = (0, 1) := rfl
private theorem occupationOf_second : occupationToHole.symm 2 = (1, 0) := rfl
private theorem occupationOf_both : occupationToHole.symm 3 = (0, 0) := rfl

/-- Particle creation, expressed as hole lowering in empty, first, second, both order. -/
def jump (i : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  reindex occupationToHole occupationToHole ((modeJump i)ᴴ)

private theorem jump_zero :
    jump 0 = !![0, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 0, 0, 0, 0] := by
  change reindex occupationToHole occupationToHole
    (((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ 1)ᴴ) = _
  apply Matrix.ext
  intro i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, occupationOf_empty, occupationOf_first,
      occupationOf_second, occupationOf_both] <;>
    norm_num [Matrix.kroneckerMap_apply, Matrix.one_apply, Complex.star_def]

private theorem jump_one :
    jump 1 = !![0, 0, 1, 0; 0, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0] := by
  change reindex occupationToHole occupationToHole
    ((diagonal (![-1, 1] : Fin 2 → ℂ) ⊗ₖ
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) = _
  apply Matrix.ext
  intro i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, occupationOf_empty, occupationOf_first,
      occupationOf_second, occupationOf_both] <;>
    norm_num [Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Complex.star_def]

/-- The two signed lowering matrices satisfy the canonical anticommutation relations. -/
theorem car (i j : Fin 2) :
    jump i * jump j + jump j * jump i = 0 ∧
      jump i * (jump j)ᴴ + (jump j)ᴴ * jump i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> constructor <;> ext a b <;>
    fin_cases a <;> fin_cases b <;>
    norm_num [jump_zero, jump_one, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.vecMul, dotProduct]

/-- The expectation of the actual matrix in the rank-one vector state. -/
def moment (x : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  (A * vecMulVec x (star x)).trace

private theorem moment_eq (x : Fin 4 → ℂ) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    moment x A = star x ⬝ᵥ (A *ᵥ x) := by
  rw [moment, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

def normalized (x : Fin 4 → ℂ) : Prop := ∑ i, Complex.normSq (x i) = 1

/-- The hole probability, using the initial projection of the hole lowering map. -/
def q (i : Fin 2) (x : Fin 4 → ℂ) : ℝ := (moment x ((jump i)ᴴ * jump i)).re

/-- Hole lowering conjugates the occupation-lowering expectation and preserves its modulus. -/
def z (i : Fin 2) (x : Fin 4 → ℂ) : ℂ := moment x (jump i)

private theorem q_zero (x : Fin 4 → ℂ) :
    q 0 x = Complex.normSq (x 1) + Complex.normSq (x 3) := by
  norm_num [q, moment_eq, jump_zero, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, Matrix.conjTranspose_apply, Pi.star_apply,
    Complex.star_def, Complex.mul_re, Complex.normSq_apply]

private theorem q_one (x : Fin 4 → ℂ) :
    q 1 x = Complex.normSq (x 2) + Complex.normSq (x 3) := by
  norm_num [q, moment_eq, jump_one, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, Matrix.conjTranspose_apply, Pi.star_apply,
    Complex.star_def, Complex.mul_re, Complex.normSq_apply]

private theorem z_zero (x : Fin 4 → ℂ) :
    z 0 x = star (x 0) * x 1 + star (x 2) * x 3 := by
  norm_num [z, moment_eq, jump_zero, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.star_apply]

private theorem z_one (x : Fin 4 → ℂ) :
    z 1 x = star (x 0) * x 2 - star (x 1) * x 3 := by
  norm_num [z, moment_eq, jump_one, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Pi.star_apply]
  ring

def beta : ℝ := 8 * Real.log 2

def modeBeta (i : Fin 2) : ℝ := ![4 * Real.log 2, beta] i

/-- The common source cap coefficient at exponent two. -/
def capCoefficient : ℝ :=
  (Real.cosh (beta / 2) - 1) / (beta * Real.sinh (beta / 2))

def c (i : Fin 2) : ℝ := (Real.cosh (modeBeta i / 2))⁻¹

def d (i : Fin 2) : ℝ := Real.tanh (modeBeta i / 2) - capCoefficient * modeBeta i

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem coefficients :
    c 0 = 8 / 17 ∧ c 1 = 32 / 257 ∧ d 0 = 15 / 34 ∧ d 1 = 480 / 4369 := by
  have h₄ : (4 * Real.log 2) / 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    ring
  have h₁₆ : beta / 2 = Real.log 16 := by
    rw [beta, show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hcap : capCoefficient = (15 / 17) / (8 * Real.log 2) := by
    have h16pos : (0 : ℝ) < 16 := by norm_num
    rw [capCoefficient, h₁₆, Real.cosh_log h16pos, Real.sinh_log h16pos, beta]
    field_simp [log_two_pos.ne']
    ring
  have hmode₀ : modeBeta 0 = 4 * Real.log 2 := rfl
  have hmode₁ : modeBeta 1 = beta := rfl
  simp only [c, d, hmode₀, hmode₁, h₄, h₁₆, hcap]
  rw [beta]
  simp only [Real.tanh_eq_sinh_div_cosh, Real.cosh_log (by norm_num : (0 : ℝ) < 4),
    Real.sinh_log (by norm_num : (0 : ℝ) < 4), Real.cosh_log (by norm_num : (0 : ℝ) < 16),
    Real.sinh_log (by norm_num : (0 : ℝ) < 16)]
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;>
    field_simp [log_two_pos.ne'] <;> ring

def modeGain (i : Fin 2) (x : Fin 4 → ℂ) : ℝ :=
  c i * Complex.normSq (z i x) - d i * q i x

def gain (x : Fin 4 → ℂ) : ℝ := modeGain 0 x + modeGain 1 x

/-- The actual complex unit vector, in empty, first, second, both order. -/
def witness (i : Fin 4) : ℂ := ((![60, 9, 10, 1] i / Real.sqrt 3782 : ℝ) : ℂ)

private theorem normalized_amplitude_mul (a b : ℝ) :
    a / Real.sqrt 3782 * (b / Real.sqrt 3782) = a * b / 3782 := by
  rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt (by norm_num)]

private theorem witness_unit : normalized witness := by
  norm_num [-Complex.ofReal_div, normalized, Fin.sum_univ_four, witness, Complex.normSq_ofReal,
    normalized_amplitude_mul]

private theorem witness_moments :
    q 0 witness = 82 / 3782 ∧ q 1 witness = 101 / 3782 ∧
      z 0 witness = ((550 / 3782 : ℝ) : ℂ) ∧
      z 1 witness = ((591 / 3782 : ℝ) : ℂ) := by
  rw [q_zero, q_one, z_zero, z_one]
  refine ⟨?_, ?_, Complex.ext ?_ ?_, Complex.ext ?_ ?_⟩
  all_goals
    simp only [witness, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Complex.normSq_ofReal,
      Complex.star_def, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      normalized_amplitude_mul]
    norm_num

private theorem witness_gain : gain witness = 15416747 / 31246048178 := by
  obtain ⟨hc₀, hc₁, hd₀, hd₁⟩ := coefficients
  obtain ⟨hq₀, hq₁, hz₀, hz₁⟩ := witness_moments
  norm_num [-Complex.ofReal_div, gain, modeGain, hc₀, hc₁, hd₀, hd₁, hq₀, hq₁, hz₀, hz₁]

private theorem pair_bound (a b u v : ℂ) :
    Complex.normSq (star a * u + star b * v) ≤
      (Complex.normSq a + Complex.normSq b) * (Complex.normSq u + Complex.normSq v) := by
  have h :
      Complex.normSq (star a * u + star b * v) + Complex.normSq (a * v - b * u) =
        (Complex.normSq a + Complex.normSq b) * (Complex.normSq u + Complex.normSq v) := by
    simp only [Complex.normSq_apply, Complex.star_def, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im]
    ring
  linarith only [h, Complex.normSq_nonneg (a * v - b * u)]

private theorem coherence_bound (i : Fin 2) (x : Fin 4 → ℂ) (hx : normalized x) :
    Complex.normSq (z i x) ≤ q i x * (1 - q i x) := by
  simp only [normalized, Fin.sum_univ_four] at hx
  fin_cases i
  · change Complex.normSq (z 0 x) ≤ q 0 x * (1 - q 0 x)
    rw [z_zero, q_zero]
    have he : 1 - (Complex.normSq (x 1) + Complex.normSq (x 3)) =
        Complex.normSq (x 0) + Complex.normSq (x 2) := by linarith only [hx]
    rw [he]
    simpa only [mul_comm (Complex.normSq (x 1) + Complex.normSq (x 3))] using
      pair_bound (x 0) (x 2) (x 1) (x 3)
  · change Complex.normSq (z 1 x) ≤ q 1 x * (1 - q 1 x)
    rw [z_one, q_one]
    have he : 1 - (Complex.normSq (x 2) + Complex.normSq (x 3)) =
        Complex.normSq (x 0) + Complex.normSq (x 1) := by linarith only [hx]
    rw [he]
    simpa only [sub_eq_add_neg, mul_neg, Complex.normSq_neg,
      mul_comm (Complex.normSq (x 2) + Complex.normSq (x 3))] using
      pair_bound (x 0) (x 1) (x 2) (-x 3)

private def axisOptimum (i : Fin 2) : ℝ := (c i - d i) ^ 2 / (4 * c i)

private theorem axis_values :
    axisOptimum 0 = 1 / 2176 ∧ axisOptimum 1 = 32 / 74273 := by
  obtain ⟨hc₀, hc₁, hd₀, hd₁⟩ := coefficients
  norm_num [axisOptimum, hc₀, hc₁, hd₀, hd₁]

private theorem axis_optimal (i : Fin 2) :
    IsGreatest {g | ∃ x, normalized x ∧ modeGain i x = g} (axisOptimum i) := by
  obtain ⟨hc₀, hc₁, hd₀, hd₁⟩ := coefficients
  have hc : 0 < c i := by fin_cases i <;> norm_num [hc₀, hc₁]
  let p := (c i - d i) / (2 * c i)
  have hp : 0 ≤ p := by fin_cases i <;> norm_num [p, hc₀, hc₁, hd₀, hd₁]
  have hp₁ : 0 ≤ 1 - p := by fin_cases i <;> norm_num [p, hc₀, hc₁, hd₀, hd₁]
  have complete_square (r : ℝ) :
      c i * (r * (1 - r)) - d i * r = axisOptimum i - c i * (r - p) ^ 2 := by
    dsimp [p, axisOptimum]
    field_simp [hc.ne']
    ring
  constructor
  · let a : ℂ := (Real.sqrt (1 - p) : ℝ)
    let b : ℂ := (Real.sqrt p : ℝ)
    let x : Fin 4 → ℂ := if i = 0 then ![a, b, 0, 0] else ![a, 0, b, 0]
    have ha : Complex.normSq a = 1 - p := by
      simp [a, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hp₁]
    have hb : Complex.normSq b = p := by
      simp [b, Complex.normSq_ofReal, ← pow_two, Real.sq_sqrt hp]
    refine ⟨x, ?_, ?_⟩
    · fin_cases i <;> simp [normalized, Fin.sum_univ_four, x, ha, hb]
    · have hq : q i x = p := by
        fin_cases i <;> simp [x, q_zero, q_one, hb]
      have hz : z i x = star a * b := by
        fin_cases i <;> simp [x, z_zero, z_one]
      rw [modeGain, hq, hz, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, ha, hb,
        mul_comm (1 - p) p, complete_square, sub_self, zero_pow (by decide : 2 ≠ 0),
        mul_zero, sub_zero]
  · rintro _ ⟨x, hx, rfl⟩
    calc
      modeGain i x ≤ c i * (q i x * (1 - q i x)) - d i * q i x :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left (coherence_bound i x hx) hc.le) _
      _ = axisOptimum i - c i * (q i x - p) ^ 2 := complete_square _
      _ ≤ axisOptimum i := sub_le_self _ (mul_nonneg hc.le (sq_nonneg _))

/-- The physical certificate and the exact optima of the two single-mode problems. -/
theorem physical_certificate :
    0 < modeBeta 0 ∧ modeBeta 0 < modeBeta 1 ∧ modeBeta 1 = beta ∧
    (c 0 = 8 / 17 ∧ c 1 = 32 / 257 ∧ d 0 = 15 / 34 ∧ d 1 = 480 / 4369) ∧
    normalized witness ∧
    q 0 witness = 82 / 3782 ∧ q 1 witness = 101 / 3782 ∧
    z 0 witness = ((550 / 3782 : ℝ) : ℂ) ∧ z 1 witness = ((591 / 3782 : ℝ) : ℂ) ∧
    gain witness = 15416747 / 31246048178 ∧
    (49 / 100000 : ℝ) < gain witness ∧
    IsGreatest {g | ∃ x, normalized x ∧ modeGain 0 x = g} (1 / 2176) ∧
    IsGreatest {g | ∃ x, normalized x ∧ modeGain 1 x = g} (32 / 74273) := by
  obtain ⟨hq₀, hq₁, hz₀, hz₁⟩ := witness_moments
  refine ⟨?_, ?_, rfl, coefficients, witness_unit, hq₀, hq₁, hz₀, hz₁, witness_gain, ?_, ?_, ?_⟩
  · change 0 < 4 * Real.log 2
    linarith only [log_two_pos]
  · change 4 * Real.log 2 < 8 * Real.log 2
    linarith only [log_two_pos]
  · rw [witness_gain]
    norm_num
  · simpa only [axis_values.1] using axis_optimal 0
  · simpa only [axis_values.2] using axis_optimal 1

/-- The proposed extension in which every gain is dominated by a single mode. -/
def claim : Prop :=
  ∀ x, normalized x → ∃ i y, normalized y ∧ gain x ≤ modeGain i y

theorem result : ¬ claim := by
  intro h
  obtain ⟨_, _, _, _, hx, _, _, _, _, _, hgain, h₀, h₁⟩ := physical_certificate
  obtain ⟨i, y, hy, hxy⟩ := h witness hx
  have hy' : modeGain i y < (49 / 100000 : ℝ) := by
    fin_cases i
    · exact (h₀.2 ⟨y, hy, rfl⟩).trans_lt (by norm_num)
    · exact (h₁.2 ⟨y, hy, rfl⟩).trans_lt (by norm_num)
  exact (not_lt_of_ge hxy) (hy'.trans hgain)

#print axioms car
#print axioms physical_certificate
#print axioms result

end D5.S3.Quantum.Fermionic.WuUnequalTemperatureCoherence
