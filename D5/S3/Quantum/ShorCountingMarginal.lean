/- GID: D5/S3/Quantum/ShorCountingMarginal
   generality: G
   mirror-B: D5/B/S3/Quantum/ShorCountingMarginal
   mirror-E: none(waiver:analytic-finite-register-proof)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds]
   utility: none
   digest: Actual padded modular-input counting marginal and pointwise lower bound. -/

/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license; the complete license is retained in
Library/HilbertOperators/aicyberg2026shor.md. Authors: aicyberg.
Source: solanaqubits/leanbook, commit 9b742770a2a5dbcf30cf9abc44e711194e957a00.
The live proof slice preserves the supplier's statements and proofs, with canonical
imports and source grouping for the receiving Lean and Mathlib pins.
Retire this transplant when the receiving pinned Mathlib supplies equivalent
actual-input execution, marginal, normalization and circular nearest-grid results;
replace the equivalent slice with direct imports at that repository pin.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

noncomputable section
namespace QuantumPhaseEstimationGeneral
open scoped BigOperators ComplexConjugate

/-- A phase measured in turns, with period one. -/
def phase (t : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * t : ℝ))

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]
theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]
@[simp] theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]
theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  rw [phase, ← Complex.exp_conj]
  simp [phase, map_ofNat]
theorem phase_nat_mul (t : ℝ) (k : ℕ) : phase (k * t) = phase t ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, phase_add, ih, pow_succ]
@[simp] theorem phase_int (z : ℤ) : phase z = 1 := by
  unfold phase
  rw [show Complex.I * ((2 * Real.pi * (z : ℝ) : ℝ) : ℂ) =
    (z : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

theorem phase_eq_one_iff (t : ℝ) : phase t = 1 ↔ ∃ z : ℤ, t = z := by
  rw [phase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨z, h⟩
    have hi := congrArg Complex.im h
    simp at hi
    refine ⟨z, ?_⟩
    nlinarith [Real.pi_pos]
  · rintro ⟨z, rfl⟩
    exact ⟨z, by push_cast; ring⟩

def amplitude (N : ℕ) (θ : ℝ) (y : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N, phase (k.val * (θ - y.val / N))
def probability (N : ℕ) (θ : ℝ) (y : Fin N) : ℝ := ‖amplitude N θ y‖ ^ 2

theorem phase_sum_geometric (N : ℕ) (δ : ℝ) (hδ : phase δ ≠ 1) :
    (∑ k : Fin N, phase (k.val * δ)) = (phase (N * δ) - 1) / (phase δ - 1) := by
  simp_rw [phase_nat_mul]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hδ]

theorem phase_sub_one_norm (t : ℝ) : ‖phase t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  rw [phase, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * t / 2 = Real.pi * t by ring]
  simp

theorem qpe_geometric_sum_closed_form (N : ℕ) (_hN : 0 < N) (θ : ℝ) (y : Fin N)
    (hδ : ¬ ∃ z : ℤ, θ - y.val / N = z) :
    ‖amplitude N θ y‖ = |Real.sin (Real.pi * N * (θ - y.val / N))| /
      (N * |Real.sin (Real.pi * (θ - y.val / N))|) := by
  have hp : phase (θ - y.val / N) ≠ 1 := mt (phase_eq_one_iff _).mp hδ
  rw [amplitude, phase_sum_geometric _ _ hp, norm_mul, norm_inv, norm_div,
    phase_sub_one_norm, phase_sub_one_norm]
  simp only [Complex.norm_natCast, mul_assoc]
  ring

theorem phase_shift_int (t : ℝ) (z : ℤ) : phase (t + z) = phase t := by
  rw [phase_add, phase_int, mul_one]

theorem amplitude_of_integral (N : ℕ) (hN : 0 < N) (θ : ℝ) (y : Fin N)
    (h : phase (θ - y.val / N) = 1) : amplitude N θ y = 1 := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [amplitude, phase_nat_mul, h, hn]

theorem amplitude_periodic (N : ℕ) (θ : ℝ) (y : Fin N) (z : ℤ) :
    amplitude N (θ + z) y = amplitude N θ y := by
  unfold amplitude
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h : (k.val : ℝ) * (θ + z - y.val / N) =
      k.val * (θ - y.val / N) + ((k.val : ℤ) * z : ℤ) := by push_cast; ring
  rw [h, phase_shift_int]

/-- A representative of the distance on the circle, including either midpoint tie. -/
def Nearest (N : ℕ) (θ : ℝ) (b : Fin N) : Prop :=
  ∃ z : ℤ, |θ - b.val / N - z| ≤ 1 / (2 * N)

theorem amplitude_lower_bound_local (N : ℕ) (hN : 0 < N) (θ : ℝ) (b : Fin N)
    (hnear : |θ - b.val / N| ≤ 1 / (2 * N)) :
    2 / Real.pi ≤ ‖amplitude N θ b‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := Real.pi_pos
  by_cases h : phase (θ - b.val / N) = 1
  · rw [amplitude_of_integral N hN θ b h, norm_one]
    exact (div_le_one hp).2 Real.two_le_pi
  · have hc := qpe_geometric_sum_closed_form N hN θ b
      (mt (phase_eq_one_iff _).mpr h)
    rw [hc]
    have hs : 0 < |Real.sin (Real.pi * (θ - b.val / N))| := by
      have hz := norm_pos_iff.mpr (sub_ne_zero.mpr h)
      rw [phase_sub_one_norm] at hz
      linarith
    have habs : (N : ℝ) * |θ - b.val / N| ≤ 1 / 2 := by
      have := (le_div_iff₀ (show (0 : ℝ) < 2 * N by positivity)).1 hnear
      nlinarith
    have hj := Real.mul_abs_le_abs_sin (x := Real.pi * N * (θ - b.val / N))
      (by rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hn]; nlinarith)
    have hu := Real.abs_sin_le_abs (x := Real.pi * (θ - b.val / N))
    rw [abs_mul, abs_of_pos hp] at hu
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hn] at hj
    apply (le_div_iff₀ (mul_pos hn hs)).2
    calc
      2 / Real.pi * (N * |Real.sin (Real.pi * (θ - b.val / N))|) ≤
          2 / Real.pi * (N * (Real.pi * |θ - b.val / N|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hn.le) (by positivity)
      _ = 2 / Real.pi * (Real.pi * N * |θ - b.val / N|) := by ring
      _ ≤ _ := hj

theorem qpe_arbitrary_phase_lower_bound (N : ℕ) (hN : 0 < N) (θ : ℝ) (b : Fin N)
    (hnear : Nearest N θ b) : 4 / Real.pi ^ 2 ≤ probability N θ b := by
  obtain ⟨z, hz⟩ := hnear
  have hl := amplitude_lower_bound_local N hN (θ - z) b
    (by simpa only [sub_right_comm] using hz)
  have he : amplitude N (θ - z) b = amplitude N θ b := by
    have := amplitude_periodic N (θ - z) b z
    simpa using this.symm
  rw [he] at hl
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hl
  unfold probability
  have heq : (4 : ℝ) / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by ring
  rw [heq]
  nlinarith

theorem phase_fraction_ne_one {N : ℕ} (hN : 0 < N) (x y : Fin N) (hxy : x ≠ y) :
    phase ((x.val - y.val : ℝ) / N) ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := (phase_eq_one_iff _).mp h
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (x.val : ℝ) < N := by exact_mod_cast x.isLt
  have hy : (y.val : ℝ) < N := by exact_mod_cast y.isLt
  have hx0 : (0 : ℝ) ≤ x.val := by positivity
  have hy0 : (0 : ℝ) ≤ y.val := by positivity
  have hm := (div_eq_iff hn.ne').mp hz
  have hzlo : (-1 : ℤ) < z := by exact_mod_cast (show (-1 : ℝ) < z by nlinarith)
  have hzhi : z < (1 : ℤ) := by exact_mod_cast (show (z : ℝ) < 1 by nlinarith)
  have hz0 : z = 0 := by omega
  subst z
  have he : (x.val : ℝ) = (y.val : ℝ) := sub_eq_zero.mp (by simpa using hm)
  exact hxy (Fin.ext (by exact_mod_cast he))

theorem phase_orthogonality {N : ℕ} (hN : 0 < N) (x y : Fin N) :
    (∑ k : Fin N, phase (k.val * ((x.val - y.val : ℝ) / N))) =
      if x = y then (N : ℂ) else 0 := by
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, phase_sum_geometric _ _ (phase_fraction_ne_one hN x y hxy)]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show (N : ℝ) * ((x.val - y.val : ℝ) / N) = x.val - y.val by field_simp]
    have hi : phase (x.val - y.val : ℝ) = 1 := by
      exact_mod_cast phase_int ((x.val : ℤ) - y.val)
    rw [hi, sub_self, zero_div]

def scale (N : ℕ) : ℂ := (Real.sqrt N : ℂ)⁻¹
def kernel (N : ℕ) (j k : Fin N) : ℂ := phase (j.val * k.val / N)
def QFT (N : ℕ) (v : Fin N → ℂ) (j : Fin N) : ℂ :=
  scale N * ∑ k, kernel N j k * v k
def inverseQFT (N : ℕ) (v : Fin N → ℂ) (j : Fin N) : ℂ :=
  scale N * ∑ k, conj (kernel N j k) * v k

theorem scale_sq {N : ℕ} (_hN : 0 < N) : scale N * scale N = (N : ℂ)⁻¹ := by
  have h : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = N := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg N)
  rw [scale, ← mul_inv, h]
@[simp] theorem scale_conj (N : ℕ) : conj (scale N) = scale N := by simp [scale]

theorem kernel_symm (N : ℕ) (j k : Fin N) : kernel N j k = kernel N k j := by
  unfold kernel; rw [mul_comm (j.val : ℝ)]

theorem kernel_orthogonality {N : ℕ} (hN : 0 < N) (x y : Fin N) :
    (∑ k, conj (kernel N k y) * kernel N k x) = if x = y then (N : ℂ) else 0 := by
  convert phase_orthogonality hN x y using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [kernel, kernel, phase_conj, ← phase_add]
  congr 1
  ring

theorem inverse_qft_qft {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    inverseQFT N (QFT N v) = v := by
  funext j
  simp only [inverseQFT, QFT]
  calc
    _ = (scale N * scale N) * ∑ k, (∑ a, conj (kernel N a j) * kernel N a k) * v k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      rw [kernel_symm N j a]
      ring
    _ = v j := by
      rw [scale_sq hN]
      simp [kernel_orthogonality hN, hN.ne']

theorem qft_inverse_qft {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    QFT N (inverseQFT N v) = v := by
  have hi := congrArg (fun u j => conj (u j)) (inverse_qft_qft hN (fun j => conj (v j)))
  funext j
  simpa [QFT, inverseQFT, map_sum] using congrFun hi j

def hermitian {N : ℕ} (u v : Fin N → ℂ) : ℂ := ∑ j, conj (u j) * v j
def normSquared {N : ℕ} (v : Fin N → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

theorem fourier_adjoint {N : ℕ} (u v : Fin N → ℂ) :
    hermitian (QFT N u) v = hermitian u (inverseQFT N v) := by
  simp only [hermitian, QFT, inverseQFT, map_mul, map_sum, scale_conj,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [kernel_symm N k j]
  ring

theorem inverse_qft_unitarity {N : ℕ} (hN : 0 < N) (u v : Fin N → ℂ) :
    hermitian (inverseQFT N u) (inverseQFT N v) = hermitian u v := by
  rw [← fourier_adjoint, qft_inverse_qft hN]

theorem hermitian_self {N : ℕ} (v : Fin N → ℂ) :
    hermitian v v = (normSquared v : ℂ) := by
  simp only [hermitian, normSquared, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, Complex.mul_conj]

theorem inverse_qft_norm {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    normSquared (inverseQFT N v) = normSquared v := by
  have h := inverse_qft_unitarity hN v v
  rw [hermitian_self, hermitian_self] at h
  exact_mod_cast h

def preState (N : ℕ) (θ : ℝ) (k : Fin N) : ℂ := scale N * phase (k.val * θ)

theorem inverse_pre_amplitude {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    inverseQFT N (preState N θ) = amplitude N θ := by
  funext y
  unfold inverseQFT preState amplitude
  rw [← scale_sq hN]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : conj (kernel N y k) * phase (k.val * θ) =
      phase (k.val * (θ - y.val / N)) := by
    rw [kernel, phase_conj, ← phase_add]
    congr 1
    ring
  calc
    _ = (scale N * scale N) * (conj (kernel N y k) * phase (k.val * θ)) := by ring
    _ = _ := by rw [hk]

theorem pre_state_normalized {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    normSquared (preState N θ) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : Complex.normSq (scale N) = (N : ℝ)⁻¹ := by
    have h := congrArg norm (scale_sq hN)
    simp only [norm_mul, norm_inv, Complex.norm_natCast] at h
    rw [Complex.normSq_eq_norm_sq, pow_two]
    exact h
  simp [normSquared, preState, Complex.normSq_eq_norm_sq,
    phase_norm, ← Complex.normSq_eq_norm_sq (scale N), hs, hn]

theorem qpe_probability_normalized {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    (∑ y : Fin N, probability N θ y) = 1 := by
  have h := inverse_qft_norm hN (preState N θ)
  rw [inverse_pre_amplitude hN, pre_state_normalized hN] at h
  simpa only [normSquared, Complex.normSq_eq_norm_sq, probability] using h

end QuantumPhaseEstimationGeneral

noncomputable section
namespace QuantumPhaseEstimationGeneral
open scoped BigOperators ComplexConjugate

abbrev TargetState (d : ℕ) := Fin d → ℂ
abbrev TargetOperator (d : ℕ) := TargetState d →ₗ[ℂ] TargetState d

/-- Binary control order: recurse through lower bits, then apply the high controlled power.
Each branch is linear; the high branch applies precisely U^(2^n), not a prescribed phase. -/
def controlledCascade (U : TargetOperator d) : (n : ℕ) → Fin (2 ^ n) → TargetOperator d
  | 0, _ => 1
  | n + 1, k =>
    let j : Fin (2 ^ n) := ⟨k.val % (2 ^ n), Nat.mod_lt _ (by positivity)⟩
    if k.val < 2 ^ n then controlledCascade U n j
    else U ^ (2 ^ n) * controlledCascade U n j

theorem controlled_cascade_eq_power (U : TargetOperator d) (n : ℕ) (k : Fin (2 ^ n)) :
    controlledCascade U n k = U ^ k.val := by
  induction n with
  | zero => simp [controlledCascade]
  | succ n ih =>
    have hp : 0 < 2 ^ n := by positivity
    have hk : k.val < 2 ^ n * 2 := by simpa [pow_succ] using k.isLt
    simp only [controlledCascade, ih]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [← pow_add]
      congr 1
      have hmod : k.val % (2 ^ n) = k.val - 2 ^ n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

theorem eigen_power (U : TargetOperator d) (ψ : TargetState d) (θ : ℝ)
    (hψ : U ψ = phase θ • ψ) (k : ℕ) : (U ^ k) ψ = phase (k * θ) • ψ := by
  rw [phase_nat_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hψ, smul_smul]
    rw [pow_succ]

def prepareControl (n : ℕ) (ψ : TargetState d) : Fin (2 ^ n) → TargetState d :=
  fun _ => scale (2 ^ n) • ψ

def runControlled (U : TargetOperator d) (n : ℕ) (ψ : TargetState d) :
    Fin (2 ^ n) → TargetState d :=
  fun k => controlledCascade U n k (prepareControl n ψ k)

def inverseControl (N : ℕ) (v : Fin N → TargetState d) : Fin N → TargetState d :=
  fun y t => inverseQFT N (fun k => v k t) y

def runQPE (U : TargetOperator d) (n : ℕ) (ψ : TargetState d) :
    Fin (2 ^ n) → TargetState d := inverseControl (2 ^ n) (runControlled U n ψ)

theorem controlled_powers_kickback (U : TargetOperator d) (n : ℕ) (ψ : TargetState d)
    (θ : ℝ) (hψ : U ψ = phase θ • ψ) :
    runControlled U n ψ = fun k => preState (2 ^ n) θ k • ψ := by
  funext k
  simp only [runControlled, prepareControl, controlled_cascade_eq_power, map_smul,
    eigen_power U ψ θ hψ, smul_smul, preState]

theorem inverse_on_product {N : ℕ} (v : Fin N → ℂ) (ψ : TargetState d) :
    inverseControl N (fun k => v k • ψ) = fun y => inverseQFT N v y • ψ := by
  funext y t
  simp [inverseControl, inverseQFT, Finset.sum_mul, mul_assoc]

theorem qpe_amplitude_derivation (U : TargetOperator d) (n : ℕ) (ψ : TargetState d)
    (θ : ℝ) (hψ : U ψ = phase θ • ψ) :
    runQPE U n ψ = fun y => amplitude (2 ^ n) θ y • ψ := by
  rw [runQPE, controlled_powers_kickback U n ψ θ hψ, inverse_on_product,
    inverse_pre_amplitude (by positivity)]

theorem target_norm_smul (z : ℂ) (ψ : TargetState d) :
    normSquared (z • ψ) = Complex.normSq z * normSquared ψ := by
  simp [normSquared, Complex.normSq_mul, Finset.mul_sum]


end QuantumPhaseEstimationGeneral

/-! Spectral order finding on a padded finite register. The order is a mathematical
parameter of the proof, not input supplied to the modular-multiplication circuit.
Continued fractions, repeated sampling and factorization are separate obligations. -/
noncomputable section
namespace QuantumShorOrderFindingCore
open scoped BigOperators ComplexConjugate
open QuantumPhaseEstimationGeneral

structure Parameters where
  modulus : ℕ
  modulus_ge_two : 2 ≤ modulus
  base : ℕ
  coprime : Nat.Coprime base modulus
  width : ℕ
  fits : modulus ≤ 2 ^ width

namespace Parameters
variable (c : Parameters)
instance : NeZero c.modulus := ⟨by have := c.modulus_ge_two; omega⟩
abbrev dimension := 2 ^ c.width
def period : ℕ := orderOf (c.base : ZMod c.modulus)
theorem period_pos : 0 < c.period :=
  ((ZMod.isUnit_iff_coprime _ _).2 c.coprime).isOfFinOrder.orderOf_pos
instance : NeZero c.period := ⟨c.period_pos.ne'⟩
theorem powers_distinct {k l : ℕ} (hk : k < c.period) (hl : l < c.period) :
    (c.base : ZMod c.modulus) ^ k = (c.base : ZMod c.modulus) ^ l ↔ k = l := by
  constructor
  · exact pow_injOn_Iio_orderOf hk hl
  · rintro rfl; rfl

def residuePerm : Equiv.Perm (Fin c.modulus) where
  toFun y := ⟨((c.base : ZMod c.modulus) * (y.val : ZMod c.modulus)).val, ZMod.val_lt _⟩
  invFun y := ⟨(((ZMod.unitOfCoprime c.base c.coprime)⁻¹ : (ZMod c.modulus)ˣ) *
    (y.val : ZMod c.modulus)).val, ZMod.val_lt _⟩
  left_inv y := by
    apply Fin.ext
    simp only [ZMod.natCast_zmod_val]
    rw [← ZMod.coe_unitOfCoprime c.base c.coprime, ← mul_assoc]
    rw [Units.inv_mul, one_mul, ZMod.val_natCast_of_lt y.isLt]
  right_inv y := by
    apply Fin.ext
    simp only [ZMod.natCast_zmod_val]
    rw [← ZMod.coe_unitOfCoprime c.base c.coprime, ← mul_assoc]
    rw [Units.mul_inv, one_mul, ZMod.val_natCast_of_lt y.isLt]

def residueEmbedding : Fin c.modulus ≃ {y : Fin c.dimension // y.val < c.modulus} where
  toFun y := ⟨⟨y.val, y.isLt.trans_le c.fits⟩, y.isLt⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def registerPerm : Equiv.Perm (Fin c.dimension) :=
  c.residuePerm.extendDomain c.residueEmbedding

theorem registerPerm_low (y : Fin c.dimension) (hy : y.val < c.modulus) :
    (c.registerPerm y).val = (c.base * y.val) % c.modulus := by
  rw [registerPerm,
    Equiv.Perm.extendDomain_apply_subtype c.residuePerm c.residueEmbedding (b := y) hy]
  change ((c.base : ZMod c.modulus) * (y.val : ZMod c.modulus)).val = _
  rw [← Nat.cast_mul, ZMod.val_natCast]

/-- Push forward along the actual padded modular-multiplication permutation. -/
def modularOperator : TargetOperator c.dimension where
  toFun v := fun y => v (c.registerPerm.symm y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


def orbit (k : Fin c.period) : Fin c.dimension :=
  ⟨((c.base : ZMod c.modulus) ^ k.val).val, (ZMod.val_lt _).trans_le c.fits⟩

theorem orbit_injective : Function.Injective c.orbit := by
  intro k l h
  apply Fin.ext
  apply (c.powers_distinct k.isLt l.isLt).1
  apply ZMod.val_injective c.modulus
  exact congrArg Fin.val h

/-- Cyclic successor in the orbit index. -/
def successor : Equiv.Perm (Fin c.period) := Equiv.addRight 1

theorem registerPerm_orbit (k : Fin c.period) :
    c.registerPerm (c.orbit k) = c.orbit (c.successor k) := by
  apply Fin.ext
  rw [c.registerPerm_low _ (ZMod.val_lt _)]
  rw [← ZMod.val_natCast c.modulus, Nat.cast_mul]
  simp only [orbit, ZMod.natCast_zmod_val]
  change ((c.base : ZMod c.modulus) * (c.base : ZMod c.modulus) ^ k.val).val =
    ((c.base : ZMod c.modulus) ^ (c.successor k).val).val
  congr 1
  rw [← pow_succ']
  change _ = (c.base : ZMod c.modulus) ^ (k + 1 : Fin c.period).val
  rw [Fin.val_add]
  change _ = (c.base : ZMod c.modulus) ^ ((k.val + 1 % c.period) % c.period)
  rw [Nat.add_mod_mod]
  exact (pow_mod_orderOf _ _).symm

end Parameters

variable {d r : ℕ}
/-- A computational basis vector, with no eigenstate assumption. -/
def basis (j : Fin d) : TargetState d := fun y => if y = j then 1 else 0

namespace Parameters
variable (c : Parameters)
/-- Isometric inclusion of orbit coordinates into the physical target register. -/
def orbitLift : (Fin c.period → ℂ) →ₗ[ℂ] TargetState c.dimension where
  toFun v := ∑ k, v k • basis (c.orbit k)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z v := by simp [smul_smul, Finset.smul_sum]

theorem orbitLift_apply (v : Fin c.period → ℂ) (y : Fin c.dimension) :
    c.orbitLift v y = ∑ k, v k * if y = c.orbit k then 1 else 0 := by
  simp [orbitLift, basis]

theorem orbitLift_inner (u v : Fin c.period → ℂ) :
    hermitian (c.orbitLift u) (c.orbitLift v) = hermitian u v := by
  classical
  simp only [hermitian, orbitLift_apply, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp [c.orbit_injective.eq_iff]

theorem modularOperator_basis (y : Fin c.dimension) :
    c.modularOperator (basis y) = basis (c.registerPerm y) := by
  funext z
  simp [modularOperator, basis, Equiv.symm_apply_eq]

end Parameters

/-- Fourier eigen-coordinates on the orbit, before embedding into the target. -/
def wave (r : ℕ) (s : Fin r) : Fin r → ℂ := inverseQFT r (basis s)

theorem wave_apply (r : ℕ) (s k : Fin r) :
    wave r s k = scale r * conj (kernel r k s) := by
  classical
  simp [wave, inverseQFT, basis]

/-- The orbit character is periodic; reducing an exponent does not change it. -/
theorem character_mod (hr : 0 < r) (s k : ℕ) :
    phase (-(k % r : ℕ) * (s : ℝ) / r) = phase (-(k : ℝ) * s / r) := by
  have hdiv : (k : ℝ) = (k % r : ℕ) + (r : ℝ) * (k / r : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k r).symm
  have hn : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : -(k : ℝ) * s / r = -(k % r : ℕ) * (s : ℝ) / r +
      (-((s * (k / r) : ℕ) : ℤ) : ℤ) := by
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [Nat.cast_mul]
    rw [hdiv]
    field_simp
    ring
  rw [he, phase_shift_int]

theorem wave_successor (hr : 0 < r) [NeZero r] (s k : Fin r) :
    wave r s k = phase (s.val / r) * wave r s (k + 1) := by
  rw [wave_apply, wave_apply]
  simp only [kernel, phase_conj]
  have hk : (k + 1 : Fin r).val = (k.val + 1) % r := by
    rw [Fin.val_add]
    change (k.val + 1 % r) % r = _
    rw [Nat.add_mod_mod]
  rw [hk]
  have hm := character_mod hr s.val (k.val + 1)
  simp only [neg_mul, neg_div] at hm
  rw [hm]
  rw [mul_left_comm, ← phase_add]
  congr 1
  push_cast
  congr 1
  ring

theorem wave_decomposition (hr : 0 < r) [NeZero r] :
    scale r • (∑ s : Fin r, wave r s) = basis (0 : Fin r) := by
  funext k
  have h := congrFun (inverse_qft_qft hr (basis (0 : Fin r))) k
  simpa [inverseQFT, QFT, basis, wave_apply, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm, kernel] using h

namespace Parameters
variable (c : Parameters)
def eigenstate (s : Fin c.period) : TargetState c.dimension := c.orbitLift (wave c.period s)

theorem shor_eigenstate_action (s : Fin c.period) :
    c.modularOperator (c.eigenstate s) = phase (s.val / c.period) • c.eigenstate s := by
  change c.modularOperator (∑ k, wave c.period s k • basis (c.orbit k)) = _
  rw [map_sum]
  simp_rw [map_smul, c.modularOperator_basis, c.registerPerm_orbit]
  change (∑ k, wave c.period s k • basis (c.orbit (c.successor k))) = _
  calc
    _ = ∑ k, (phase (s.val / c.period) * wave c.period s (c.successor k)) •
        basis (c.orbit (c.successor k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [wave_successor c.period_pos s k]
      rfl
    _ = _ := by
      rw [Equiv.sum_comp c.successor (fun k =>
        (phase (s.val / c.period) * wave c.period s k) • basis (c.orbit k))]
      simp [eigenstate, orbitLift, Finset.smul_sum, smul_smul]

theorem orbitLift_basis (k : Fin c.period) :
    c.orbitLift (basis k) = basis (c.orbit k) := by
  classical
  change (∑ i, (if i = k then (1 : ℂ) else 0) • basis (c.orbit i)) = _
  simp only [ite_smul, one_smul, zero_smul]
  simp

def input : TargetState c.dimension :=
  basis ⟨1, (lt_of_lt_of_le (by have := c.modulus_ge_two; omega) c.fits)⟩

theorem orbit_zero : c.orbit (0 : Fin c.period) =
    ⟨1, (lt_of_lt_of_le (by have := c.modulus_ge_two; omega) c.fits)⟩ := by
  apply Fin.ext
  simp only [orbit, Fin.val_zero, pow_zero]
  rw [ZMod.val_one_eq_one_mod]
  apply Nat.mod_eq_of_lt
  have := c.modulus_ge_two
  omega

theorem shor_input_state_decomposition :
    c.input = scale c.period • (∑ s, c.eigenstate s) := by
  have h := congrArg c.orbitLift (wave_decomposition c.period_pos)
  rw [map_smul, map_sum, c.orbitLift_basis, c.orbit_zero] at h
  exact h.symm

theorem orbitLift_norm (v : Fin c.period → ℂ) :
    normSquared (c.orbitLift v) = normSquared v := by
  have h := c.orbitLift_inner v v
  rw [hermitian_self, hermitian_self] at h
  exact_mod_cast h


end Parameters

theorem wave_synthesis (v : Fin r → ℂ) :
    (∑ s : Fin r, v s • wave r s) = inverseQFT r v := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wave_apply, inverseQFT,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Linearity in the target input of the actual circuit, at each output coordinate. -/
def qpeLinear (U : TargetOperator d) (n : ℕ) (y : Fin (2 ^ n)) : TargetOperator d where
  toFun ψ := runQPE U n ψ y
  map_add' u v := by
    funext t
    simp [runQPE, inverseControl, inverseQFT, runControlled, prepareControl,
      smul_add, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' z v := by
    funext t
    simp [runQPE, inverseControl, inverseQFT, runControlled, prepareControl,
      smul_smul, map_smul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem scale_norm_square (_hr : 0 < r) : ‖scale r‖ ^ 2 = (r : ℝ)⁻¹ := by
  simp [scale, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow,
    sq_abs, Real.sq_sqrt (Nat.cast_nonneg r)]

namespace Parameters
variable (c : Parameters)
theorem eigenstate_synthesis (v : Fin c.period → ℂ) :
    (∑ s, v s • c.eigenstate s) = c.orbitLift (inverseQFT c.period v) := by
  rw [← wave_synthesis, map_sum]
  simp [map_smul, eigenstate]

theorem eigenstate_synthesis_norm (v : Fin c.period → ℂ) :
    normSquared (∑ s, v s • c.eigenstate s) = normSquared v := by
  rw [c.eigenstate_synthesis, c.orbitLift_norm, inverse_qft_norm c.period_pos]

theorem shor_qpe_output (n : ℕ) (y : Fin (2 ^ n)) :
    runQPE c.modularOperator n c.input y = scale c.period •
      ∑ s, amplitude (2 ^ n) (s.val / c.period) y • c.eigenstate s := by
  change qpeLinear c.modularOperator n y c.input = _
  rw [c.shor_input_state_decomposition, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact congrFun (qpe_amplitude_derivation c.modularOperator n (c.eigenstate s)
    (s.val / c.period) (c.shor_eigenstate_action s)) y

theorem shor_qpe_probability_mixture (n : ℕ) (y : Fin (2 ^ n)) :
    normSquared (runQPE c.modularOperator n c.input y) =
      (c.period : ℝ)⁻¹ * ∑ s : Fin c.period, probability (2 ^ n) (s.val / c.period) y := by
  rw [c.shor_qpe_output, target_norm_smul, Complex.normSq_eq_norm_sq,
    scale_norm_square c.period_pos,
    c.eigenstate_synthesis_norm]
  simp only [normSquared, probability, Complex.normSq_eq_norm_sq]

theorem shor_phase_accuracy_bound (n : ℕ) (s : Fin c.period)
    (b : Fin (2 ^ n))
    (hb : Nearest (2 ^ n) (s.val / c.period) b) :
    4 / Real.pi ^ 2 ≤ probability (2 ^ n) (s.val / c.period) b :=
  qpe_arbitrary_phase_lower_bound _ (by positivity) _ _ hb

theorem shor_distribution_normalized (n : ℕ) :
    (∑ y : Fin (2 ^ n), normSquared (runQPE c.modularOperator n c.input y)) = 1 := by
  simp_rw [c.shor_qpe_probability_mixture]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp [qpe_probability_normalized (by positivity : 0 < 2 ^ n), c.period_pos.ne']

/-- An individual component carries weight 1/r in the actual marginal mixture. -/
theorem shor_mixture_peak_lower_bound (n : ℕ) (s : Fin c.period) (b : Fin (2 ^ n))
    (hb : Nearest (2 ^ n) (s.val / c.period) b) :
    (c.period : ℝ)⁻¹ * (4 / Real.pi ^ 2) ≤
      normSquared (runQPE c.modularOperator n c.input b) := by
  rw [c.shor_qpe_probability_mixture]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (c.shor_phase_accuracy_bound n s b hb).trans
    (Finset.single_le_sum (fun t _ => sq_nonneg ‖amplitude (2 ^ n) (t.val / c.period) b‖)
      (Finset.mem_univ s))

end Parameters
end QuantumShorOrderFindingCore
