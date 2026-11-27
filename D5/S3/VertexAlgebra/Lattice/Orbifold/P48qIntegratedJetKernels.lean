/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qIntegratedJetKernels
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integrate the diagonal jet kernels and identify the omitted axes of the sum. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qJetContractions
import Mathlib.RingTheory.PowerSeries.Log

/-!
Integrate the P48q jet kernels in the normalized diagonal variable. For a pair
of jets of degrees `d` and `e`, integration contributes `1/d` and `1/e`.
The positive-degree antidiagonal is finite, and the two omitted axes give
the two singleton primitives in the resulting logarithm identity.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedJetKernels

open P48qJetContractions (scalarKernel pairJetCoeff pairJetCoeff_closed)
open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)
open scoped BigOperators

/-- The zero-constant primitive `J_r` of the scalar current–charge kernel. -/
def integratedScalarKernel (r : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else Ring.choose (-r) n / (n : ℂ)

@[simp] theorem coeff_integratedScalarKernel (r : ℂ) (n : ℕ) :
    PowerSeries.coeff n (integratedScalarKernel r) =
      if n = 0 then 0 else Ring.choose (-r) n / (n : ℂ) :=
  PowerSeries.coeff_mk _ _

theorem derivative_integratedScalarKernel (r : ℂ) :
    PowerSeries.derivative (integratedScalarKernel r) = scalarKernel r := by
  apply PowerSeries.ext
  intro n
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  rw [PowerSeries.coeff_derivative, coeff_integratedScalarKernel,
    ite_eq_right (Nat.succ_ne_zero n), ← Nat.cast_add_one, div_mul_cancel₀ _ hn,
    scalarKernel, PowerSeries.coeff_mk]

@[simp] theorem integratedScalarKernel_zero : integratedScalarKernel 0 = 0 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp
  | succ n => simp [Ring.choose_zero_succ]

/-- The primitive for residue `1` is the negative of Mathlib's series for `log(1 + X)`. -/
theorem integratedScalarKernel_one : integratedScalarKernel 1 = -PowerSeries.log ℂ := by
  have : HasUniqueDiv ℂ := .of_module_rat ℂ
  apply PowerSeries.derivative.ext
  · rw [derivative_integratedScalarKernel, map_neg, PowerSeries.derivative_log]
    apply PowerSeries.ext
    intro n
    rw [scalarKernel, PowerSeries.coeff_mk, map_neg, PowerSeries.coeff_mk,
      Ring.choose_neg,
      show (1 : ℂ) + ((n + 1 : ℕ) : ℂ) - 1 = ((n + 1 : ℕ) : ℂ) by ring,
      Ring.choose_natCast, Nat.choose_self, Nat.cast_one, Units.smul_def, zsmul_eq_mul,
      Int.cast_negOnePow_natCast, mul_one, pow_succ, mul_neg_one]
  · rw [map_neg, PowerSeries.constantCoeff_log, neg_zero,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_integratedScalarKernel,
      ite_eq_left rfl]

/-- Integrate both positive jet levels and evaluate on the diagonal. -/
def integratedPairKernel (r : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    ∑ p ∈ antidiagonal n with 0 < p.1 ∧ 0 < p.2,
      pairJetCoeff r p.1 p.2 / ((p.1 : ℂ) * (p.2 : ℂ))

@[simp] theorem coeff_zero_integratedPairKernel (r : ℂ) :
    PowerSeries.coeff 0 (integratedPairKernel r) = 0 := by
  simp [integratedPairKernel, Finset.sum_filter]

private theorem sum_choose_antidiagonal_pos (a b : ℂ) (n : ℕ) :
    (∑ p ∈ antidiagonal (n + 1) with 0 < p.1 ∧ 0 < p.2,
      Ring.choose a p.1 * Ring.choose b p.2) =
      Ring.choose (a + b) (n + 1) - Ring.choose a (n + 1) - Ring.choose b (n + 1) := by
  let f (p : ℕ × ℕ) := Ring.choose a p.1 * Ring.choose b p.2
  have hfull : Ring.choose (a + b) (n + 1) =
      ∑ p ∈ antidiagonal (n + 1), f p := by
    have h := congrArg (PowerSeries.coeff (n + 1)) (PowerSeries.binomialSeries_add (A := ℂ) a b)
    simpa only [PowerSeries.binomialSeries_coeff, PowerSeries.coeff_mul, smul_eq_mul, mul_one, f]
      using h
  have hsplit (g : ℕ × ℕ → ℂ) :
      (∑ p ∈ antidiagonal (n + 1), g p) =
        (∑ k ∈ Finset.range n, g (k + 1, n + 1 - (k + 1))) + g (0, n + 1) + g (n + 1, 0) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
      Finset.sum_range_succ', Nat.sub_self, Nat.sub_zero]
  have hpos : (∑ p ∈ antidiagonal (n + 1) with 0 < p.1 ∧ 0 < p.2, f p) =
      ∑ k ∈ Finset.range n, f (k + 1, n + 1 - (k + 1)) := by
    rw [Finset.sum_filter, hsplit]
    simp only [Nat.not_lt_zero, false_and, and_false, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hsecond : 0 < n + 1 - (k + 1) := by omega
    exact ite_eq_left (And.intro (Nat.succ_pos k) hsecond)
  change (∑ p ∈ antidiagonal (n + 1) with 0 < p.1 ∧ 0 < p.2, f p) = _
  rw [hpos, hfull, hsplit f]
  simp only [f, Ring.choose_zero_right, one_mul, mul_one]
  ring

/-- Cancellation of `d * e` in every positive bidegree leaves a common `1/n`
on the degree-`n` antidiagonal. -/
theorem coeff_integratedPairKernel_of_ne_zero (r : ℂ) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff n (integratedPairKernel r) =
      (Ring.choose (-1 : ℂ) n - Ring.choose (-r) n - Ring.choose (r - 1) n) / (n : ℂ) := by
  rw [integratedPairKernel, PowerSeries.coeff_mk]
  calc
    _ = ∑ p ∈ antidiagonal n with 0 < p.1 ∧ 0 < p.2,
          (Ring.choose (-r) p.1 * Ring.choose (r - 1) p.2) / (n : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp, hd, he⟩
      have hsum : (p.1 : ℂ) + (p.2 : ℂ) = (n : ℂ) := by
        exact_mod_cast mem_antidiagonal.mp hp
      have hd0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
      have he0 : (p.2 : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt he
      rw [pairJetCoeff_closed r p.1 p.2 hd, hsum]
      calc
        _ = ((Ring.choose (-r) p.1 * Ring.choose (r - 1) p.2) / (n : ℂ)) *
              ((p.1 : ℂ) * (p.2 : ℂ)) / ((p.1 : ℂ) * (p.2 : ℂ)) := by ring
        _ = _ := mul_div_cancel_right₀ _ (mul_ne_zero hd0 he0)
    _ = _ := by
      cases n with
      | zero => exact (hn rfl).elim
      | succ n =>
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        rw [sum_choose_antidiagonal_pos, show -r + (r - 1) = (-1 : ℂ) by ring]

/-- The full integrated pair correction is `-log(1 + X) - J_r - J_(1-r)`. -/
theorem integratedPairKernel_eq (r : ℂ) :
    integratedPairKernel r =
      -PowerSeries.log ℂ - integratedScalarKernel r - integratedScalarKernel (1 - r) := by
  rw [← integratedScalarKernel_one]
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [coeff_zero_integratedPairKernel, map_sub, coeff_integratedScalarKernel,
      ite_true, sub_zero]
  · rw [coeff_integratedPairKernel_of_ne_zero r n hn]
    simp only [map_sub, coeff_integratedScalarKernel, ite_eq_right hn,
      show -(1 - r) = r - 1 by ring]
    ring

/-- For opposite moving residues, the common self-pairing `g` contributes
`-g * log(1 + X)` after the two half-weighted pair corrections. The pairings
`p` and `q` with the other charge retain their singleton primitives. -/
theorem oppositeResidue_cancellation (r g p q : ℂ) :
    (g + p) • integratedScalarKernel r + (g + q) • integratedScalarKernel (1 - r) +
        (g / 2) • (integratedPairKernel r + integratedPairKernel (1 - r)) =
      (-g) • PowerSeries.log ℂ + p • integratedScalarKernel r +
        q • integratedScalarKernel (1 - r) := by
  rw [integratedPairKernel_eq r, integratedPairKernel_eq (1 - r),
    show 1 - (1 - r) = r by ring]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_smul, smul_eq_mul]
  ring

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedJetKernels
