/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthMSDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Single-length prime moments and the restricted Montgomery–Soundararajan correlation hypothesis. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.ContinuousSampling
import D5.S3.Arith.Robin.ForwardKernel.VarianceTransferDefs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
open VarianceTransferDefs
noncomputable section
set_option autoImplicit false

def chebyshevError (x : ℝ) : ℝ := Chebyshev.psi x - x
def primeIncrement (v x : ℝ) : ℝ := increment chebyshevError v x
def montgomerySoundararajanConstant : ℝ := 1 - Real.eulerMascheroniConstant - Real.log (2 * Real.pi)
def discretePrimeMoment (k N K : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, primeIncrement (K : ℝ) (n : ℝ) ^ k

def continuousPrimeMoment (k : ℕ) (Y v : ℝ) : ℝ := ∫ x in (1 : ℝ)..Y, primeIncrement v x ^ k

def montgomerySoundararajanMainTerm (k : ℕ) (Y v : ℝ) : ℝ :=
  (if k = 2 then (1 : ℝ) else 3) * v ^ (k / 2) *
    (∫ y in (1 : ℝ)..Y, (Real.log (y / v) + montgomerySoundararajanConstant) ^ (k / 2))

def montgomerySoundararajanError (k : ℕ) (ε Y v : ℝ) : ℝ :=
  Y * Real.log Y ^ (k / 2) * v ^ (k / 2) *
      (v / Real.log Y) ^ (-1 / (8 * (k : ℝ))) +
    v ^ k * Y ^ (1 / 2 + ε)

private def primeCorrelationError {r : ℕ} (d : Fin r → ℕ) (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ∏ i, ArithmeticFunction.vonMangoldt (n + d i)) -
    y * concreteSS (Finset.univ.image d)

private abbrev LengthFamily := ℕ → ℕ → Prop

/-- Equation (20), restricted to an arbitrary family of lengths, with a single
    constant uniform in N, K, r, shifts, and real cutoff y. -/
def MS20 (k : ℕ) (R : LengthFamily) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 < A ∧
    ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, R N K →
      ∀ r : ℕ, 1 ≤ r → r ≤ k → ∀ d : Fin r → ℕ,
        Function.Injective d → (∀ i, 1 ≤ d i ∧ d i ≤ K) →
        ∀ y : ℝ, 0 ≤ y → y ≤ (N : ℝ) →
          |primeCorrelationError d y| ≤ A * (N : ℝ) ^ (1 / 2 + ε)

/-- The external result is passed as a term of this Prop. k is fixed before
    all constants. The integer cutoff N and length K match equation (18). -/
def MSThirdTheorem : Prop :=
  ∀ k : ℕ, (k = 2 ∨ k = 4) → ∀ R : LengthFamily, MS20 k R →
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∀ K : ℕ, R N K →
        Real.log (N : ℝ) ≤ (K : ℝ) →
        (K : ℝ) ≤ (N : ℝ) ^ (1 / (k : ℝ)) →
          |discretePrimeMoment k N K - montgomerySoundararajanMainTerm k (N : ℝ) (K : ℝ)| ≤
            C * montgomerySoundararajanError k ε (N : ℝ) (K : ℝ)

def polynomialLengthFamily (β M : ℝ) : LengthFamily :=
  fun N K => (K : ℝ) ≤ M * (N : ℝ) ^ β


/-- Strong Hardy–Littlewood errors give the restricted correlation hypothesis. -/
theorem hl4_implies_ms20 (β M : ℝ) (k : ℕ) (hM : 1 ≤ M) (hk : k ≤ 4)
    (hHL : HL4 concreteSS β) : MS20 k (polynomialLengthFamily β M) := by
  intro ε hε
  obtain ⟨A, hA, N₀, hN₀⟩ := hHL ε hε M hM
  refine ⟨A, hA, eventually_atTop.mpr ⟨⌈N₀⌉₊, ?_⟩⟩
  intro N hN K hK r hr hrk d hd hdK y hy hyN
  have hNN : N₀ ≤ (N : ℝ) := (Nat.le_ceil N₀).trans (by exact_mod_cast hN)
  have hshift (i : Fin r) : 1 ≤ d i ∧ (d i : ℝ) ≤ M * (N : ℝ) ^ β := by
    refine ⟨(hdK i).1, ?_⟩
    have hcast : (d i : ℝ) ≤ (K : ℝ) := by exact_mod_cast (hdK i).2
    exact hcast.trans hK
  have hy3 : y ≤ 3 * (N : ℝ) := by
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  exact hN₀ N hNN r hr (hrk.trans hk) d hd hshift y hy hy3


/-- An integer-length centered prime increment is the corresponding lattice sum. -/
theorem integer_increment (n K : ℕ) : primeIncrement (K : ℝ) (n : ℝ) = S (K : ℝ) 0 1 n := by
  rw [S_eq_psi_shift _ _ _ _ (by norm_num) (by norm_num) (Nat.cast_nonneg K)]
  simp only [one_mul, zero_mul, Nat.floor_natCast, Nat.floor_zero, Nat.add_zero,
    Nat.cast_add, Nat.cast_zero, sub_zero, primeIncrement, increment, chebyshevError]
  ring

/-- At an integer base point, the lattice sum uses the natural floor of the length. -/
theorem real_length_cell (v : ℝ) (n : ℕ) (_hv : 0 ≤ v) :
    S v 0 1 n = primeIncrement (⌊v⌋₊ : ℝ) (n : ℝ) := by
  rw [integer_increment]
  simp only [S, points, zero_mul, one_mul, Nat.floor_zero, Nat.floor_natCast]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
