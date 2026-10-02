/- GID: D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/WStateTIMPSBondDimension
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.claim; result=D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.result; claim=D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.claim
   digest: A bond-dimension-3 TI PBC MPS of W_7 beats the floor(n/2)+1 bound of 2306.16456. -/

/-
proof_shape: result: bind-only (evaluation of the definitions at one explicit pair of 3 × 3
  matrices: the 128 word traces of the integer matrices by kernel computation, and the factor
  1/√7 pulled out of each word)
escape_witness: null
admission_basis: open-problem-resolution (issue #12026; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.SpinChains.WStateTIMPSBondDimension

/-- `A 0`, `A 1` are a translation-invariant matrix product state representation with periodic
boundary conditions, of bond dimension `d`, of the normalized `W`-state of order `n`: for every
word `w ∈ {0, 1}ⁿ`, the trace of `A (w 0) * A (w 1) * ⋯ * A (w (n - 1))` is `1/√n` when `w` has
exactly one letter `1`, and `0` otherwise. -/
def IsWStateTIMPS (n d : ℕ) (A : Fin 2 → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ w : Fin n → Fin 2, Matrix.trace (List.ofFn fun i => A (w i)).prod =
    if ∑ i, (w i : ℕ) = 1 then ((1 / Real.sqrt n : ℝ) : ℂ) else 0

/-- The conjecture of Klimov, Sengupta and Biamonte (arXiv:2306.16456, l. 414): for `n ≥ 2`,
every translation-invariant MPS representation with periodic boundary conditions of the
`W`-state of order `n` has bond dimension at least `⌊n/2⌋ + 1`. -/
def claim : Prop :=
  ∀ (n d : ℕ) (A : Fin 2 → Matrix (Fin d) (Fin d) ℂ), 2 ≤ n → IsWStateTIMPS n d A →
    n / 2 + 1 ≤ d

/-- The conjecture fails at `n = 7`: the matrices `A 0 = E₁₂ + E₂₁ + E₂₃` and
`A 1 = E₃₁ / √7` represent the `W`-state of order `7` with bond dimension `3 < ⌊7/2⌋ + 1`. -/
theorem result : ¬ claim := by
  intro h
  have hcount : ∀ w : Fin 7 → Fin 2,
      (if ∑ i, (w i : ℕ) = 1 then
        Matrix.trace (List.ofFn fun i =>
          (![!![0,1,0;1,0,1;0,0,0], !![0,0,0;0,0,0;1,0,0]] : Fin 2 → Matrix (Fin 3) (Fin 3) ℕ)
            (w i)).prod = 1 ∧ (List.ofFn w).count 1 = 1
      else Matrix.trace (List.ofFn fun i =>
          (![!![0,1,0;1,0,1;0,0,0], !![0,0,0;0,0,0;1,0,0]] : Fin 2 → Matrix (Fin 3) (Fin 3) ℕ)
            (w i)).prod = 0) := by
    decide +kernel
  set M : Fin 2 → Matrix (Fin 3) (Fin 3) ℕ :=
    ![!![0,1,0;1,0,1;0,0,0], !![0,0,0;0,0,0;1,0,0]]
  set c : ℂ := ((1 / Real.sqrt 7 : ℝ) : ℂ) with hc
  set f : ℕ →+* ℂ := Nat.castRingHom ℂ
  set A : Fin 2 → Matrix (Fin 3) (Fin 3) ℂ :=
    fun b => (if b = 1 then c else 1) • (M b).map f with hA
  have hscale : ∀ l : List (Fin 2),
      (l.map A).prod = c ^ (l.count 1) • ((l.map M).prod.map f) := by
    intro l
    induction l with
    | nil => simp [Matrix.map_one (⇑f) (map_zero f) (map_one f)]
    | cons b l ih =>
      rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, Matrix.map_mul,
        List.count_cons]
      fin_cases b <;> simp [hA, pow_succ, smul_smul, mul_comm]
  have hW : IsWStateTIMPS 7 3 A := by
    intro w
    have hw := hcount w
    rw [show (List.ofFn fun i => A (w i)) = (List.ofFn w).map A by rw [List.map_ofFn]; rfl,
      hscale, Matrix.trace_smul, ← AddMonoidHom.map_trace,
      show (List.ofFn w).map M = List.ofFn fun i => M (w i) by rw [List.map_ofFn]; rfl]
    split_ifs at hw ⊢ with h1
    · obtain ⟨htr, hk⟩ := hw
      rw [hk, htr]
      simp [hc]
    · rw [hw]
      simp
  exact absurd (h 7 3 A (by norm_num) hW) (by norm_num)

end D5.S3.Quantum.SpinChains.WStateTIMPSBondDimension
