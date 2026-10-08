/- GID: D5/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/FiniteScalarTraceKernel
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Finite scalar deletion traces determine exact modular source kernels. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S1.Dynamics.ProfiniteCharacter
import D5.S1.Digit.Infinite.SuccessorContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.FiniteScalarTraceKernel

open D5.S3.Arith.FibonacciAtomic.GraftAffineClosure (step quantity)
open D5.S1.Dynamics (ProfiniteIntegers)
open D5.S1.Dynamics.ProfiniteCharacter (residueProjection)
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)

local notation "Source" => LegalDigits × (ProfiniteIntegers × ProfiniteIntegers)

/-- Delete successive digits using the inverse Fibonacci matrix. -/
def trajectory {R : Type*} [CommRing R] (U : ℕ → R) (z : R × R) : ℕ → R × R
  | 0 => z
  | j + 1 => ((trajectory U z j).2 - (trajectory U z j).1 + U j,
      (trajectory U z j).1 - U j)

/-- The `r + 1` scalar readings modulo the positive modulus `m + 1`. -/
def scalarTrace (m r : ℕ) (p : Source) : Fin (r + 1) → ZMod (m + 1) :=
  fun j => quantity (trajectory (fun k => ((p.1.val k).toNat : ZMod (m + 1)))
    (residueProjection m p.2.1, residueProjection m p.2.2) j.val)

private theorem bounded_propagation {R : Type*} [CommRing R]
    (c c' f f' : ℕ → R) (r : ℕ)
    (hc : ∀ j, c j - c (j + 1) - c (j + 2) = f j)
    (hc' : ∀ j, c' j - c' (j + 1) - c' (j + 2) = f' j)
    (h0 : c 0 = c' 0) (h1 : c 1 = c' 1)
    (hf : ∀ j, j + 2 ≤ r → f j = f' j) :
    ∀ j, j ≤ r → c j = c' j := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero => exact fun _ => h0
  | one => exact fun _ => h1
  | more j hj hj' =>
    intro hbound
    have he := hf j hbound
    have ha := hj (by omega)
    have hb := hj' (by omega)
    linear_combination ha - hb - hc j + hc' j + he

private theorem scalar_recurrence {R : Type*} [CommRing R]
    (U : ℕ → R) (z : R × R) (j : ℕ) :
    quantity (trajectory U z j) - quantity (trajectory U z (j + 1)) -
      quantity (trajectory U z (j + 2)) = 2 * U j + U (j + 1) := by
  simp only [trajectory, quantity]
  ring

private theorem trace_kernel {R : Type*} [CommRing R]
    (U U' : ℕ → R) (z z' : R × R) (r : ℕ) (hr : 1 ≤ r) :
    (∀ j, j ≤ r → quantity (trajectory U z j) = quantity (trajectory U' z' j)) ↔
      z' - z = (-3 * (U' 0 - U 0), 2 * (U' 0 - U 0)) ∧
        ∀ j, j + 2 ≤ r → 2 * (U' j - U j) + (U' (j + 1) - U (j + 1)) = 0 := by
  constructor
  · intro h
    have h0 := h 0 (by omega)
    have h1 := h 1 hr
    simp only [trajectory, quantity] at h0 h1
    refine ⟨?_, ?_⟩
    · apply Prod.ext
      · change z'.1 - z.1 = -3 * (U' 0 - U 0)
        linear_combination 2 * h0 - 3 * h1
      · change z'.2 - z.2 = 2 * (U' 0 - U 0)
        linear_combination 2 * h1 - h0
    · intro j hj
      have ha := h j (by omega)
      have hb := h (j + 1) (by omega)
      have hc := h (j + 2) hj
      linear_combination scalar_recurrence U' z' j - scalar_recurrence U z j +
        ha - hb - hc
  · rintro ⟨hz, hf⟩
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    change z'.1 - z.1 = -3 * (U' 0 - U 0) at hx
    change z'.2 - z.2 = 2 * (U' 0 - U 0) at hy
    apply bounded_propagation
      (fun j => quantity (trajectory U z j)) (fun j => quantity (trajectory U' z' j))
      (fun j => 2 * U j + U (j + 1)) (fun j => 2 * U' j + U' (j + 1)) r
      (scalar_recurrence U z) (scalar_recurrence U' z')
    · simp only [trajectory, quantity]
      linear_combination -2 * hx - 3 * hy
    · simp only [trajectory, quantity]
      linear_combination -hx - 2 * hy
    · intro j hj
      linear_combination -hf j hj

end D5.S3.Arith.FibonacciAtomic.FiniteScalarTraceKernel
