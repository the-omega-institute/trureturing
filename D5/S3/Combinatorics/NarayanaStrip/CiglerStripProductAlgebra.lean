/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripProductAlgebra
   mirror-E: none(waiver:generic-continuant-product-algebra)
   anchors: [mathlib/module/Mathlib.Algebra.LinearRecurrence]
   utility: none
   digest: Generic ring continuants and the algebraic factorization at Cigler's good heights. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductContinuants
import Mathlib.Algebra.LinearRecurrence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra

variable {R : Type*} [CommRing R]

local notation "minusWeight" =>
  (fun (t z : R) (n : ℕ) =>
    ite (n % 4 = 0) (1 : R) (ite (n % 4 = 1) t (ite (n % 4 = 2) (-1) (-t))) * z)

local notation "plusWeight" =>
  (fun (t z : R) (n : ℕ) => ite (n % 2 = 0) (1 : R) t * z)

local notation "core" =>
  (fun (t z : R) =>
    LinearRecurrence.mkSol
      (LinearRecurrence.mk 2 ![-(t ^ 2 * z ^ 4), 1 - (1 + t ^ 2) * z ^ 2]) ![0, 1])

theorem minus_endpoints (t z : R) (m : ℕ) :
    cont (minusWeight t z) 0 1 (4 * m + 1) =
        core t z (m + 1) + (z + z ^ 2) * core t z m ∧
      cont (minusWeight t z) 1 1 (4 * m + 1) =
        core t z (m + 1) - t * z ^ 2 * core t z m ∧
      cont (minusWeight t z) 0 1 (4 * m + 2) =
        core t z (m + 1) + t * z ^ 2 * core t z m ∧
      cont (minusWeight t z) 1 1 (4 * m + 2) =
        core t z (m + 1) - z * (core t z (m + 1) + t ^ 2 * z ^ 2 * core t z m) := by
  let A := 1 - (1 + t ^ 2) * z ^ 2
  let B := t ^ 2 * z ^ 4
  let recurrence : LinearRecurrence R := ⟨2, ![-B, A]⟩
  let F := recurrence.mkSol ![0, 1]
  have initialZero : F 0 = 0 := recurrence.mkSol_eq_init ![0, 1] 0
  have initialOne : F 1 = 1 := recurrence.mkSol_eq_init ![0, 1] 1
  have recurrenceStep (index : ℕ) : F (index + 2) = A * F (index + 1) - B * F index := by
    have step := recurrence.is_sol_mkSol ![0, 1] index
    simp only [recurrence, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero] at step
    change F (index + 2) = -B * F index + A * F (index + 1) at step
    rw [step]
    ring
  have terminal (r0 r1 : R) (k : ℕ) :
      cont (minusWeight t z) r0 r1 (4 * k + 2) =
        cont (minusWeight t z) r0 r1 (4 * k + 1) -
          z * cont (minusWeight t z) r0 r1 (4 * k) := by
    rw [cont]
    simp
  have step (r0 r1 : R) (k : ℕ) :
      cont (minusWeight t z) r0 r1 (4 * (k + 1) + 1) =
          (1 + z - t ^ 2 * z ^ 2) * cont (minusWeight t z) r0 r1 (4 * k + 1) -
            (z + (1 + t) * z ^ 2) * cont (minusWeight t z) r0 r1 (4 * k) ∧
        cont (minusWeight t z) r0 r1 (4 * (k + 1)) =
          (1 + (1 - t) * z) * cont (minusWeight t z) r0 r1 (4 * k + 1) -
            (z + z ^ 2) * cont (minusWeight t z) r0 r1 (4 * k) := by
    have third : cont (minusWeight t z) r0 r1 (4 * k + 3) =
        cont (minusWeight t z) r0 r1 (4 * k + 2) -
          t * z * cont (minusWeight t z) r0 r1 (4 * k + 1) := by
      rw [show 4 * k + 3 = (4 * k + 1) + 2 by omega, cont]
      simp [Nat.add_mod]
    have fourth : cont (minusWeight t z) r0 r1 (4 * k + 4) =
        cont (minusWeight t z) r0 r1 (4 * k + 3) +
          z * cont (minusWeight t z) r0 r1 (4 * k + 2) := by
      rw [show 4 * k + 4 = (4 * k + 2) + 2 by omega, cont]
      simp [Nat.add_mod]
    have fifth : cont (minusWeight t z) r0 r1 (4 * k + 5) =
        cont (minusWeight t z) r0 r1 (4 * k + 4) +
          t * z * cont (minusWeight t z) r0 r1 (4 * k + 3) := by
      rw [show 4 * k + 5 = (4 * k + 3) + 2 by omega, cont]
      simp [Nat.add_mod]
    rw [show 4 * (k + 1) + 1 = 4 * k + 5 by omega,
      show 4 * (k + 1) = 4 * k + 4 by omega, fifth, fourth, third, terminal]
    constructor <;> ring
  have blocks : ∀ k : ℕ, ∀ r0 r1 : R,
      cont (minusWeight t z) r0 r1 (4 * k + 1) =
          (F (k + 1) + (z + z ^ 2) * F k) * r1 -
            (z + (1 + t) * z ^ 2) * F k * r0 ∧
        cont (minusWeight t z) r0 r1 (4 * k) =
          (1 + (1 - t) * z) * F k * r1 +
            (F (k + 1) - (1 + z - t ^ 2 * z ^ 2) * F k) * r0 := by
    intro k
    induction k with
    | zero =>
        intro r0 r1
        simp [cont, initialZero, initialOne]
    | succ k ih =>
        intro r0 r1
        obtain ⟨upper, lower⟩ := ih r0 r1
        obtain ⟨upperStep, lowerStep⟩ := step r0 r1 k
        have next : F (k + 2) = A * F (k + 1) - B * F k := by
          exact recurrenceStep k
        change cont (minusWeight t z) r0 r1 (4 * (k + 1) + 1) = _ ∧
          cont (minusWeight t z) r0 r1 (4 * (k + 1)) = _
        rw [upperStep, lowerStep, upper, lower]
        change _ = (F (k + 2) + (z + z ^ 2) * F (k + 1)) * r1 -
            (z + (1 + t) * z ^ 2) * F (k + 1) * r0 ∧
          _ = (1 + (1 - t) * z) * F (k + 1) * r1 +
            (F (k + 2) - (1 + z - t ^ 2 * z ^ 2) * F (k + 1)) * r0
        rw [next]
        dsimp only [A, B]
        constructor <;> ring
  obtain ⟨pUpper, pLower⟩ := blocks m 0 1
  obtain ⟨qUpper, qLower⟩ := blocks m 1 1
  change cont (minusWeight t z) 0 1 (4 * m + 1) = _ ∧
    cont (minusWeight t z) 1 1 (4 * m + 1) = _ ∧
    cont (minusWeight t z) 0 1 (4 * m + 2) = _ ∧
    cont (minusWeight t z) 1 1 (4 * m + 2) = _
  rw [terminal, terminal, pUpper, pLower, qUpper, qLower]
  change _ = F (m + 1) + (z + z ^ 2) * F m ∧
    _ = F (m + 1) - t * z ^ 2 * F m ∧
    _ = F (m + 1) + t * z ^ 2 * F m ∧
    _ = F (m + 1) - z * (F (m + 1) + t ^ 2 * z ^ 2 * F m)
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

theorem plus_endpoints (t z : R) (k : ℕ) :
    cont (plusWeight (t ^ 2) (z ^ 2)) 0 1 (2 * k + 1) =
        core t z (k + 1) + z ^ 2 * core t z k ∧
      cont (plusWeight (t ^ 2) (z ^ 2)) 1 1 (2 * k + 1) = core t z (k + 1) ∧
      cont (plusWeight (t ^ 2) (z ^ 2)) 0 1 (2 * k) = core t z k ∧
      cont (plusWeight (t ^ 2) (z ^ 2)) 1 1 (2 * k) =
        core t z (k + 1) + t ^ 2 * z ^ 2 * core t z k := by
  let A := 1 - (1 + t ^ 2) * z ^ 2
  let B := t ^ 2 * z ^ 4
  let recurrence : LinearRecurrence R := ⟨2, ![-B, A]⟩
  let F := recurrence.mkSol ![0, 1]
  have initialZero : F 0 = 0 := recurrence.mkSol_eq_init ![0, 1] 0
  have initialOne : F 1 = 1 := recurrence.mkSol_eq_init ![0, 1] 1
  have recurrenceStep (index : ℕ) : F (index + 2) = A * F (index + 1) - B * F index := by
    have step := recurrence.is_sol_mkSol ![0, 1] index
    simp only [recurrence, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, add_zero] at step
    change F (index + 2) = -B * F index + A * F (index + 1) at step
    rw [step]
    ring
  have first (r0 r1 : R) (n : ℕ) :
      cont (plusWeight (t ^ 2) (z ^ 2)) r0 r1 (2 * n + 2) =
        cont (plusWeight (t ^ 2) (z ^ 2)) r0 r1 (2 * n + 1) -
          z ^ 2 * cont (plusWeight (t ^ 2) (z ^ 2)) r0 r1 (2 * n) := by
    rw [cont]
    simp
  have second (r0 r1 : R) (n : ℕ) :
      cont (plusWeight (t ^ 2) (z ^ 2)) r0 r1 (2 * n + 3) =
        cont (plusWeight (t ^ 2) (z ^ 2)) r0 r1 (2 * n + 2) -
          t ^ 2 * z ^ 2 * cont (plusWeight (t ^ 2) (z ^ 2)) r0 r1 (2 * n + 1) := by
    rw [show 2 * n + 3 = (2 * n + 1) + 2 by omega, cont]
    simp [Nat.add_mod]
  change cont (plusWeight (t ^ 2) (z ^ 2)) 0 1 (2 * k + 1) =
      F (k + 1) + z ^ 2 * F k ∧
    cont (plusWeight (t ^ 2) (z ^ 2)) 1 1 (2 * k + 1) = F (k + 1) ∧
    cont (plusWeight (t ^ 2) (z ^ 2)) 0 1 (2 * k) = F k ∧
    cont (plusWeight (t ^ 2) (z ^ 2)) 1 1 (2 * k) =
      F (k + 1) + t ^ 2 * z ^ 2 * F k
  induction k with
  | zero => simp [cont, initialZero, initialOne]
  | succ k ih =>
      obtain ⟨pOdd, qOdd, pEven, qEven⟩ := ih
      have next : F (k + 2) = A * F (k + 1) - B * F k := by
        exact recurrenceStep k
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
        show 2 * (k + 1) = 2 * k + 2 by omega,
        second, second, first, first, pOdd, qOdd, pEven, qEven]
      change _ = F (k + 2) + z ^ 2 * F (k + 1) ∧
        _ = F (k + 2) ∧ _ = F (k + 1) ∧
        _ = F (k + 2) + t ^ 2 * z ^ 2 * F (k + 1)
      rw [next]
      dsimp only [A, B]
      constructor
      · ring
      constructor
      · ring
      constructor <;> ring

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra
