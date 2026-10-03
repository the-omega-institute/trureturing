/- GID: D5/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NarayanaStrip/CiglerStripProductSeries
   mirror-E: none(waiver:good-height-continuant-factorization)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Expand]
   utility: none
   digest: Doubling the common recurrence factors both good-height numerators and denominators. -/

import D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra
import Mathlib.RingTheory.PowerSeries.Expand

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

theorem product_factorization (t z : R) (m : ℕ) :
    cont (plusWeight (t ^ 2) (z ^ 2)) 0 1 (4 * m + 1) =
        cont (minusWeight t z) 0 1 (4 * m + 1) *
          cont (minusWeight (-t) (-z)) 0 1 (4 * m + 1) ∧
      cont (plusWeight (t ^ 2) (z ^ 2)) 1 1 (4 * m + 1) =
        cont (minusWeight t z) 1 1 (4 * m + 1) *
          cont (minusWeight (-t) (-z)) 1 1 (4 * m + 1) ∧
      cont (plusWeight (t ^ 2) (z ^ 2)) 0 1 (4 * m + 2) =
        cont (minusWeight t z) 0 1 (4 * m + 2) *
          cont (minusWeight (-t) (-z)) 0 1 (4 * m + 2) ∧
      cont (plusWeight (t ^ 2) (z ^ 2)) 1 1 (4 * m + 2) =
        cont (minusWeight t z) 1 1 (4 * m + 2) *
          cont (minusWeight (-t) (-z)) 1 1 (4 * m + 2) := by
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
  have doubling : ∀ k : ℕ,
      F (2 * k + 1) = F (k + 1) ^ 2 - B * F k ^ 2 ∧
        F (2 * k) = 2 * F (k + 1) * F k - A * F k ^ 2 := by
    intro k
    induction k with
    | zero => simp [initialZero, initialOne]
    | succ k ih =>
        have evenNext : F (2 * k + 2) = A * F (2 * k + 1) - B * F (2 * k) := by
          exact recurrenceStep (2 * k)
        have oddNext : F (2 * k + 3) = A * F (2 * k + 2) - B * F (2 * k + 1) := by
          exact recurrenceStep (2 * k + 1)
        have next : F (k + 2) = A * F (k + 1) - B * F k := by
          exact recurrenceStep k
        change F (2 * (k + 1) + 1) = F (k + 2) ^ 2 - B * F (k + 1) ^ 2 ∧
          F (2 * (k + 1)) = 2 * F (k + 2) * F (k + 1) - A * F (k + 1) ^ 2
        rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
          show 2 * (k + 1) = 2 * k + 2 by omega,
          oddNext, evenNext, ih.1, ih.2, next]
        constructor <;> ring
  have flipped : core (-t) (-z) = core t z := by
    change LinearRecurrence.mkSol
        (LinearRecurrence.mk 2 ![-((-t) ^ 2 * (-z) ^ 4), 1 - (1 + (-t) ^ 2) * (-z) ^ 2])
        ![0, 1] =
      LinearRecurrence.mkSol
        (LinearRecurrence.mk 2 ![-(t ^ 2 * z ^ 4), 1 - (1 + t ^ 2) * z ^ 2]) ![0, 1]
    rw [show (-t) ^ 2 * (-z) ^ 4 = t ^ 2 * z ^ 4 by ring,
      show 1 - (1 + (-t) ^ 2) * (-z) ^ 2 = 1 - (1 + t ^ 2) * z ^ 2 by ring]
  obtain ⟨pMinus, qMinus, pNext, qNext⟩ := minus_endpoints t z m
  obtain ⟨pFlip, qFlip, pFlipNext, qFlipNext⟩ := minus_endpoints (-t) (-z) m
  rw [flipped] at pFlip qFlip pFlipNext qFlipNext
  obtain ⟨pPlus, qPlus, _, _⟩ := plus_endpoints t z (2 * m)
  obtain ⟨_, _, pPlusNext, qPlusNext⟩ := plus_endpoints t z (2 * m + 1)
  rw [show 2 * (2 * m) + 1 = 4 * m + 1 by omega] at pPlus qPlus
  rw [show 2 * (2 * m + 1) = 4 * m + 2 by omega] at pPlusNext qPlusNext
  rw [pMinus, qMinus, pNext, qNext, pFlip, qFlip, pFlipNext, qFlipNext,
    pPlus, qPlus, pPlusNext, qPlusNext]
  change F (2 * m + 1) + z ^ 2 * F (2 * m) =
      (F (m + 1) + (z + z ^ 2) * F m) *
        (F (m + 1) + (-z + (-z) ^ 2) * F m) ∧
    F (2 * m + 1) = (F (m + 1) - t * z ^ 2 * F m) *
      (F (m + 1) - (-t) * (-z) ^ 2 * F m) ∧
    F (2 * m + 1) = (F (m + 1) + t * z ^ 2 * F m) *
      (F (m + 1) + (-t) * (-z) ^ 2 * F m) ∧
    F (2 * m + 2) + t ^ 2 * z ^ 2 * F (2 * m + 1) =
      (F (m + 1) - z * (F (m + 1) + t ^ 2 * z ^ 2 * F m)) *
        (F (m + 1) - (-z) * (F (m + 1) + (-t) ^ 2 * (-z) ^ 2 * F m))
  have next : F (2 * m + 2) = A * F (2 * m + 1) - B * F (2 * m) := by
    exact recurrenceStep (2 * m)
  rw [next, (doubling m).1, (doubling m).2]
  dsimp only [A, B]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

end D5.S3.Combinatorics.NarayanaStrip.CiglerStripProductAlgebra
