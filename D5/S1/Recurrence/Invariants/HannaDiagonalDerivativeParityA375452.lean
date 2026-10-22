/- GID: D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/HannaDiagonalDerivativeParityA375452
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The diagonal derivative equation has Hanna's two Mersenne parity supports. -/

/-
proof_shape: IsGF: bind-only (definition); consumers: result, claim.
proof_shape: claim: bind-only (definition); consumers: result.
proof_shape: result: bind-only; settles A375452.
escape_witness: none
admission_basis: open-problem-resolution (#18826; Proved)
Direct frozen dependency identities are provided in the handover.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19834.
The definitions state Hanna's generating equation and parity conjecture.
The shared theorem in HannaDiagonalDerivativeParity supplies existence and parity.
This unbounded symbolic proof performs no finite-instance computation; utility is none.
-/

import D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

set_option autoImplicit false

namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParityA375452

open PowerSeries

/-- OEIS A375452: "Expansion of g.f. A(x) satisfying [x^n] x*A'(x) / (1 - n*A(x)) = n^n for n >= 1",
offset 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 0 ∧
    ∀ n : ℕ, 1 ≤ n → coeff n (X * derivative (R := ℚ) A * (1 - C (n : ℚ) * A)⁻¹) = (n : ℚ) ^ n

/-- OEIS A375452 (P. D. Hanna), conjecture: "for n > 1, a(n) is odd iff n is of the form 2^k-2 or 2^k-1
for some k > 1." -/
def claim : Prop :=
  (∃ A, IsGF A) ∧
    ∀ A, IsGF A → ∀ n : ℕ, 1 < n → ∃ m : ℤ, coeff n A = m ∧
      (Odd m ↔ ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1))

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParityA375452

namespace D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParityA375452
open PowerSeries D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParity

theorem result : claim := by
  let t : ℕ → ℤ := fun n => (n : ℤ) ^ (n - 1)
  have ht : ∀ n, 1 ≤ n → (t n : ZMod 2) = (n : ZMod 2) := by
    intro n hn
    dsimp only [t]
    push_cast
    by_cases h1 : n = 1
    · subst n; norm_num
    have he : n - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (lt_of_le_of_ne hn (Ne.symm h1))
    rcases Nat.even_or_odd n with hev | ho
    · rw [hev.natCast_zmod_two, zero_pow he]
    · rw [ho.natCast_zmod_two, one_pow]
  have hp : ∀ n : ℕ, 1 ≤ n → (n : ℚ) * (t n : ℚ) = (n : ℚ) ^ n := by
    intro n hn
    dsimp only [t]
    push_cast
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have hequiv : ∀ A : PowerSeries ℚ, IsGF A ↔ IsDiagonal (fun n => (t n : ℚ)) A := by
    intro A
    constructor
    · rintro ⟨h0, hA⟩
      exact ⟨h0, fun n hn => (hA n hn).trans (hp n hn).symm⟩
    · rintro ⟨h0, hA⟩
      exact ⟨h0, fun n hn => (hA n hn).trans (hp n hn)⟩
  have h := diagonal_integral_parity t ht
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA⟩ := h.1
    exact ⟨A, (hequiv A).mpr hA⟩
  · intro A hA
    exact h.2 A ((hequiv A).mp hA)

end D5.S1.Recurrence.Invariants.HannaDiagonalDerivativeParityA375452
