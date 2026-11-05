/- GID: D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/BalaA193236ModFiveSeven
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's unbounded modulo-five and modulo-seven coefficient congruences. -/

/-
proof_shape: F: bind-only (definition); consumers: IsGF, result, source236.
proof_shape: IsGF: bind-only (definition); consumers: claim.
proof_shape: claim: bind-only (definition); consumers: result.
proof_shape: weight236: bind-only (definition); consumers: result, source236, weight236_nine.
proof_shape: weight236_nine: bind-only; consumers: result.
proof_shape: source236: bind-only; consumers: result.
proof_shape: result: bind-only; consumers: none.
escape_witness: none
admission_basis: open-problem-resolution (#22113; Proved)
Direct frozen dependencies: F: none.
Direct frozen dependencies: IsGF: none.
Direct frozen dependencies: claim: none.
Direct frozen dependencies: weight236: none.
Direct frozen dependencies: weight236_nine: none.
Direct frozen dependencies: source236: none.
Direct frozen dependencies: result: D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.exists_unique_fixed @ sha256:bd62df5aa141eaff1ceec9e8af00309b4a8e194b4354ad180a51862599cef981; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.Agree @ sha256:76d7ce5ef0f66968d4516f93f05e27e9125f8f29944ffacca0d95b580f786d34; D5/S1/Recurrence/Invariants/UnitReversionSquareParity.agree_iff @ sha256:b8236ebf1419cfde429c1b9ba55a7c2c22195bd600685feda80fdbf0688cd6d6.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22201.
The source coefficient sum, normalization and claim retain their literal expressions.
-/

import D5.S1.Recurrence.Residue.BalaA193237ModFiveSeven

set_option autoImplicit false
open PowerSeries
open D5.S1.Recurrence.Residue.BalaA193237ModFiveSeven

namespace D5.S1.Recurrence.Residue.BalaA193236ModFiveSeven

/-- The series inside the reciprocal cube root in OEIS A193236, with its literal weights.
The coefficient sum is finite: j(j+1)/2 = m implies j ≤ m. -/
noncomputable def F : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ j ∈ Finset.range (m + 1),
      if j * (j + 1) / 2 = m then
        (-3 : ℚ) ^ j * ((2 * j + 1 : ℕ) : ℚ)
      else 0

/-- The reciprocal cube root with constant coefficient one: A^3 * F = 1. -/
def IsGF (A : PowerSeries ℚ) : Prop :=
  constantCoeff A = 1 ∧ A ^ 3 * F = 1

/-- Both clauses of Bala's %F conjecture, with existence and integral coefficients. -/
def claim : Prop :=
  (∃ A : PowerSeries ℚ, IsGF A) ∧
    ∀ A : PowerSeries ℚ, IsGF A →
      ∃ a : ℕ → ℤ,
        (∀ m : ℕ, coeff m A = (a m : ℚ)) ∧
          ∀ n : ℕ, (5 : ℤ) ∣ a (5 * n + 4) ∧ (7 : ℤ) ∣ a (7 * n + 5)


private noncomputable def weight236 (j : ℕ) : ℤ := (-3)^j

private theorem weight236_nine (j : ℕ) (hj : 0 < j) :
    (9 : ℤ) ∣ ((2*j+1 : ℕ) : ℤ)*weight236 j := by
  rcases j with _ | _ | k
  · omega
  · norm_num [weight236]
  · change (9 : ℤ) ∣ ((2*(k+2)+1 : ℕ) : ℤ) * (-3)^(k+2)
    refine ⟨((2*(k+2)+1 : ℕ) : ℤ) * (-3)^k, ?_⟩
    rw [pow_add]
    ring

private theorem source236 : F =
    PowerSeries.map (Int.castRingHom ℚ) (triangular weight236) := by
  ext n
  simp only [F, triangular, coeff_mk, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs with ht
  · simp only [weight236, map_mul, map_pow, map_neg, map_one, map_ofNat,
      map_natCast]
    ring
  · simp

theorem result : claim := by
  exact D5.S1.Recurrence.Residue.BalaA193237ModFiveSeven.resolve F weight236 (by norm_num [weight236]) weight236_nine source236

end D5.S1.Recurrence.Residue.BalaA193236ModFiveSeven
