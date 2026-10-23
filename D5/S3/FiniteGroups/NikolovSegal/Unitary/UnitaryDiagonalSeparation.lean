/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalSeparation
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryDiagonalSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryDiagonalGeometry
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryIntegerWeights

namespace NikolovSegal.UnitaryField

open Matrix
variable {F : Type*} [Field F] [Finite F]

theorem pairedEntries_eq_exponent (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) (i : Fin d ⊕ Fin d) :
    pairedEntries ι a u i = u ^ pairedExponent (Nat.card (fixedField ι)) a i := by
  cases i with
  | inl i => rfl
  | inr i =>
    simp only [pairedEntries, pairedExponent, involutionUnit_pow ι hinv hne]
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    ring

theorem oddEntries_eq_exponent (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    {d : ℕ} (a : Fin d → ℤ) (u : Fˣ) (i : Option (Fin d ⊕ Fin d)) :
    oddEntries ι a u i = u ^ oddExponent (Nat.card (fixedField ι)) a i := by
  cases i with
  | none =>
    simp only [oddEntries, oddExponent, involutionUnit_pow ι hinv hne]
    have hd : u / u ^ Nat.card (fixedField ι) =
        u ^ (1 - (Nat.card (fixedField ι) : ℤ)) := by
      rw [zpow_sub, zpow_one, zpow_natCast]
      rfl
    rw [hd, ← zpow_mul]
    congr 1
    ring
  | some i => exact pairedEntries_eq_exponent ι hinv hne a u i

theorem pairedExponent_bound {d : ℕ} (Q B : ℕ) (hQ : 1 ≤ Q)
    (a : Fin d → ℤ) (ha : ∀ i, |a i| ≤ B) (i : Fin d ⊕ Fin d) :
    |pairedExponent Q a i| ≤ (Q : ℤ) * B := by
  have hQz : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  cases i with
  | inl i => have := ha i; simp only [pairedExponent]; nlinarith
  | inr i =>
    simp only [pairedExponent, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℤ) ≤ Q)]
    exact mul_le_mul_of_nonneg_left (ha i) (by positivity)

theorem odd_positiveExponent_bound (d Q : ℕ) (hQ : 1 ≤ Q)
    (i : Option (Fin d ⊕ Fin d)) :
    |oddExponent Q (positiveWeight d) i| ≤ (Q : ℤ) * ((d + 1 : ℕ) : ℤ)^2 := by
  have hQz : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  have hS := weightSum_bounds d
  cases i with
  | none =>
    change |((Q : ℤ) - 1) * weightSum d| ≤ _
    rw [abs_mul, abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
    push_cast at hS ⊢
    nlinarith
  | some i =>
    apply pairedExponent_bound Q ((d + 1)^2) hQ _ _ i
    intro j
    have h := positiveWeight_bounds j
    rw [abs_of_nonneg (by omega)]
    push_cast at h ⊢
    nlinarith

/- Explicit local budget. One full-field unit works before all matrix/root targets.
No union bound or assumed regularity is used: all exponent differences are proved
nonzero, and the generator cannot annihilate an exponent below its order. -/
theorem separated_power_weights {I : Type*} (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (B s : ℕ) (hs : 0 < s)
    (hQ : 2 * s * B + 2 < Nat.card (fixedField ι))
    (b : I → ℤ) (hb : Function.Injective b)
    (hbound : ∀ i, |b i| ≤ (Nat.card (fixedField ι) : ℤ) * B) :
    ∃ u : Fˣ, ∀ i j, i ≠ j → ((u ^ b i / u ^ b j) ^ s : Fˣ) ≠ 1 := by
  obtain ⟨u, hu⟩ := full_unit_simultaneous_avoidance ι hinv hne
  refine ⟨u, fun i j hij hp => ?_⟩
  have hbn : b i - b j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hb h))
  have hsn : (s : ℤ) ≠ 0 := by omega
  have hn : (b i - b j) * (s : ℤ) ≠ 0 := mul_ne_zero hbn hsn
  have hdiff : |b i - b j| ≤ 2 * (Nat.card (fixedField ι) : ℤ) * B := by
    have h := abs_sub (b i) (b j)
    have hi := hbound i
    have hj := hbound j
    linarith
  have hQz : 2 * (s : ℤ) * B + 2 < Nat.card (fixedField ι) := by exact_mod_cast hQ
  have hQ1 : 1 ≤ Nat.card (fixedField ι)^2 := by
    have : 2 ≤ Nat.card (fixedField ι) := Finite.one_lt_card
    nlinarith
  have hl : ((b i - b j) * (s : ℤ)).natAbs < Nat.card (fixedField ι)^2 - 1 := by
    rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℤ) ≤ s), Nat.cast_sub hQ1]
    push_cast
    have hs0 : 0 ≤ (s : ℤ) := by positivity
    have h := mul_le_mul_of_nonneg_right hdiff hs0
    nlinarith
  apply hu _ hn hl
  rw [div_eq_mul_inv, ← zpow_sub, ← zpow_natCast, ← zpow_mul] at hp
  exact hp

theorem regular_even_diagonal (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (m s : ℕ) (hs : 0 < s)
    (hQ : 2 * s * (m + 2)^2 + 2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ,
      adjoint ι (evenDiagonal ι (evenWeight m) (evenWeight_sum m) u).val *
        hermitianForm (pairSwap (m + 2)) *
        (evenDiagonal ι (evenWeight m) (evenWeight_sum m) u).val =
        hermitianForm (pairSwap (m + 2)) ∧
      ∀ i j : Fin (m + 2) ⊕ Fin (m + 2), i ≠ j →
        ((pairedEntries ι (evenWeight m) u i / pairedEntries ι (evenWeight m) u j)^s : Fˣ) ≠ 1 := by
  have hQb : (m + 2)^2 < Nat.card (fixedField ι) := by nlinarith
  have hQ1 : 1 ≤ Nat.card (fixedField ι) := by omega
  obtain ⟨u, hu⟩ := separated_power_weights ι hinv hne ((m + 2)^2) s hs hQ
    (pairedExponent (Nat.card (fixedField ι)) (evenWeight m))
    (pairedExponent_injective _ _ hQb _ (evenWeight_injective m)
      (evenWeight_nonzero m) (evenWeight_bound m))
    (pairedExponent_bound _ _ hQ1 _ (evenWeight_bound m))
  exact ⟨u, evenDiagonal_unitary ι hinv _ _ u, by
    simpa only [pairedEntries_eq_exponent ι hinv hne] using hu⟩

theorem regular_odd_diagonal (ι : F ≃+* F)
    (hinv : Function.Involutive ι) (hne : ι ≠ RingEquiv.refl F)
    (d s : ℕ) (hd : 0 < d) (hs : 0 < s)
    (hQ : 2 * s * (d + 1)^2 + 2 < Nat.card (fixedField ι)) :
    ∃ u : Fˣ,
      adjoint ι (oddDiagonal ι (positiveWeight d) u).val * hermitianForm (oddSwap d) *
        (oddDiagonal ι (positiveWeight d) u).val = hermitianForm (oddSwap d) ∧
      ((oddEntries ι (positiveWeight d) u none : Fˣ) : F) *
        ι ((oddEntries ι (positiveWeight d) u none : Fˣ) : F) = 1 ∧
      ∀ i j : Option (Fin d ⊕ Fin d), i ≠ j →
        ((oddEntries ι (positiveWeight d) u i / oddEntries ι (positiveWeight d) u j)^s : Fˣ) ≠ 1 := by
  have hQ2 : 2 < Nat.card (fixedField ι) := by nlinarith
  obtain ⟨u, hu⟩ := separated_power_weights ι hinv hne ((d + 1)^2) s hs hQ
    (oddExponent (Nat.card (fixedField ι)) (positiveWeight d))
    (odd_positiveExponent_injective hd _ hQ2)
    (odd_positiveExponent_bound d _ (by omega))
  refine ⟨u, oddDiagonal_unitary ι hinv _ u, ?_, ?_⟩
  · have hn := norm_one_correction ι hinv u
    have hnunit : (u / involutionUnit ι u) ∈ normOne ι :=
      (mem_normOne ι hinv hne _).mpr hn
    exact (mem_normOne ι hinv hne _).mp
      ((normOne ι).zpow_mem hnunit (-(∑ i, positiveWeight d i)))
  · simpa only [oddEntries_eq_exponent ι hinv hne] using hu

end NikolovSegal.UnitaryField
