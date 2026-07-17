/- GID: D5/S1/Digit/PrimeAxisAddition
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxisAddition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rowwise W normalization turns prime-axis table addition into multiplication. -/

import D5.S1.Digit.PrimeAxisEncoding

namespace D5.S1.Digit

private theorem normalize_zero : normalize (0 : RawDigits) = 0 := by
  apply normalize_eq_of_canonical
  simp [CanonicalRaw]

private theorem rawValue_zero : rawValue (0 : RawDigits) = 0 := by
  exact Finsupp.sum_zero_index

/-- Rowwise raw addition followed by the existing local W normalizer. -/
noncomputable def normalizedPrimeAxisAdd (z w : PrimeAxisTable) : PrimeAxisTable :=
  { digits := (z.digits + w.digits).mapRange normalize normalize_zero
    canonical := fun p => by
      change CanonicalRaw (normalize ((z.digits + w.digits) p))
      exact normalize_canonical _ }

/-- Decoder multiplicativity for actual rowwise addition and W normalization. -/
theorem prime_axis_addition_spec (z w : PrimeAxisTable) :
    Function.Bijective primeAxisEncoding ∧
      decodePrimeAxisTable (normalizedPrimeAxisAdd z w) =
        decodePrimeAxisTable z * decodePrimeAxisTable w := by
  refine ⟨primeAxisEncoding.bijective, ?_⟩
  change ((z.digits + w.digits).mapRange normalize normalize_zero).prod
      (fun p row => (p : ℕ) ^ rawValue row) =
    z.digits.prod (fun p row => (p : ℕ) ^ rawValue row) *
      w.digits.prod (fun p row => (p : ℕ) ^ rawValue row)
  rw [Finsupp.prod_mapRange_index (fun _ => by rw [rawValue_zero, pow_zero])]
  simp_rw [rawValue_normalize]
  apply Finsupp.prod_add_index'
  · intro p
    rw [rawValue_zero, pow_zero]
  · intro p r s
    rw [rawValue_add, Nat.pow_add]

end D5.S1.Digit
