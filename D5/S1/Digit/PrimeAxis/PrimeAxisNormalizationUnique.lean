/- GID: D5/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/PrimeAxisNormalizationUnique
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prime-axis addition has a unique normalization whose decoder is multiplication. -/

import D5.S1.Digit.PrimeAxisAddition

namespace D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique

open D5.S1.Digit

private theorem primeAxisTable_eq_of_digits_eq {a b : PrimeAxisTable}
    (h : a.digits = b.digits) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- After rowwise addition, there is exactly one canonical prime-axis table with
the summed exponent on every axis, and decoding that table is multiplication. -/
theorem normalized_prime_axis_add_unique (z w : PrimeAxisTable) :
    ∃! result : PrimeAxisTable,
      (forall p,
        CanonicalRaw (result.digits p) /\
          rawValue (result.digits p) =
            rawValue (z.digits p) + rawValue (w.digits p)) /\
        decodePrimeAxisTable result =
          decodePrimeAxisTable z * decodePrimeAxisTable w := by
  have haxis (p : PrimeAxis) :
      CanonicalRaw ((normalizedPrimeAxisAdd z w).digits p) /\
        rawValue ((normalizedPrimeAxisAdd z w).digits p) =
          rawValue (z.digits p) + rawValue (w.digits p) := by
    refine ⟨(normalizedPrimeAxisAdd z w).canonical p, ?_⟩
    change rawValue (normalize ((z.digits + w.digits) p)) = _
    rw [rawValue_normalize]
    simpa using rawValue_add (z.digits p) (w.digits p)
  refine ⟨normalizedPrimeAxisAdd z w,
    ⟨haxis, (prime_axis_addition_spec z w).2⟩, ?_⟩
  intro result hresult
  apply primeAxisTable_eq_of_digits_eq
  apply Finsupp.ext
  intro p
  apply canonicalRaw_unique (hresult.1 p).1
    ((normalizedPrimeAxisAdd z w).canonical p)
  exact (hresult.1 p).2.trans (haxis p).2.symm

private def emptyPrimeAxisTable : PrimeAxisTable where
  digits := 0
  canonical := by simp [CanonicalRaw]

/-- Checked evidence that the quantified table domain is inhabited. -/
example : PrimeAxisTable := emptyPrimeAxisTable

/-- Checked concrete instance of the unique-normalization conclusion. -/
example :
    ∃! result : PrimeAxisTable,
      (forall p,
        CanonicalRaw (result.digits p) /\
          rawValue (result.digits p) =
            rawValue (emptyPrimeAxisTable.digits p) +
              rawValue (emptyPrimeAxisTable.digits p)) /\
        decodePrimeAxisTable result =
          decodePrimeAxisTable emptyPrimeAxisTable *
            decodePrimeAxisTable emptyPrimeAxisTable :=
  normalized_prime_axis_add_unique emptyPrimeAxisTable emptyPrimeAxisTable

end D5.S1.Digit.PrimeAxis.PrimeAxisNormalizationUnique
