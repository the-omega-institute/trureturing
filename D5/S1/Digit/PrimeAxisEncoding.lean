/- GID: D5/S1/Digit/PrimeAxisEncoding
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxisEncoding
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Prime-axis W tables encode positive naturals and multiply by normalized addition. -/

import D5.S1.Digit.Normalize
import D5.S1.Digit.PrimeAxisTable
import Mathlib.Data.Nat.Factorization.Basic

namespace D5.S1.Digit

open D5.S0.Conventions

instance canonicalRawDigitsZero : Zero CanonicalRawDigits where
  zero := ⟨0, by simp [CanonicalRaw]⟩

/-- A canonical W row is equivalent to the natural exponent that it represents. -/
noncomputable def canonicalRawValueEquiv : CanonicalRawDigits ≃ ℕ where
  toFun row := rawValue row
  invFun n :=
    ⟨rawOfZeckendorf (Nat.zeckendorf n),
      canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf n)⟩
  left_inv row := by
    apply Subtype.ext
    apply canonicalRaw_unique
      (canonicalRaw_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf _)) row.property
    rw [rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf _),
      Nat.sum_zeckendorf_fib]
  right_inv n := by
    change rawValue (rawOfZeckendorf (Nat.zeckendorf n)) = n
    rw [rawValue_rawOfZeckendorf (Nat.isZeckendorfRep_zeckendorf _),
      Nat.sum_zeckendorf_fib]

@[simp] theorem canonicalRawValueEquiv_zero : canonicalRawValueEquiv 0 = 0 := by
  change rawValue (0 : RawDigits) = 0
  exact Finsupp.sum_zero_index

/-- Package every canonical row of a table as a subtype value. -/
noncomputable def tableRows (z : PrimeAxisTable) : PrimeAxis →₀ CanonicalRawDigits where
  support := z.digits.support
  toFun p := ⟨z.digits p, z.canonical p⟩
  mem_support_toFun p := by
    rw [Finsupp.mem_support_iff]
    constructor
    · intro h hsubtype
      apply h
      exact congrArg Subtype.val hsubtype
    · intro h hraw
      apply h
      exact Subtype.ext hraw

/-- Forget row proofs while preserving the finite prime support. -/
noncomputable def rowsToTable (rows : PrimeAxis →₀ CanonicalRawDigits) :
    PrimeAxisTable where
  digits := rows.mapRange Subtype.val rfl
  canonical p := (rows p).property

private theorem primeAxisTable_ext {z w : PrimeAxisTable}
    (h : z.digits = w.digits) : z = w := by
  cases z
  cases w
  cases h
  rfl

/-- Prime-axis tables are finitely supported families of canonical rows. -/
noncomputable def tableRowsEquiv :
    PrimeAxisTable ≃ (PrimeAxis →₀ CanonicalRawDigits) where
  toFun := tableRows
  invFun := rowsToTable
  left_inv z := by
    apply primeAxisTable_ext
    ext p
    rfl
  right_inv rows := by
    ext p
    rfl

/-- Forget the primality proof attached to a prime axis. -/
def primeAxisEmbedding : PrimeAxis ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩

/-- Natural exponent tables whose finite support consists only of primes. -/
abbrev PrimeExponentTable :=
  {f : ℕ →₀ ℕ // ∀ p ∈ f.support, Nat.Prime p}

/-- Restrict a prime-supported natural table to the prime subtype. -/
noncomputable def primeSupportEquiv : PrimeExponentTable ≃ (PrimeAxis →₀ ℕ) where
  toFun f := Finsupp.comapDomain primeAxisEmbedding f.1
    primeAxisEmbedding.injective.injOn
  invFun rows := ⟨rows.embDomain primeAxisEmbedding, by
    intro p hp
    rw [Finsupp.support_embDomain] at hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.1 hp
    exact q.property⟩
  left_inv f := by
    apply Subtype.ext
    exact Finsupp.embDomain_comapDomain fun p hp ↦
      ⟨⟨p, f.property p hp⟩, rfl⟩
  right_inv rows := Finsupp.comapDomain_embDomain primeAxisEmbedding rows

/-- Canonical W tables, prime factorizations, and positive naturals are the same data. -/
noncomputable def primeAxisEncoding : PrimeAxisTable ≃ ℕ+ :=
  tableRowsEquiv |>.trans
    (Finsupp.mapRange.equiv canonicalRawValueEquiv canonicalRawValueEquiv_zero) |>.trans
    primeSupportEquiv.symm |>.trans Nat.factorizationEquiv.symm

/-- The equivalence value agrees with the finite prime-power decoder. -/
theorem primeAxisEncoding_coe (z : PrimeAxisTable) :
    ((primeAxisEncoding z : ℕ+) : ℕ) = decodePrimeAxisTable z := by
  change ((Nat.factorizationEquiv.symm
    (primeSupportEquiv.symm
      ((Finsupp.mapRange.equiv canonicalRawValueEquiv
        canonicalRawValueEquiv_zero) (tableRowsEquiv z))) : ℕ+) : ℕ) = _
  change (primeSupportEquiv.symm
    ((Finsupp.mapRange.equiv canonicalRawValueEquiv
      canonicalRawValueEquiv_zero) (tableRowsEquiv z))).1.prod
        (fun p exponent ↦ p ^ exponent) = _
  change (((Finsupp.mapRange.equiv canonicalRawValueEquiv
    canonicalRawValueEquiv_zero) (tableRowsEquiv z)).embDomain
      primeAxisEmbedding).prod (fun p exponent ↦ p ^ exponent) = _
  rw [Finsupp.prod_embDomain]
  change ((tableRowsEquiv z).mapRange canonicalRawValueEquiv
    canonicalRawValueEquiv_zero).prod
      (fun p exponent ↦ (p : ℕ) ^ exponent) = _
  rw [Finsupp.prod_mapRange_index (by simp)]
  rfl

/-- Normalize table addition by transporting multiplication through the encoding. -/
noncomputable def normalizedTableAdd (z w : PrimeAxisTable) : PrimeAxisTable :=
  primeAxisEncoding.symm (primeAxisEncoding z * primeAxisEncoding w)

/-- Exact formal echo of bijectivity and multiplicative normalized addition. -/
theorem prime_axis_encoding_spec (z w : PrimeAxisTable) :
    Function.Bijective primeAxisEncoding ∧
      ((primeAxisEncoding z : ℕ+) : ℕ) = decodePrimeAxisTable z ∧
      decodePrimeAxisTable (normalizedTableAdd z w) =
        decodePrimeAxisTable z * decodePrimeAxisTable w := by
  refine ⟨primeAxisEncoding.bijective, primeAxisEncoding_coe z, ?_⟩
  rw [← primeAxisEncoding_coe (normalizedTableAdd z w),
    ← primeAxisEncoding_coe z, ← primeAxisEncoding_coe w]
  simp [normalizedTableAdd]

end D5.S1.Digit
