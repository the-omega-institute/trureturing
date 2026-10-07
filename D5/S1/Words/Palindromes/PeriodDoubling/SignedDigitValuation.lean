/- GID: D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitValuation
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/SignedDigitValuation
   mirror-E: none(waiver:literal-lowest-signed-digit-valuation)
   anchors: []
   utility: none
   digest: The lowest nonzero signed binary coefficient gives the exact dyadic valuation. -/

/-
proof_shape: content (signed_digits_lowest_valuation)
escape_witness: Digit induction peels the zero prefix and proves the odd signed residual is nonzero.
admission_basis: escape-witness
Direct frozen dependencies: none.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

theorem signed_digits_lowest_valuation (ds : List ℤ) (k : ℕ)
    (hzero : ∀ i : ℕ, i < k → ds[i]?.getD 0=0)
    (hcoeff : ds[k]?.getD 0=-1 ∨ ds[k]?.getD 0=1) :
    padicValInt 2 (ds.foldr (fun z x => z+2*x) 0)=k := by
  haveI : Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
  induction k generalizing ds with
  | zero =>
    cases ds with
    | nil => simp at hcoeff
    | cons d ds =>
      have hd : d=-1 ∨ d=1 := by simpa using hcoeff
      have hnd : ¬(2:ℤ) ∣ d+2*ds.foldr (fun z x => z+2*x) 0 := by
        rintro ⟨x,hx⟩
        rcases hd with hd | hd <;> omega
      exact padicValInt.eq_zero_of_not_dvd hnd
  | succ k ih =>
    cases ds with
    | nil => simp at hcoeff
    | cons d ds =>
      have hd : d=0 := by simpa using hzero 0 (by omega)
      have hz : ∀ i : ℕ, i < k → ds[i]?.getD 0=0 := by
        intro i hi
        simpa using hzero (i+1) (by omega)
      have hc : ds[k]?.getD 0=-1 ∨ ds[k]?.getD 0=1 := by simpa using hcoeff
      have ht:=ih ds hz hc
      have hne : ds.foldr (fun z x => z+2*x) 0 ≠ 0 := by
        intro he
        have nz (ds : List ℤ) (k : ℕ)
            (hz : ∀ i : ℕ, i < k → ds[i]?.getD 0=0)
            (hc : ds[k]?.getD 0=-1 ∨ ds[k]?.getD 0=1) :
            ds.foldr (fun z x => z+2*x) 0 ≠ 0 := by
          induction k generalizing ds with
          | zero =>
            cases ds with
            | nil => simp at hc
            | cons d ds =>
              have hh : d=-1 ∨ d=1 := by simpa using hc
              simp only [List.foldr_cons]
              rcases hh with hh | hh <;> omega
          | succ k ih =>
            cases ds with
            | nil => simp at hc
            | cons d ds =>
              have hd : d=0 := by simpa using hz 0 (by omega)
              have hh:=ih ds (fun i hi => by simpa using hz (i+1) (by omega)) (by simpa using hc)
              simp only [List.foldr_cons,hd,zero_add]
              exact mul_ne_zero (by decide) hh
        exact nz ds k hz hc he
      simp only [List.foldr_cons,hd,zero_add]
      calc
        _ = padicValInt 2 (ds.foldr (fun z x => z+2*x) 0 * (2:ℕ)) := by congr 1;exact mul_comm _ _
        _ = padicValInt 2 (ds.foldr (fun z x => z+2*x) 0)+1 := padicValInt_mul_eq_succ (p:=2) _ hne
        _ = k+1 := by rw [ht]

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.signed_digits_lowest_valuation
