/- GID: D5/S1/Digit/PrimeAxis/ChargedTableNormalization
   generality: I
   mirror-B: D5/B/S1/Digit/PrimeAxis/ChargedTableNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite sequences of charged carries normalize every finitely supported prime-indexed raw table. -/

import D5.S1.Deficit.ChargedCarryPath
import D5.S1.Digit.PrimeAxisTable

set_option autoImplicit false

namespace D5.S1.Digit.PrimeAxis.ChargedTableNormalization

open D5.S1.Deficit

/-- One charged carry changes the selected prime row and leaves every other row unchanged. -/
def TableStep (r r' : PrimeAxis →₀ RawDigits) (p : PrimeAxis) (z : ℤ) : Prop :=
  ChargedCarryStep (r p) (r' p) z ∧ ∀ q, q ≠ p → r' q = r q

/-- A finite sequence of actual table carries records its total charge at each prime. -/
inductive TablePath : (PrimeAxis →₀ RawDigits) → (PrimeAxis →₀ RawDigits) →
    (PrimeAxis →₀ ℤ) → Prop
  /-- The empty path leaves the table unchanged and has zero charge at every prime. -/
  | refl (r : PrimeAxis →₀ RawDigits) : TablePath r r 0
  /-- Appending a carry adds its integer charge only at the prime row on which it acts. -/
  | tail {r s t : PrimeAxis →₀ RawDigits} {charge : PrimeAxis →₀ ℤ}
      {p : PrimeAxis} {z : ℤ} :
      TablePath r s charge → TableStep s t p z →
      TablePath r t (charge + Finsupp.single p z)

/-- Normalize each raw row; the zero row remains zero, so the resulting table has finite support. -/
noncomputable def rowNormalize (r : PrimeAxis →₀ RawDigits) : PrimeAxis →₀ RawDigits :=
  r.mapRange normalize (by
    apply normalize_eq_of_canonical
    simp [CanonicalRaw])

/-- Every finitely supported raw prime table reaches its rowwise normal form by one finite
sequence of single-row carries, with a finitely supported charge indexed by primes. -/
theorem exists_tablePath_rowNormalize (r : PrimeAxis →₀ RawDigits) :
    ∃ charge : PrimeAxis →₀ ℤ, TablePath r (rowNormalize r) charge := by
  classical
  have lift (t : PrimeAxis →₀ RawDigits) (p : PrimeAxis)
      {a b : RawDigits} {z : ℤ} (h : ChargedReduces a b z) :
      TablePath (t.update p a) (t.update p b) (Finsupp.single p z) := by
    induction h with
    | refl => simpa using TablePath.refl (t.update p a)
    | tail _ step ih =>
        rw [Finsupp.single_add]
        apply TablePath.tail ih
        refine ⟨?_, ?_⟩
        · simpa [Finsupp.update_apply] using step
        · intro q hq
          simp [Finsupp.update_apply, hq]
  have concat {a b c : PrimeAxis →₀ RawDigits} {z w : PrimeAxis →₀ ℤ}
      (hab : TablePath a b z) (hbc : TablePath b c w) :
      TablePath a c (z + w) := by
    induction hbc with
    | refl => simpa using hab
    | tail _ step ih => simpa [add_assoc] using TablePath.tail ih step
  have assemble (s : Finset PrimeAxis) :
      ∀ t : PrimeAxis →₀ RawDigits, (∀ p, p ∉ s → CanonicalRaw (t p)) →
        ∃ c : PrimeAxis →₀ ℤ, TablePath t (rowNormalize t) c := by
    induction s using Finset.induction_on with
    | empty =>
        intro t ht
        have hn : rowNormalize t = t := by
          apply Finsupp.ext
          intro p
          exact normalize_eq_of_canonical (ht p (by simp))
        rw [hn]
        exact ⟨0, TablePath.refl t⟩
    | @insert p s _ ih =>
        intro t ht
        let u := t.update p (normalize (t p))
        have htu : TablePath t u (Finsupp.single p (carrySignedCount (t p))) := by
          simpa [u] using lift t p (charged_normalize_exists (t p))
        have hu : ∀ q, q ∉ s → CanonicalRaw (u q) := by
          intro q hq
          by_cases hqp : q = p
          · subst q
            simpa [u, Finsupp.update_apply] using normalize_canonical (t p)
          · simpa [u, Finsupp.update_apply, hqp] using ht q (by simp [hqp, hq])
        obtain ⟨c, hc⟩ := ih u hu
        have hn : rowNormalize u = rowNormalize t := by
          apply Finsupp.ext
          intro q
          by_cases hqp : q = p
          · subst q
            simpa [rowNormalize, u, Finsupp.update_apply] using
              normalize_eq_of_canonical (normalize_canonical (t p))
          · simp [rowNormalize, u, Finsupp.update_apply, hqp]
        refine ⟨Finsupp.single p (carrySignedCount (t p)) + c, ?_⟩
        rw [← hn]
        exact concat htu hc
  apply assemble r.support r
  intro p hp
  rw [Finsupp.notMem_support_iff.mp hp]
  simp [CanonicalRaw]

/-- Restricting a finite table path to one prime gives a charged raw-row reduction
with exactly the charge recorded at that prime. -/
theorem tablePath_project {r r' : PrimeAxis →₀ RawDigits} {charge : PrimeAxis →₀ ℤ}
    (h : TablePath r r' charge) (p : PrimeAxis) :
    ChargedReduces (r p) (r' p) (charge p) := by
  classical
  induction h with
  | refl => simpa using ChargedReduces.refl (r p)
  | @tail s t c q z _ step ih =>
      by_cases hpq : p = q
      · subst q
        simpa using ChargedReduces.tail ih step.1
      · simpa [Finsupp.single_apply, hpq, step.2 p hpq] using ih

end D5.S1.Digit.PrimeAxis.ChargedTableNormalization
