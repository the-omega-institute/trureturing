/- GID: D5/S3/ArithUnits/FiniteWindowResidues
   generality: G
   mirror-B: D5/B/S3/ArithUnits/FiniteWindowResidues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every finite coprime residue window has a bounded simultaneous representative. -/

import Mathlib.Data.Nat.ChineseRemainder

/- Provenance: thin honest wrapper over pinned mathlib's finite Chinese
   remainder constructor (`Nat.chineseRemainderOfFinset`) and its canonical
   product bound (`Nat.chineseRemainderOfFinset_lt_prod`). -/

namespace D5.S3.ArithUnits.FiniteWindowResidues

open scoped Function

/-- Every assignment of target residues on a finite, pairwise-coprime window
is realized simultaneously by a natural number below the product period. -/
theorem finite_window_residues_realizable {ι : Type*}
    (target modulus : ι → ℕ) (window : Finset ι)
    (hmodulus : ∀ i ∈ window, modulus i ≠ 0)
    (hcoprime : Set.Pairwise window (Nat.Coprime on modulus)) :
    ∃ n < ∏ i ∈ window, modulus i,
      ∀ i ∈ window, n ≡ target i [MOD modulus i] := by
  let n := Nat.chineseRemainderOfFinset target modulus window hmodulus hcoprime
  exact ⟨n, Nat.chineseRemainderOfFinset_lt_prod target modulus hmodulus hcoprime,
    n.property⟩

end D5.S3.ArithUnits.FiniteWindowResidues
