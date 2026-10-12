/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthFiveAbsorption
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRankThree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Whole special-unitary width: exactly FIVE alternating actual unitriangular
factors. The invariant is absorbed through genuine Hermitian central Levi
reduction, so the bound is absolute, rather than linear in rank. -/
namespace NikolovSegal.UnitaryWholeGroupWidth
open Matrix UnitarySylow
universe u
variable {F : Type u} [Field F] [Finite F] {ι : RingAut F}

private theorem five_of_four {n : ℕ} {g : specialUnitary n ι}
    (hh : ∃ a b c d : specialUnitary n ι,
      Positive a ∧ Negative b ∧ Positive c ∧ Negative d ∧ a*b*c*d=g) : FiveFactor g := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,heq⟩ := hh
  exact ⟨a,b,c,d,1,ha,hb,hc,hd,positive_one,by simpa using heq⟩

/-- Every rank, including zero/one, every finite quadratic field, and every
actual SU target. There is no supplied generation or factorization premise. -/
theorem five_factor (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (n : ℕ) (g : specialUnitary n ι) : FiveFactor g := by
  have hall : ∀ n, ∀ g : specialUnitary n ι, FiveFactor g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g
      by_cases hn : n < 4
      · interval_cases n
        · exact five_of_four (trivial_four_factor g)
        · exact five_of_four (trivial_four_factor g)
        · exact five_of_four (rankTwo_four_factor hinv hne g)
        · exact five_of_four (rankThree_four_factor hinv hne g)
      · obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
        obtain ⟨B,r0,r1,r2,r3,r4,h0,h1,h2,h3,h4,heq⟩ := higher_rank_five_radicals hinv hne g
        rw [←heq]
        exact five_factor_absorb (ih (k+2) (by omega) B) h0 h1 h2 h3 h4
  exact hall n g

end NikolovSegal.UnitaryWholeGroupWidth
