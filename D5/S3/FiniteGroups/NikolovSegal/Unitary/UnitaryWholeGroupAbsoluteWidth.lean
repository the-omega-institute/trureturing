/- GID: D5/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/Unitary/UnitaryWholeGroupAbsoluteWidth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual unitary matrix geometry and ordered whole-group products, preserving every field and rank hypothesis. -/

import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthFiveAbsorption
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthRankThree
import D5.S3.FiniteGroups.NikolovSegal.Unitary.UnitaryWidthTrivialRanks

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

/-- Literal ordered-factor endpoint, with five genuine alternating SU factors. -/
theorem alternating_five (hinv : Function.Involutive ι) (hne : ι≠RingEquiv.refl F)
    (n : ℕ) (g : specialUnitary n ι) :
    ∃ a : Fin 5 → specialUnitary n ι,
      (∀ j, if j.val % 2=0 then
        ∀ r c : Fin n, c.val < r.val+1 → ((a j).val.val-1) r c=0
      else ∀ r c : Fin n, r.val < c.val+1 → ((a j).val.val-1) r c=0) ∧
      (List.ofFn a).prod=g := by
  obtain ⟨a,b,c,d,e,ha,hb,hc,hd,he,hprod⟩ := five_factor hinv hne n g
  let f : Fin 5 → specialUnitary n ι := ![a,b,c,d,e]
  refine ⟨f,?_,?_⟩
  · intro j
    fin_cases j
    all_goals first | exact ha | exact hb | exact hc | exact hd | exact he
  · simpa [f,List.ofFn_succ,mul_assoc] using hprod

/-- ONE positive absolute length BEFORE every field, rank, involution and target.
All factors belong to the SAME literal determinant-one Hermitian SU carrier. -/
theorem exists_absolute_unitriangular_width :
    ∃ K : ℕ, 0 < K ∧ ∀ (F : Type u) [Field F] [Finite F], ∀ n : ℕ,
      ∀ (ι : RingAut F), Function.Involutive ι → ι≠RingEquiv.refl F →
      ∀ g : specialUnitary n ι,
      ∃ a : Fin K → specialUnitary n ι,
        (∀ j, if j.val % 2=0 then
          ∀ r c : Fin n, c.val < r.val+1 → ((a j).val.val-1) r c=0
        else ∀ r c : Fin n, r.val < c.val+1 → ((a j).val.val-1) r c=0) ∧
        (List.ofFn a).prod=g := by
  refine ⟨5,by decide,?_⟩
  intro F _ _ n ι hinv hne g
  exact alternating_five hinv hne n g

end NikolovSegal.UnitaryWholeGroupWidth
