/- GID: D5/S1/Words/Powers/GoldenDesubstitutionNormalForm
   generality: I
   mirror-B: D5/B/S1/Words/Powers/GoldenDesubstitutionNormalForm
   mirror-E: none(waiver:block-boundary-bookkeeping)
   anchors: []
   digest: Iterated golden desubstitution has a unique terminal index. -/

import D5.S0.Rewriting.Newman
import D5.S1.Words.Powers.GoldenDesubstitution

namespace GoldenDesubstitutionNormalForm

open D5.S1.Words
open D5.S1.Words.Powers

/-- One golden desubstitution step sends a nonzero block boundary to its source index. -/
def desubStep (x y : Nat) : Prop :=
  x ≠ 0 ∧ goldenSubstStart y = x

/-- Every golden desubstitution step strictly decreases the index. -/
theorem desubStep_lt {x y : Nat} (h : desubStep x y) : y < x := by
  rcases h with ⟨hx, hstart⟩
  have hy : 0 < y := by
    by_contra hnot
    have hy0 : y = 0 := Nat.eq_zero_of_not_pos hnot
    subst y
    rw [goldenSubstStart_zero] at hstart
    exact hx hstart.symm
  have hcount : 0 < goldenWindowTrueCount 0 y := by
    rw [goldenWindowTrueCount, Finset.card_pos]
    exact ⟨0, by simp [hy, goldenWord_zero]⟩
  rw [← hstart, goldenSubstStart]
  omega

/-- Strict index descent makes golden desubstitution terminating. -/
theorem desubStep_termination : WellFounded (Function.swap desubStep) := by
  refine Subrelation.wf (q := Function.swap desubStep) (r := (· < ·)) ?_ Nat.lt_wfRel.wf
  intro a b hab
  exact desubStep_lt hab

/-- A block boundary has at most one golden desubstitution source. -/
theorem desubStep_deterministic {x y z : Nat}
    (hy : desubStep x y) (hz : desubStep x z) : y = z :=
  goldenSubstStart_strictMono.injective (hy.2.trans hz.2.symm)

/-- Determinism gives local confluence in one reflexive join. -/
theorem desubStep_localConfluence :
    ∀ h a b, desubStep h a → desubStep h b →
      ∃ c, Relation.ReflTransGen desubStep a c ∧ Relation.ReflTransGen desubStep b c := by
  intro h a b ha hb
  have hab : a = b := desubStep_deterministic ha hb
  subst b
  exact ⟨a, .refl, .refl⟩

/-- The terminal indices are zero and exactly the false positions of the golden word. -/
theorem desubStep_irreducible_iff (m : Nat) :
    (¬ ∃ x, desubStep m x) ↔ m = 0 ∨ goldenWord m = false := by
  constructor
  · intro hirreducible
    by_cases hm : m = 0
    · exact Or.inl hm
    · cases hword : goldenWord m with
      | false => exact Or.inr rfl
      | true =>
          obtain ⟨k, hk⟩ := exists_goldenSubstStart_of_true hword
          exact False.elim (hirreducible ⟨k, hm, hk⟩)
  · intro hterminal
    rintro ⟨x, hx⟩
    rcases hterminal with hm | hfalse
    · exact hx.1 hm
    · have htrue := goldenWord_goldenSubstStart x
      rw [hx.2, hfalse] at htrue
      exact Bool.noConfusion htrue

/-- Every index has a unique terminal reached by iterated golden desubstitution. -/
theorem golden_desubstitution_unique_terminal (n : Nat) :
    ∃! m, Relation.ReflTransGen desubStep n m ∧ (m = 0 ∨ goldenWord m = false) := by
  obtain ⟨m, hm, hunique⟩ :=
    newman_unique_normal_form desubStep desubStep_termination desubStep_localConfluence n
  refine ⟨m, ⟨hm.1, (desubStep_irreducible_iff m).mp hm.2⟩, ?_⟩
  intro y hy
  exact hunique y ⟨hy.1, (desubStep_irreducible_iff y).mpr hy.2⟩

private theorem goldenWord_one : goldenWord 1 = false := by
  simpa [goldenSubstStart_zero, goldenWord_zero] using goldenWord_goldenSubstStart_succ 0

/-- The unique terminal reached from block boundary `2` is source index `1`. -/
example : ∀ m, Relation.ReflTransGen desubStep 2 m →
    (m = 0 ∨ goldenWord m = false) → m = 1 := by
  intro m hpath hterminal
  obtain ⟨u, _, hunique⟩ := golden_desubstitution_unique_terminal 2
  have hstart : goldenSubstStart 1 = 2 := by
    simpa [goldenSubstStart_zero] using goldenSubstStart_step_true goldenWord_zero
  have hone : Relation.ReflTransGen desubStep 2 1 ∧ (1 = 0 ∨ goldenWord 1 = false) :=
    ⟨.single ⟨by omega, hstart⟩, Or.inr goldenWord_one⟩
  have hm : m = u := hunique m ⟨hpath, hterminal⟩
  have hone' : 1 = u := hunique 1 hone
  exact hm.trans hone'.symm

#print axioms golden_desubstitution_unique_terminal

end GoldenDesubstitutionNormalForm
