/- GID: D5/S0/Computability/OriginalClauseLanguages
   generality: G
   mirror-B: D5/B/S0/Computability/OriginalClauseLanguages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact original guarded SAT, guarded UNSAT and their ordered binary pair language. -/

import D5.S0.Computability.UnrestrictedClauseWords
import D5.S0.Computability.BinaryMachine.StackPair

set_option autoImplicit false
namespace PredictiveThermodynamic.OriginalClasses
open Conventional
open Complexity (Word pairWords)

/-- Well-formedness is the exact unrestricted original decoder's domain. -/
def W (w : Word) : Prop := ∃ F, Unrestricted.readWord w = some F

/-- The only SAT premise is on these original bytes and appearing-name semantics. -/
def S (w : Word) : Prop :=
  ∃ F, Unrestricted.readWord w = some F ∧ ∃ a : Appearing F → Bool, evaluate F a = true

/-- Malformed strings belong to neither guarded language. -/
def U (w : Word) : Prop := W w ∧ ¬ S w

/-- The UNSAT component is first. Both components retain their original bytes. -/
def Q (w : Word) : Prop := ∃ u v, w = pairWords u v ∧ U u ∧ S v

def trueWord : Word := formulaWord []
def falseWord : Word := formulaWord [.empty]

def repair (fallback w : Word) : Word := if (Unrestricted.readWord w).isSome then w else fallback

private theorem read_true : Unrestricted.readWord trueWord = some [] :=
  (Unrestricted.word_codec trueWord []).mpr ⟨by simp [Unrestricted.Canonical], rfl⟩
private theorem read_false : Unrestricted.readWord falseWord = some [.empty] :=
  (Unrestricted.word_codec falseWord [.empty]).mpr ⟨by simp [Unrestricted.Canonical], rfl⟩
private theorem sat_true : S trueWord := ⟨[], read_true, (fun _ => false), rfl⟩
private theorem not_sat_false : ¬ S falseWord := by
  rintro ⟨F, hF, a, ha⟩
  have h : F = [.empty] := Option.some.inj (hF.symm.trans read_false)
  subst F
  simp [evaluate, Std.Sat.CNF.Clause.eval] at ha

/-- The two fallback directions differ. False repair preserves SAT and always
returns a valid original formula. True repair converts guarded UNSAT exactly to
complement-SAT, rejecting every malformed original input. -/
theorem repair_laws (w : Word) :
    W (repair falseWord w) ∧ (S (repair falseWord w) ↔ S w) ∧
      (U w ↔ ¬ S (repair trueWord w)) ∧
      (W w → repair falseWord w = w ∧ repair trueWord w = w) := by
  cases hr : Unrestricted.readWord w with
  | none =>
    have hnW : ¬ W w := by rintro ⟨F,hF⟩; simp [hr] at hF
    have hnS : ¬ S w := by rintro ⟨F,hF,_⟩; simp [hr] at hF
    simp [repair, hr, U, hnW, hnS, not_sat_false, sat_true]
    exact ⟨[.empty], read_false⟩
  | some F =>
    have hw : W w := ⟨F, hr⟩
    simp [repair, hr, U, hw]

/-- The ordered pair has an exact all-word decoder, so malformed outer words
cannot enter the language. This equivalence imposes no restriction on payloads. -/
theorem pair_language (w : Word) :
    Q w ↔ ∃ u v, Complexity.StackPair.decodePair w = some (u, v) ∧ U u ∧ S v := by
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨u,v,(Complexity.StackPair.decodePair_eq_some_iff w u v).mpr he,hu,hv⟩
  · rintro ⟨u,v,he,hu,hv⟩
    exact ⟨u,v,(Complexity.StackPair.decodePair_eq_some_iff w u v).mp he,hu,hv⟩

end PredictiveThermodynamic.OriginalClasses
