/- GID: D5/S0/Computability/OriginalClauseClassification
   generality: G
   mirror-B: D5/B/S0/Computability/OriginalClauseClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original guarded UNSAT and ordered UNSAT-SAT are conditionally complete in one concrete binary model. -/

import D5.S0.Computability.OriginalClauseGuard
import D5.S0.Computability.OriginalPairLanguages
import D5.S0.Computability.BinaryMachine.NPPreimage
import D5.S0.Computability.BinaryMachine.TransducerPair

set_option autoImplicit false
namespace PredictiveThermodynamic.OriginalGuard
open Complexity

/-- The finite lexical control recognizes exactly the unrestricted decoder's
original domain, including every malformed and empty boundary. -/
private theorem valid_iff (w : Word) :
    valid w = (Unrestricted.readWord w).isSome := by
  have hp := Unrestricted.phase_scan (.body []) w
  cases hq : Unrestricted.scan (.body []) w <;>
    simp [Unrestricted.readWord,Unrestricted.finish,hq,Unrestricted.phase] at hp ⊢ <;>
    simp [valid,← hp]

end PredictiveThermodynamic.OriginalGuard

namespace PredictiveThermodynamic.OriginalClasses
open Complexity

/-- The concrete scanner's exact bytes implement the original decoder repair. -/
private theorem polyTime_repair (fallback : Word) : PolyTime (repair fallback) := by
  apply polyTime_congr (f := OriginalGuard.repair fallback)
    (fun w => ?_) (OriginalGuard.polyTime_repair fallback)
  simp [OriginalGuard.repair,repair,OriginalGuard.valid_iff]

private theorem pair_words (u v : Word) : Q (pairWords u v) ↔ U u ∧ S v := by
  rw [pair_language]
  simp

/-- Conditional only on NP-completeness of the exact original unrestricted
well-formed SAT language, guarded original UNSAT is coNP-complete and the ordered
original (UNSAT,SAT) pair language is DP-complete. All reductions are total
polynomial binary transducers in the same finite single-tape model. -/
theorem lemma63 (hS : NPComplete S) : CoNPComplete U ∧ DPComplete Q := by
  classical
  have hpFalse := polyTime_repair falseWord
  have hpTrue := polyTime_repair trueWord
  have hpLeft : PolyTime leftGuard :=
    polyTime_comp (f := PairProjection.project false trueWord) (g := repair trueWord)
      hpTrue (PairProjection.polyTime_project false trueWord)
  have hpRight : PolyTime rightGuard :=
    polyTime_comp (f := PairProjection.project true falseWord) (g := repair falseWord)
      hpFalse (PairProjection.polyTime_project true falseWord)
  have hU : InCoNP U := by
    apply inNP_congr (A := fun w => S (repair trueWord w))
      (fun w => ?_) (inNP_preimage hS.1 hpTrue)
    simpa only [not_not] using (not_congr ((repair_laws w).2.2.1)).symm
  have hardU : ∀ A : Language, InCoNP A → PolyRed A U := by
    intro A hA
    obtain ⟨f,hf,hfS⟩ := hS.2 (fun x => ¬ A x) hA
    refine ⟨fun x => repair falseWord (f x),polyTime_comp hpFalse hf,?_⟩
    intro x
    have hr := repair_laws (f x)
    change A x ↔ W (repair falseWord (f x)) ∧ ¬ S (repair falseWord (f x))
    rw [hr.2.1]
    exact ⟨fun hx => ⟨hr.1,fun hs => (hfS x).mpr hs hx⟩,
      fun hx => by_contra fun hn => hx.2 ((hfS x).mp hn)⟩
  have hQ : InDP Q := by
    refine ⟨(fun w => S (rightGuard w)),(fun w => ¬ S (leftGuard w)),
      inNP_preimage hS.1 hpRight,?_,?_⟩
    · apply inNP_congr (A := fun w => S (leftGuard w)) (fun w => ?_)
        (inNP_preimage hS.1 hpLeft)
      simp
    · intro w
      exact (pair_split w).trans and_comm
  have hardQ : ∀ A : Language, InDP A → PolyRed A Q := by
    intro A hA
    obtain ⟨X,Y,hX,hY,hXY⟩ := hA
    obtain ⟨f,hf,hfS⟩ := hS.2 (fun x => ¬ Y x) hY
    obtain ⟨g,hg,hgS⟩ := hS.2 X hX
    let first := fun x => repair falseWord (f x)
    let second := fun x => repair falseWord (g x)
    refine ⟨(fun x => pairWords (first x) (second x)),
      TransducerPair.polyTime_pair (polyTime_comp hpFalse hf) (polyTime_comp hpFalse hg),?_⟩
    intro x
    rw [pair_words]
    have hrFirst := repair_laws (f x)
    have hrSecond := repair_laws (g x)
    change A x ↔ (W (first x) ∧ ¬ S (first x)) ∧ S (second x)
    have hWF : W (first x) := hrFirst.1
    have hSF : S (first x) ↔ S (f x) := hrFirst.2.1
    have hSG : S (second x) ↔ S (g x) := hrSecond.2.1
    rw [hSF,hSG,← hgS x,← hfS x]
    simpa [hWF,and_comm,and_left_comm,and_assoc] using hXY x
  exact ⟨⟨hU,hardU⟩,⟨hQ,hardQ⟩⟩

end PredictiveThermodynamic.OriginalClasses
