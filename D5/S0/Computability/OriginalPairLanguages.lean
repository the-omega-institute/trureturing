/- GID: D5/S0/Computability/OriginalPairLanguages
   generality: G
   mirror-B: D5/B/S0/Computability/OriginalPairLanguages
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact all-word guarded projections characterize the ordered original UNSAT-SAT language. -/

import D5.S0.Computability.OriginalClauseLanguages
import D5.S0.Computability.BinaryMachine.PairProjection

set_option autoImplicit false
namespace PredictiveThermodynamic.OriginalClasses
open Complexity

/-- The complement-SAT factor uses the true repair and the first component. -/
def leftGuard (w : Word) : Word := repair trueWord (PairProjection.project false trueWord w)
/-- The SAT factor uses the false repair and the second component. -/
def rightGuard (w : Word) : Word := repair falseWord (PairProjection.project true falseWord w)

/-- Every outer word, including malformed words and pairs with malformed
components, has exactly the ordered guarded intersection semantics. -/
theorem pair_split (w : Word) : Q w ↔ ¬ S (leftGuard w) ∧ S (rightGuard w) := by
  classical
  have hbad : ¬ S [] := by
    rintro ⟨F,hF,_⟩
    change (none : Option Conventional.Formula) = some F at hF
    cases hF
  have hnotU : ¬ U [] := by
    rintro ⟨⟨F,hF⟩,_⟩
    change (none : Option Conventional.Formula) = some F at hF
    cases hF
  have htrue : S trueWord := by
    have h := (repair_laws []).2.2.1
    change (U [] ↔ ¬ S trueWord) at h
    by_contra hn
    exact hnotU (h.mpr hn)
  have hfalse : ¬ S falseWord := by
    have h := (repair_laws []).2.1
    change (S falseWord ↔ S []) at h
    exact fun hs => hbad (h.mp hs)
  have htrueU : ¬ U trueWord := fun h => h.2 htrue
  change Q w ↔ ¬ S (repair trueWord (PairProjection.project false trueWord w)) ∧
    S (repair falseWord (PairProjection.project true falseWord w))
  rw [← (repair_laws (PairProjection.project false trueWord w)).2.2.1,
    (repair_laws (PairProjection.project true falseWord w)).2.1,pair_language]
  cases hp : StackPair.decodePair w with
  | none => simp [PairProjection.project,hp,htrueU,hfalse]
  | some p =>
    obtain ⟨u,v⟩ := p
    simp [PairProjection.project,hp]

end PredictiveThermodynamic.OriginalClasses
