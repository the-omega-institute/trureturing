/- SOURCE ONLY. UNCOMPILED. Construct the original-domain positive word
from the actual full outgoing input tower and actual response-output word.
Every leaf and intermediate endpoint belongs to TypedPositiveSplitWord.Word.
Local supplier candidates expose RepeatedFullOutSplit.appendFull and make
terminal reflexivity tactics safe under goal closure. Their mathematical
statements and constructions are unchanged. -/
import D5.S3.ConceptDynamics.Coding.FullOutResponseIdentification
import D5.S3.ConceptDynamics.Coding.ResponsePositiveShiftConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.OriginalPositiveWordAssembly
open EssentialWordRealization FiniteWindowTableCriterion
open TwoSidedFiniteInduction RepeatedFullOutSplit
open TypedPositiveSplitWord SplitTowerTranslation SplitTowerPositiveAccounting
open OriginalResponseNumbering ResponseTwoSidedConsumer

/-- Appending the actual last outgoing split adds no incoming stage, even
when the earlier tower contains incoming stages. -/
private theorem appendFull_inCount {F K : Presentation} (t : Tower F K) :
    TowerWord.inCount (appendFull t) = TowerWord.inCount t := by
  induction t with
  | nil F => rfl
  | outgoing T p tail ih => exact ih
  | incoming T p tail ih => exact congrArg (fun n : ℕ => n+1) ih

/-- This is a property of the constructed tower, not an input profile. -/
private theorem full_inCount (F : Presentation) (n : ℕ) :
    TowerWord.inCount (tower F n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change TowerWord.inCount (appendFull (tower F n)) = 0
      rw [appendFull_inCount,ih]

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E) (hG : Essential G)
variable {a b c d : ℕ} (pair : TablePair G G a b c d) (S : SameTableConjugacy pair)

/-- A finite word on the ORIGINAL graph. Its input is the actual q-fold
full outgoing tower, then the actual finite numbered identification, then
the constructed response word. No inverse, time, U or arbitrary-history-map
leaf is introduced. Both the letter count and the correction are derived. -/
theorem positive_word :
    ∃ w : Word (original G hG) (original G hG),
      w.letters = (a+b+1)+2*((a+c)+(b+d+1)) ∧
      (∀ x : History G,
        S.forward x = time G (-(a:ℤ)-(((a+c)+(b+d+1):ℕ):ℤ)) (w.eval x)) := by
  let F := original G hG
  let A := tower F (a+b+1)
  let J := FullOutResponseIdentification.numberedIdentification F pair
  let R := ResponsePositiveShiftConsumer.word G hG pair S
  let w : Word F F := .comp (TowerWord.forward A) (.comp (.relabel J) R)
  have hinput (y : Hist F) : A.toHomeomorph y = (TowerWord.forward A).eval y := by
    have h := TowerWord.forward_literal A y
    have hi : TowerWord.inCount A = 0 := full_inCount F (a+b+1)
    rw [hi] at h
    simpa only [Int.natCast_zero,neg_zero,
      StandardBeamHomeomorphisms.translate_zero] using h
  refine ⟨w,?_,?_⟩
  · change (TowerWord.forward A).letters+(0+R.letters) = _
    rw [TowerWord.forward_letters]
    change (tower F (a+b+1)).length+
      (0+(ResponsePositiveShiftConsumer.word G hG pair S).letters) = _
    rw [tower_length,ResponsePositiveShiftConsumer.word_letters] <;> omega
  · intro x
    calc
      S.forward x = time G (-(((a+c)+(b+d+1):ℕ):ℤ))
          (R.eval (numberedLift G pair x)) :=
        ResponsePositiveShiftConsumer.original_centred G hG pair S x
      _ = time G (-(((a+c)+(b+d+1):ℕ):ℤ))
          (R.eval (J.homeomorph ((TowerWord.forward A).eval
            (time G (-(a:ℤ)) x)))) := by
        rw [FullOutResponseIdentification.numberedLift_eq_tower_negative F pair x,
          hinput] <;> rfl
      _ = time G (-(((a+c)+(b+d+1):ℕ):ℤ)+(-(a:ℤ))) (w.eval x) := by
        rw [Word.eval_time,relabel_homeomorph_time,Word.eval_time,
          StandardBeamHomeomorphisms.translate_add] <;> rfl
      _ = time G (-(a:ℤ)-(((a+c)+(b+d+1):ℕ):ℤ)) (w.eval x) := by
        congr 1 <;> omega

end D5.S3.ConceptDynamics.Coding.OriginalPositiveWordAssembly
