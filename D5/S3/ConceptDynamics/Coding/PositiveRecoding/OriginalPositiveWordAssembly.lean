/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/OriginalPositiveWordAssembly
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/OriginalPositiveWordAssembly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct the positive word on the original finite presentation. -/

/- Construct the original-domain word from the full outgoing input tower, its actual numbered response identification and the response-output word. Every leaf and endpoint belongs to TypedPositiveSplitWord.Word. -/
import D5.S3.ConceptDynamics.Coding.ResponseRealization.FullOutResponseIdentification
import D5.S3.ConceptDynamics.Coding.ResponseRealization.ResponsePositiveShiftConsumer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
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
    simp only [Int.natCast_zero, neg_zero] at h
    refine h.trans ?_
    apply Subtype.ext
    funext t
    change ((TowerWord.forward A).eval y).val (t+0) = ((TowerWord.forward A).eval y).val t
    rw [add_zero]
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
        have ht := FullOutResponseIdentification.numberedLift_eq_tower_negative F pair x
        have hl := hinput (time F.graph (-(a:ℤ)) x)
        have he : numberedLift G pair x =
            J.homeomorph ((TowerWord.forward A).eval (time G (-(a:ℤ)) x)) :=
          ht.trans (congrArg J.homeomorph hl)
        exact congrArg (fun z => time G (-(((a+c)+(b+d+1):ℕ):ℤ)) (R.eval z)) he
      _ = time G (-(((a+c)+(b+d+1):ℕ):ℤ)+(-(a:ℤ))) (w.eval x) := by
        change time G (-(((a+c)+(b+d+1):ℕ):ℤ)) (w.eval (time F.graph (-(a:ℤ)) x)) = _
        refine (congrArg (time G (-(((a+c)+(b+d+1):ℕ):ℤ)))
          (Word.eval_time w (-(a:ℤ)) x)).trans ?_
        let y : History G := w.eval x
        change time G (-(((a+c)+(b+d+1):ℕ):ℤ)) (time G (-(a:ℤ)) y) = _
        apply Subtype.ext
        funext t
        change y.val (t+(-(((a+c)+(b+d+1):ℕ):ℤ))+(-(a:ℤ))) =
          y.val (t+(-(((a+c)+(b+d+1):ℕ):ℤ)+(-(a:ℤ))))
        exact congrArg y.val (by omega)
      _ = time G (-(a:ℤ)-(((a+c)+(b+d+1):ℕ):ℤ)) (w.eval x) := by
        congr 1 <;> omega

end D5.S3.ConceptDynamics.Coding.OriginalPositiveWordAssembly
