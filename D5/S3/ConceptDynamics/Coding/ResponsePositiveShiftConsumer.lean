/- SOURCE ONLY. UNCOMPILED. Actual response-output positive word and shift.
The uncentred input U is explicit but is NOT claimed to be a positive word.
Its identification with the iterated full outgoing input remains external. -/
import D5.S3.ConceptDynamics.Coding.ConstructedTowerProfiles
import D5.S3.ConceptDynamics.Coding.CentredResponseCorrection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.ResponsePositiveShiftConsumer
open EssentialWordRealization FiniteWindowTableCriterion TwoSidedFiniteInduction
open OriginalResponseGraph OriginalResponseNumbering ResponseTwoSidedConsumer
open TypedPositiveSplitWord SplitTowerTranslation SplitTowerPositiveAccounting
open ConstructedTowerProfiles

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable (G : DirectedMultigraph V E) (hG : Essential G)
variable {a b c d : ℕ} (pair : TablePair G G a b c d) (S : SameTableConjugacy pair)

/-- This is an actual finite numbered word from the exact response graph to
G: source lifts, terminal finite relabeling, reversed target lifts. -/
def word : Word (response G hG pair S) (original G hG) :=
  terminalWord (terminal G hG pair S)

theorem word_letters : (word G hG pair S).letters = 2*((a+c)+(b+d+1)) :=
  terminal_letters (terminal G hG pair S)

/-- Literal -k on EVERY response history. Both counts are derived from the
actual recursion, including its completed first outgoing stage. -/
theorem output_literal (z : Hist (response G hG pair S)) :
    numberedOutput G pair S (local_of_conjugacy hG hG pair S).seamG z =
      time G (-(((a+c)+(b+d+1):ℕ):ℤ)) ((word G hG pair S).eval z) := by
  let r := terminal G hG pair S
  have hr := response_profile G hG pair S
  have he : -(TowerWord.inCount r.left : ℤ)-(TowerWord.outCount r.right : ℤ) =
      -(((a+c)+(b+d+1):ℕ):ℤ) := by
    rw [hr.1,hr.2.2.2.1]
    omega
  have h := terminal_literal r z
  rw [he] at h
  exact h

/-- Exact original-history equality, with centring still kept separate. -/
theorem original_centred (x : History G) :
    S.forward x = time G (-(((a+c)+(b+d+1):ℕ):ℤ))
      ((word G hG pair S).eval (numberedLift G pair x)) := by
  obtain ⟨_,_,hp,_,_,_,_,_⟩ := numbered_response_reduction G pair hG S
  rw [← hp x]
  exact output_literal G hG pair S (numberedLift G pair x)

/-- U commutes with integer time by its ACTUAL future-block coordinates.
No full-outgoing graph equivalence or word representation for U is used. -/
theorem uncentred_time (s : ℤ) (x : History G) :
    CentredResponseCorrection.uncentred G pair (time G s x) =
      time (countedGraph G pair) s (CentredResponseCorrection.uncentred G pair x) := by
  apply Subtype.ext
  funext t
  apply (edgeEquiv G pair).injective
  change edgeEquiv G pair ((CentredResponseCorrection.uncentred G pair (time G s x)).val t) =
    edgeEquiv G pair ((CentredResponseCorrection.uncentred G pair x).val (t+s))
  rw [CentredResponseCorrection.uncentred_coordinate,CentredResponseCorrection.uncentred_coordinate]
  congr 1
  apply legalWord_ext
  funext j
  change x.val (t+(j.val:ℤ)+s) = x.val (t+s+(j.val:ℤ))
  exact congrArg x.val (by omega)

/-- Compose ONLY the already constructed U centring law with the now
constructed response-output word. The full original input word is NOT a
hypothesis and is NOT a conclusion. The resulting sign is literally -a-k. -/
theorem original_uncentred (x : History G) :
    S.forward x = time G (-(a:ℤ)-(((a+c)+(b+d+1):ℕ):ℤ))
      ((word G hG pair S).eval (CentredResponseCorrection.uncentred G pair x)) := by
  rw [original_centred G hG pair S x,
    CentredResponseCorrection.centred_eq_uncentred_negative,uncentred_time,
    ]
  have ht := Word.eval_time (word G hG pair S) (-(a:ℤ))
    (CentredResponseCorrection.uncentred G pair x)
  refine (congrArg (time G (-(((a+c)+(b+d+1):ℕ):ℤ))) ht).trans ?_
  let y : History G := (word G hG pair S).eval (CentredResponseCorrection.uncentred G pair x)
  change time G (-(((a+c)+(b+d+1):ℕ):ℤ)) (time G (-(a:ℤ)) y) = _
  apply Subtype.ext
  funext t
  change y.val (t+(-(((a+c)+(b+d+1):ℕ):ℤ))+(-(a:ℤ))) =
    y.val (t+(-(a:ℤ)-(((a+c)+(b+d+1):ℕ):ℤ)))
  exact congrArg y.val (by omega)
end D5.S3.ConceptDynamics.Coding.ResponsePositiveShiftConsumer
