/- GID: D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponsePositiveShiftConsumer
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseRealization/ResponsePositiveShiftConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The constructed response-output positive word has its exact letter count and literal negative time correction on all histories. -/

/- Construct the response-output positive word and its signed correction. The original-domain input identification is supplied by FullOutResponseIdentification. -/
import D5.S3.ConceptDynamics.Coding.ResponseRealization.ConstructedTowerProfiles
import D5.S3.ConceptDynamics.Coding.ResponseRealization.CentredResponseCorrection

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


end D5.S3.ConceptDynamics.Coding.ResponsePositiveShiftConsumer
