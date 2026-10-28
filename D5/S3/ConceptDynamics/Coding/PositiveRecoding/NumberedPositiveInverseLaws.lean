/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/NumberedPositiveInverseLaws
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact numbered positive recoding and inverse time signs. -/

/- At time t the positive recoding joins s_t to r_(t+1); its inverse reads the preceding half at t-1. Opposite positive recodings compose to forward unit time. -/
import D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.NumberedPositiveInverseLaws
open CountedMatrixOverlap
variable {n m : ℕ} (R : CountMat n m) (S : CountMat m n)

/-- Integer time translation has the literal forward-time sign. -/
def translate {k : ℕ} (B : CountMat k k) (a : ℤ) (x : Path B) : Path B :=
  ⟨fun t => x.val (t+a),fun t => by
    simpa only [add_assoc,add_comm a 1] using x.property (t+a)⟩

/-- The actual positive law (r_t,s_t) -> (s_t,r_(t+1)). -/
theorem positive_coordinate (x : Path (R*S)) (t : ℤ) :
    (elementaryHomeomorph R S x).val t =
      join S R (split R S (x.val t)).2 (split R S (x.val (t+1))).1 (x.property t) := rfl

/-- The inverse has preceding time on the recovered R half-edge. -/
theorem inverse_coordinate (y : Path (S*R)) (t : ℤ) :
    ((elementaryHomeomorph R S).symm y).val t =
      join R S (split S R (y.val (t-1))).2 (split S R (y.val t)).1
        (by simpa only [split_target, split_source, sub_add_cancel] using y.property (t-1)) := rfl

theorem positive_translate (a : ℤ) (x : Path (R*S)) :
    elementaryHomeomorph R S (translate (R*S) a x) =
      translate (S*R) a (elementaryHomeomorph R S x) := by
  apply Subtype.ext
  funext t
  have ht : t + a + 1 = t + 1 + a := by omega
  simp only [positive_coordinate, translate, ht]

/-- Replacing an inverse by the opposite POSITIVE recoding costs -1. -/
theorem inverse_eq_negative_positive (y : Path (S*R)) :
    (elementaryHomeomorph R S).symm y =
      translate (R*S) (-1) (elementaryHomeomorph S R y) := by
  apply Subtype.ext
  funext t
  rw [inverse_coordinate]
  change _ = (elementaryHomeomorph S R y).val (t+(-1))
  rw [positive_coordinate]
  have hprev : t+(-1) = t-1 := by omega
  simp only [hprev,sub_add_cancel]


end D5.S3.ConceptDynamics.Coding.NumberedPositiveInverseLaws
