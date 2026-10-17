/- SOURCE ONLY. UNCOMPILED. Exact numbered coordinate and inverse signs.
Uses the EXISTING counted split/join enumeration, never another ranking. -/
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
@[simp] theorem translate_zero {k : ℕ} (B : CountMat k k) (x : Path B) :
    translate B 0 x = x := by apply Subtype.ext; funext t; simp [translate]
theorem translate_add {k : ℕ} (B : CountMat k k) (a b : ℤ) (x : Path B) :
    translate B a (translate B b x) = translate B (a+b) x := by
  apply Subtype.ext
  funext t
  simp only [translate,add_assoc]

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

/-- Two opposite positive recodings yield FORWARD unit time, not identity. -/
theorem positive_opposite (x : Path (R*S)) :
    elementaryHomeomorph S R (elementaryHomeomorph R S x) = shift (R*S) x := by
  apply Subtype.ext
  funext t
  simp only [positive_coordinate, split_join]
  exact join_split R S (x.val (t+1))

end D5.S3.ConceptDynamics.Coding.NumberedPositiveInverseLaws
