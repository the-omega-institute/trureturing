/- SOURCE ONLY. UNCOMPILED. Construction-internal integer time laws.
The sign convention is always (tau a x)_t = x_(t+a).
No time-commutation premise is introduced. -/
import D5.S3.ConceptDynamics.Coding.TwoSidedFiniteInduction
import D5.S3.ConceptDynamics.Coding.InSplitNumberedRecoding
import D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.SplitTowerTranslation
open EssentialWordRealization
open TwoSidedFiniteInduction
open CountedMatrixOverlap (CountMat Path elementaryHomeomorph)
open ZeroWindowRelabeling (Relabel)

abbrev time {V E : Type*} (G : DirectedMultigraph V E) :=
  StandardBeamHomeomorphisms.translate G
abbrev counted {n : ℕ} (B : CountMat n n) := InSplitNumberedRecoding.counted B

/-- Both previously supplied translations have exactly the same coordinates. -/
theorem counted_time {n : ℕ} (B : CountMat n n) (a : ℤ) (x : Path B) :
    time (counted B) a x = NumberedPositiveInverseLaws.translate B a x := rfl

section Relabel
variable {V E W D : Type*} {G : DirectedMultigraph V E} {H : DirectedMultigraph W D}

theorem relabel_time (r : Relabel G H) (a : ℤ) (x : History G) :
    r.history (time G a x) = time H a (r.history x) := rfl

variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace D] [DiscreteTopology D]

theorem relabel_homeomorph_time (r : Relabel G H) (a : ℤ) (x : History G) :
    r.homeomorph (time G a x) = time H a (r.homeomorph x) := rfl

theorem relabel_inverse_time (r : Relabel G H) (a : ℤ) (x : History H) :
    r.homeomorph.symm (time H a x) = time G a (r.homeomorph.symm x) := rfl
end Relabel

section Split
variable {V E L : Type*} (G : DirectedMultigraph V E) (p : E → L)

theorem outgoing_lift_time (a : ℤ) (x : History G) :
    ActualOutSplit.lift G p (time G a x) =
      time (ActualOutSplit.graph G p) a (ActualOutSplit.lift G p x) := by
  apply Subtype.ext
  funext t
  apply ActualOutSplit.edge_ext G p
  · rfl
  · change p (x.val (t+1+a)) = p (x.val (t+a+1))
    exact congrArg (fun s : ℤ => p (x.val s)) (by omega)

theorem outgoing_forget_time (a : ℤ) (z : History (ActualOutSplit.graph G p)) :
    ActualOutSplit.forget G p (time (ActualOutSplit.graph G p) a z) =
      time G a (ActualOutSplit.forget G p z) := rfl

theorem incoming_lift_time (a : ℤ) (x : History G) :
    ActualInSplit.lift G p (time G a x) =
      time (ActualInSplit.graph G p) a (ActualInSplit.lift G p x) := by
  apply Subtype.ext
  funext t
  apply ActualInSplit.edge_ext G p
  · change p (x.val (t-1+a)) = p (x.val (t+a-1))
    exact congrArg (fun s : ℤ => p (x.val s)) (by omega)
  · rfl

theorem incoming_forget_time (a : ℤ) (z : History (ActualInSplit.graph G p)) :
    ActualInSplit.forget G p (time (ActualInSplit.graph G p) a z) =
      time G a (ActualInSplit.forget G p z) := rfl
end Split

section Positive
variable {n m : ℕ} (R : CountMat n m) (S : CountMat m n)

theorem positive_time (a : ℤ) (x : Path (R*S)) :
    elementaryHomeomorph R S (time (counted (R*S)) a x) =
      time (counted (S*R)) a (elementaryHomeomorph R S x) :=
  NumberedPositiveInverseLaws.positive_translate R S a x

/-- The actual inverse also commutes with every integer time, derived from
bijectivity and the positive coordinate theorem, rather than assumed. -/
theorem positive_inverse_time (a : ℤ) (z : Path (S*R)) :
    (elementaryHomeomorph R S).symm (time (counted (S*R)) a z) =
      time (counted (R*S)) a ((elementaryHomeomorph R S).symm z) := by
  apply (elementaryHomeomorph R S).injective
  exact ((elementaryHomeomorph R S).apply_symm_apply _).trans
    ((positive_time R S a ((elementaryHomeomorph R S).symm z)).trans
      (congrArg (time (counted (S*R)) a)
        ((elementaryHomeomorph R S).apply_symm_apply z))).symm
end Positive
end D5.S3.ConceptDynamics.Coding.SplitTowerTranslation
