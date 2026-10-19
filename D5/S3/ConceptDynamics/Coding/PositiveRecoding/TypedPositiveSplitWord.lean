/- GID: D5/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/PositiveRecoding/TypedPositiveSplitWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Endpoint-typed finite positive words with explicit corrections. -/

/- Words have only relabel, positive and composition constructors, with literal intermediate presentations. Numbering reuses the existing rectangular fibers and counted split/join. -/
import D5.S3.ConceptDynamics.Coding.PositiveRecoding.SplitTowerTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.ConceptDynamics.Coding.TypedPositiveSplitWord
open EssentialWordRealization TwoSidedFiniteInduction
open CountedMatrixOverlap (CountMat Path elementaryHomeomorph)
open ZeroWindowRelabeling (Relabel)
open SplitTowerTranslation

/-- A positive letter is bracketed by actual finite graph bijections.
Composition is indexed by the literal intermediate finite presentation. -/
inductive Word : Presentation → Presentation → Type 1
  | relabel {F H : Presentation} (r : Relabel F.graph H.graph) : Word F H
  | positive {F H : Presentation} {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
      (old : Relabel (counted (R*S)) F.graph)
      (next : Relabel (counted (S*R)) H.graph) : Word F H
  | comp {F H K : Presentation} (first : Word F H) (second : Word H K) : Word F K

namespace Word
variable {F H K : Presentation}

def eval : {F H : Presentation} → Word F H → (Hist F ≃ₜ Hist H)
  | _, _, .relabel r => r.homeomorph
  | _, _, .positive R S old next =>
      old.homeomorph.symm.trans ((elementaryHomeomorph R S).trans next.homeomorph)
  | _, _, .comp first second => first.eval.trans second.eval

def letters : {F H : Presentation} → Word F H → ℕ
  | _, _, .relabel _ => 0
  | _, _, .positive _ _ _ _ => 1
  | _, _, .comp first second => first.letters+second.letters

def identity (F : Presentation) : Word F F := .relabel {
  vertex := Equiv.refl _
  edge := Equiv.refl _
  source := fun _ => rfl
  target := fun _ => rfl }

theorem eval_time : ∀ {F H : Presentation} (w : Word F H) (a : ℤ) (x : Hist F),
    w.eval (time F.graph a x) = time H.graph a (w.eval x)
  | _, _, .relabel r, a, x => relabel_homeomorph_time r a x
  | _, _, .positive R S old next, a, x => by
      change next.homeomorph (elementaryHomeomorph R S
        (old.homeomorph.symm (time _ a x))) = _
      calc
        _ = next.homeomorph (elementaryHomeomorph R S
            (time (counted (R*S)) a (old.homeomorph.symm x))) :=
          congrArg (fun z => next.homeomorph (elementaryHomeomorph R S z))
            (relabel_inverse_time old a x)
        _ = next.homeomorph (time (counted (S*R)) a
            (elementaryHomeomorph R S (old.homeomorph.symm x))) :=
          congrArg next.homeomorph (positive_time R S a _)
        _ = _ := relabel_homeomorph_time next a _
  | _, _, .comp u v, a, x => by
      change v.eval (u.eval (time _ a x)) = _
      exact (congrArg v.eval (eval_time u a x)).trans (eval_time v a (u.eval x))

theorem numbered_letter {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (old : Relabel (counted (R*S)) F.graph)
    (next : Relabel (counted (S*R)) H.graph) (x : Hist F) :
    next.homeomorph.symm ((Word.positive R S old next).eval x) =
      elementaryHomeomorph R S (old.homeomorph.symm x) :=
  next.homeomorph.symm_apply_apply _

/-- Opposite POSITIVE letter, with the literal negative-unit correction. -/
theorem inverse_letter {n m : ℕ} (R : CountMat n m) (S : CountMat m n)
    (old : Relabel (counted (R*S)) F.graph)
    (next : Relabel (counted (S*R)) H.graph) (z : Hist H) :
    (Word.positive R S old next).eval.symm z =
      time F.graph (-1) ((Word.positive S R next old).eval z) := by
  change old.homeomorph ((elementaryHomeomorph R S).symm
    (next.homeomorph.symm z)) = _
  calc
    _ = old.homeomorph (time (counted (R*S)) (-1)
        (elementaryHomeomorph S R (next.homeomorph.symm z))) :=
      congrArg old.homeomorph
        (NumberedPositiveInverseLaws.inverse_eq_negative_positive R S _)
    _ = _ := relabel_homeomorph_time old (-1) _
end Word

/-- The outgoing supplier has finite edge bijections and both endpoint
laws. Expose those as Relabel data; do not introduce another enumeration. -/
def outOld (F T : Presentation) (p : F.E → T.E) :
    Relabel (counted (OutSplitNumberedRecoding.R F.graph p *
      OutSplitNumberedRecoding.S F.graph p)) F.graph where
  vertex := (OutSplitNumberedRecoding.oldNumber (V := F.V)).symm
  edge := OutSplitNumberedRecoding.oldEdgeEquiv F.graph p
  source e := by
    apply (OutSplitNumberedRecoding.oldNumber (V := F.V)).injective
    rw [(OutSplitNumberedRecoding.oldNumber (V := F.V)).apply_symm_apply]
    exact (OutSplitNumberedRecoding.old_endpoints F.graph p e).1
  target e := by
    apply (OutSplitNumberedRecoding.oldNumber (V := F.V)).injective
    rw [(OutSplitNumberedRecoding.oldNumber (V := F.V)).apply_symm_apply]
    exact (OutSplitNumberedRecoding.old_endpoints F.graph p e).2

def outNext (F T : Presentation) (p : F.E → T.E) :
    Relabel (counted (OutSplitNumberedRecoding.S F.graph p *
      OutSplitNumberedRecoding.R F.graph p)) (out F T p).graph where
  vertex := (OutSplitNumberedRecoding.newNumber F.graph p).symm
  edge := OutSplitNumberedRecoding.newEdgeEquiv F.graph p
  source e := by
    apply (OutSplitNumberedRecoding.newNumber F.graph p).injective
    exact (OutSplitNumberedRecoding.new_endpoints F.graph p e).1.trans
      ((OutSplitNumberedRecoding.newNumber F.graph p).apply_symm_apply e.source).symm
  target e := by
    apply (OutSplitNumberedRecoding.newNumber F.graph p).injective
    exact (OutSplitNumberedRecoding.new_endpoints F.graph p e).2.trans
      ((OutSplitNumberedRecoding.newNumber F.graph p).apply_symm_apply e.target).symm

/-- Function-level equalities, including the existing supplier's exact
parallel-edge numbering; no matrix-equality transport is hidden here. -/
theorem out_old_number (F T : Presentation) (p : F.E → T.E) (x : Hist F) :
    (outOld F T p).homeomorph.symm x = OutSplitNumberedRecoding.oldPaths F.graph p x := rfl

theorem out_next_number (F T : Presentation) (p : F.E → T.E) (z : Hist (out F T p)) :
    (outNext F T p).homeomorph.symm z = OutSplitNumberedRecoding.newPaths F.graph p z := rfl

def outgoing (F T : Presentation) (p : F.E → T.E) : Word F (out F T p) :=
  .positive (OutSplitNumberedRecoding.R F.graph p) (OutSplitNumberedRecoding.S F.graph p)
    (outOld F T p) (outNext F T p)

def outgoingBack (F T : Presentation) (p : F.E → T.E) : Word (out F T p) F :=
  .positive (OutSplitNumberedRecoding.S F.graph p) (OutSplitNumberedRecoding.R F.graph p)
    (outNext F T p) (outOld F T p)

def incoming (F T : Presentation) (p : F.E → T.E) :
    Word F (TwoSidedFiniteInduction.incoming F T p) :=
  .positive (InSplitNumberedRecoding.R F.graph p) (InSplitNumberedRecoding.S F.graph p)
    (InSplitNumberedRecoding.oldRelabel F.graph p) (InSplitNumberedRecoding.newRelabel F.graph p)

def incomingBack (F T : Presentation) (p : F.E → T.E) :
    Word (TwoSidedFiniteInduction.incoming F T p) F :=
  .positive (InSplitNumberedRecoding.S F.graph p) (InSplitNumberedRecoding.R F.graph p)
    (InSplitNumberedRecoding.newRelabel F.graph p) (InSplitNumberedRecoding.oldRelabel F.graph p)

theorem outgoing_literal (F T : Presentation) (p : F.E → T.E) (x : Hist F) :
    ActualOutSplit.lift F.graph p x = (outgoing F T p).eval x := by
  apply (outNext F T p).homeomorph.symm.injective
  rw [show outgoing F T p = Word.positive _ _ (outOld F T p) (outNext F T p) from rfl,
    Word.numbered_letter,out_old_number,out_next_number]
  exact (OutSplitNumberedRecoding.numbered_recoding F.graph p x).symm

theorem outgoing_inverse_literal (F T : Presentation) (p : F.E → T.E)
    (z : Hist (out F T p)) :
    ActualOutSplit.forget F.graph p z = time F.graph (-1) ((outgoingBack F T p).eval z) := by
  have hinv : (outgoing F T p).eval.symm z = ActualOutSplit.forget F.graph p z := by
    apply (outgoing F T p).eval.injective
    rw [(outgoing F T p).eval.apply_symm_apply,← outgoing_literal,ActualOutSplit.lift_forget]
  rw [← hinv]
  exact Word.inverse_letter _ _ (outOld F T p) (outNext F T p) z

theorem incoming_literal (F T : Presentation) (p : F.E → T.E) (x : Hist F) :
    ActualInSplit.lift F.graph p x =
      time (TwoSidedFiniteInduction.incoming F T p).graph (-1) ((incoming F T p).eval x) := by
  apply (InSplitNumberedRecoding.newRelabel F.graph p).homeomorph.symm.injective
  have hn := Word.numbered_letter (F := F)
    (H := TwoSidedFiniteInduction.incoming F T p) (InSplitNumberedRecoding.R F.graph p)
    (InSplitNumberedRecoding.S F.graph p) (InSplitNumberedRecoding.oldRelabel F.graph p)
    (InSplitNumberedRecoding.newRelabel F.graph p) x
  have ht := relabel_inverse_time (InSplitNumberedRecoding.newRelabel F.graph p)
    (-1) ((incoming F T p).eval x)
  exact (InSplitNumberedRecoding.numbered_lift F.graph p x).trans
    ((congrArg (time (counted _) (-1)) hn).symm.trans ht.symm)

theorem incoming_inverse_literal (F T : Presentation) (p : F.E → T.E)
    (z : Hist (TwoSidedFiniteInduction.incoming F T p)) :
    ActualInSplit.forget F.graph p z = (incomingBack F T p).eval z := by
  apply (InSplitNumberedRecoding.oldRelabel F.graph p).homeomorph.symm.injective
  rw [show incomingBack F T p = Word.positive _ _ _ _ from rfl,Word.numbered_letter]
  exact (InSplitNumberedRecoding.numbered_forget F.graph p z).symm
end D5.S3.ConceptDynamics.Coding.TypedPositiveSplitWord
