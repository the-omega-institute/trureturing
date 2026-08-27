/- GID: D5/S3/Observer/Naturality/ObserverMorphismComposition
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/ObserverMorphismComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observer morphisms compose forward on states and backward on protocols. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches for observer morphisms, evaluation preservation, and
     the paired state/protocol composition law found no canonical structure or
     exact theorem, so this declaration states the law directly on the source
     maps without introducing a competing family primitive.
   * Pinned-Mathlib search found `Function.comp_apply`, which is used to expose
     the two composite maps. No library theorem combines the two
     evaluation-preservation hypotheses into this source statement. -/

namespace D5.S3.Observer.Naturality.ObserverMorphismComposition

/-- Evaluation-preserving observer morphisms compose forward on state maps and
backward on protocol maps. -/
theorem observer_morphism_composition
    {X1 X2 X3 P1 P2 P3 Law : Type*}
    (e1 : X1 -> P1 -> Law) (e2 : X2 -> P2 -> Law) (e3 : X3 -> P3 -> Law)
    (f1 : X1 -> X2) (g1 : P2 -> P1)
    (f2 : X2 -> X3) (g2 : P3 -> P2)
    (h1 : forall x p, e2 (f1 x) p = e1 x (g1 p))
    (h2 : forall x p, e3 (f2 x) p = e2 x (g2 p)) :
    forall x p, e3 ((f2 ∘ f1) x) p = e1 x ((g1 ∘ g2) p) := by
  intro x p
  calc
    e3 ((f2 ∘ f1) x) p = e2 (f1 x) (g2 p) := by
      simpa only [Function.comp_apply] using h2 (f1 x) p
    _ = e1 x (g1 (g2 p)) := h1 x (g2 p)
    _ = e1 x ((g1 ∘ g2) p) := by rw [Function.comp_apply]

/-- Two identity translations on singleton carriers witness the hypotheses. -/
example : True := by
  have _witness :=
    observer_morphism_composition
      (e1 := fun _ : Unit => fun _ : Unit => ())
      (e2 := fun _ : Unit => fun _ : Unit => ())
      (e3 := fun _ : Unit => fun _ : Unit => ())
      (f1 := id) (g1 := id) (f2 := id) (g2 := id)
      (by intros; rfl) (by intros; rfl)
  exact True.intro

#print axioms observer_morphism_composition

end D5.S3.Observer.Naturality.ObserverMorphismComposition
