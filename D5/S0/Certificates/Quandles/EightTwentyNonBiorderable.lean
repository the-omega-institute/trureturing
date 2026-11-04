/- GID: D5/S0/Certificates/Quandles/EightTwentyNonBiorderable
   generality: I
   mirror-B: D5/B/S0/Certificates/Quandles/EightTwentyNonBiorderable
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [lake/module/D5.S0.Certificates.Quandles.PresentedQuandle, lake/module/D5.S0.Certificates.Quandles.SixRelationObstruction]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.claim; result=D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.result; claim=D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.claim
   digest: No order on the full eight-crossing presented quandle is strictly increasing in both variables. -/

/- proof_shape: content (full term quotient, universal coloring and order obstruction).
   admission_basis: escape-witness
   escape_witness: d_ne_g separates actual quotient classes through lift and eval_rel;
   result consumes sixRelation_forces_eq, whose live proof constructs a strict-order cycle.
   Direct project dependencies: PresentedQuandle (quotient Quandle, lift, lift_of,
   relation_eq) and SixRelationObstruction.sixRelation_forces_eq.
   lift_unique completes arbitrary-target uniqueness, including inverse terms;
   it is retained general content, not a dependency of result.
   The diagram-to-knot identification is an external source map from arXiv:2505.19573v1,
   fig8_20 and relations 8_20_1--8_20_8; no ambient-isotopy theorem is asserted.
   Repo-prior-exposed implementation; predecessor proof is an attributed input.
   No novelty, current openness, original-resolution or acceptance claim is made here. -/

import D5.S0.Certificates.Quandles.PresentedQuandle
import D5.S0.Certificates.Quandles.SixRelationObstruction

/-! Full presentation and order-obstruction sources; see the corresponding Scribe. -/


namespace D5.S0.Certificates.Quandles.EightTwentyNonBiorderable

open PresentedQuandle

/-- The eight arcs in the original oriented diagram, with the paper's names. -/
inductive Arc
  | a | b | c | d | e | f | g | h
  deriving DecidableEq

/-- All eight original crossings, in their original numbering.
The paper's `x*y` is represented by the actor-first term `act y x`. -/
inductive Crossing : Term Arc → Term Arc → Prop
  | r1 : Crossing (.act (.gen .e) (.gen .b)) (.gen .a)
  | r2 : Crossing (.act (.gen .g) (.gen .c)) (.gen .b)
  | r3 : Crossing (.act (.gen .g) (.gen .d)) (.gen .e)
  | r4 : Crossing (.act (.gen .e) (.gen .g)) (.gen .h)
  | r5 : Crossing (.act (.gen .d) (.gen .f)) (.gen .g)
  | r6 : Crossing (.act (.gen .a) (.gen .d)) (.gen .c)
  | r7 : Crossing (.act (.gen .c) (.gen .a)) (.gen .h)
  | r8 : Crossing (.act (.gen .c) (.gen .f)) (.gen .e)

/-- The genuine full quandle given by this presentation, including inverse-action terms. -/
abbrev KnotQuandle := Carrier Crossing

/-- The named generators in the actual quotient. -/
def arc (x : Arc) : KnotQuandle := of Crossing x

/-- The primary paper's right-quandle operation, with the variables swapped for Mathlib. -/
def op (x y : KnotQuandle) : KnotQuandle := Shelf.act y x

/-- The exact mod-nine separator, used only as a homomorphism target. -/
def color : Arc → Quandle.Dihedral 9
  | .a => (7 : ZMod 9)
  | .b => (6 : ZMod 9)
  | .c => (5 : ZMod 9)
  | .d => (0 : ZMod 9)
  | .e => (2 : ZMod 9)
  | .f => (8 : ZMod 9)
  | .g => (1 : ZMod 9)
  | .h => (3 : ZMod 9)

private theorem color_crossings :
    ∀ x y, Crossing x y → x.eval color = y.eval color := by
  intro x y h
  cases h
  · change (2 * 2 - 6 : ZMod 9) = 7
    decide
  · change (2 * 1 - 5 : ZMod 9) = 6
    decide
  · change (2 * 1 - 0 : ZMod 9) = 2
    decide
  · change (2 * 2 - 1 : ZMod 9) = 3
    decide
  · change (2 * 0 - 8 : ZMod 9) = 1
    decide
  · change (2 * 7 - 0 : ZMod 9) = 5
    decide
  · change (2 * 5 - 7 : ZMod 9) = 3
    decide
  · change (2 * 5 - 8 : ZMod 9) = 2
    decide

/-- Universal evaluation extends the coloring to the entire presented quandle. -/
def colorHom : ShelfHom KnotQuandle (Quandle.Dihedral 9) :=
  lift Crossing color color_crossings

private theorem d_ne_g : arc .d ≠ arc .g := by
  intro h
  have hc : color .d = color .g := by
    simpa only [colorHom, arc, lift_of] using congrArg colorHom h
  change (0 : ZMod 9) = 1 at hc
  exact (by decide : (0 : ZMod 9) ≠ 1) hc

/-- Existence of ONE linear order on ALL elements, with both strict translation laws.
There is no generator-order or order-preservation condition on the coloring. -/
def claim : Prop :=
  ∃ order : LinearOrder KnotQuandle,
    letI := order
    (∀ z, StrictMono (op z)) ∧ (∀ z, StrictMono (fun x => op x z))

/-- Closed full-domain refutation for the exact eight-relation presentation.
Its identification with the oriented knot diagram is the stated external source boundary. -/
theorem result : ¬ claim := by
  rintro ⟨order, hmono⟩
  letI := order
  obtain ⟨hl, hr⟩ := hmono
  apply d_ne_g
  exact SixRelationObstruction.sixRelation_forces_eq op
    (fun _ => Quandle.fix) hl hr
    (arc .a) (arc .c) (arc .d) (arc .e) (arc .f) (arc .g) (arc .h)
    (relation_eq Crossing Crossing.r3)
    (relation_eq Crossing Crossing.r4)
    (relation_eq Crossing Crossing.r5)
    (relation_eq Crossing Crossing.r6)
    (relation_eq Crossing Crossing.r7)
    (relation_eq Crossing Crossing.r8)

end D5.S0.Certificates.Quandles.EightTwentyNonBiorderable
