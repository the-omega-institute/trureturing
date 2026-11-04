/- GID: D5/S0/Certificates/Quandles/PresentedQuandle
   generality: G
   mirror-B: D5/B/S0/Certificates/Quandles/PresentedQuandle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Quandle, mathlib/module/Mathlib.Data.Quot]
   utility: none
   digest: Term presentation of quandles with inverse action and its universal evaluation map. -/

/- proof_shape: content (term congruence, quotient quandle and universal map).
   admission_basis: escape-witness
   escape_witness: lift_unique, by induction on terms including inverse action.
   Consumed by EightTwentyNonBiorderable.colorHom and its separation proof.
   No finite enumeration or numerical reduction is used in this module. -/

import Mathlib.Algebra.Quandle
import Mathlib.Data.Quot

/-! Full presentation and order-obstruction sources; see the corresponding Scribe. -/


namespace D5.S0.Certificates.Quandles.PresentedQuandle

universe u v

/-- Formal quandle expressions; inverse action is essential for a rack presentation. -/
inductive Term (G : Type u) : Type u
  | gen : G → Term G
  | act : Term G → Term G → Term G
  | invAct : Term G → Term G → Term G

/-- Evaluation with Mathlib's actor-first convention. -/
def Term.eval {G : Type u} {Q : Type v} [Quandle Q] (v : G → Q) : Term G → Q
  | .gen g => v g
  | .act x y => Shelf.act (x.eval v) (y.eval v)
  | .invAct x y => Rack.invAct (x.eval v) (y.eval v)

/-- The least equivalence congruence containing the quandle axioms and the relations.
Only these constructors identify terms; no finiteness or extra cancellation is imposed. -/
inductive Rel {G : Type u} (R : Term G → Term G → Prop) : Term G → Term G → Prop
  | refl (x) : Rel R x x
  | symm {x y} : Rel R x y → Rel R y x
  | trans {x y z} : Rel R x y → Rel R y z → Rel R x z
  | act {x x' y y'} : Rel R x x' → Rel R y y' → Rel R (.act x y) (.act x' y')
  | invAct {x x' y y'} : Rel R x x' → Rel R y y' → Rel R (.invAct x y) (.invAct x' y')
  | fix (x) : Rel R (.act x x) x
  | distrib (x y z) : Rel R (.act x (.act y z)) (.act (.act x y) (.act x z))
  | leftInv (x y) : Rel R (.invAct x (.act x y)) y
  | rightInv (x y) : Rel R (.act x (.invAct x y)) y
  | equation {x y} : R x y → Rel R x y

/-- The congruence as a setoid. -/
def congruence {G : Type u} (R : Term G → Term G → Prop) : Setoid (Term G) where
  r := Rel R
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

/-- The full presented quandle, not just the positive-term shelf. -/
abbrev Carrier {G : Type u} (R : Term G → Term G → Prop) : Type u := Quotient (congruence R)

variable {G : Type u} (R : Term G → Term G → Prop)

/-- Generator of the presentation. -/
def of (g : G) : Carrier R := Quotient.mk _ (.gen g)

instance : Quandle (Carrier R) where
  act := Quotient.map₂ (sa := congruence R) (sb := congruence R) (sc := congruence R)
    Term.act (by intro a a' ha b b' hb; exact Rel.act ha hb)
  invAct := Quotient.map₂ (sa := congruence R) (sb := congruence R) (sc := congruence R)
    Term.invAct (by intro a a' ha b b' hb; exact Rel.invAct ha hb)
  self_distrib := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    exact Quotient.sound (Rel.distrib a b c)
  left_inv := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact Quotient.sound (Rel.leftInv a b)
  right_inv := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact Quotient.sound (Rel.rightInv a b)
  fix := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (Rel.fix a)

/-- Every supplied relation holds in the quotient. -/
theorem relation_eq {x y : Term G} (h : R x y) :
    (Quotient.mk (congruence R) x : Carrier R) = Quotient.mk _ y :=
  Quotient.sound (Rel.equation h)

private theorem eval_rel {Q : Type v} [Quandle Q] (v : G → Q)
    (hv : ∀ x y, R x y → x.eval v = y.eval v) {x y : Term G}
    (h : Rel R x y) : x.eval v = y.eval v := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | act _ _ ih₁ ih₂ => exact congrArg₂ Shelf.act ih₁ ih₂
  | invAct _ _ ih₁ ih₂ => exact congrArg₂ Rack.invAct ih₁ ih₂
  | fix => exact Quandle.fix
  | distrib => exact Shelf.self_distrib
  | leftInv => exact Rack.invAct_act_eq _ _
  | rightInv => exact Rack.act_invAct_eq _ _
  | equation h => exact hv _ _ h

/-- A generator assignment satisfying the relations extends to an actual quandle map. -/
def lift {Q : Type v} [Quandle Q] (v : G → Q)
    (hv : ∀ x y, R x y → x.eval v = y.eval v) : ShelfHom (Carrier R) Q where
  toFun := Quotient.lift (Term.eval v) (fun _ _ h => eval_rel R v hv h)
  map_act' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    rfl

/-- The extended map has the prescribed generator values. -/
@[simp] theorem lift_of {Q : Type v} [Quandle Q] (v : G → Q)
    (hv : ∀ x y, R x y → x.eval v = y.eval v) (g : G) :
    lift R v hv (of R g) = v g := rfl

private theorem map_invAct {Q : Type v} [Quandle Q]
    (h : ShelfHom (Carrier R) Q) (x y : Carrier R) :
    h (Rack.invAct x y) = Rack.invAct (h x) (h y) := by
  apply (Rack.act' (h x)).injective
  change Shelf.act (h x) (h (Rack.invAct x y)) =
    Shelf.act (h x) (Rack.invAct (h x) (h y))
  rw [← h.map_act, Rack.act_invAct_eq, Rack.act_invAct_eq]

/-- Uniqueness among all quandle homomorphisms, including on inverse-action terms.
Together with `lift` and `lift_of` this is the required presentation universal property. -/
theorem lift_unique {Q : Type v} [Quandle Q] (v : G → Q)
    (hv : ∀ x y, R x y → x.eval v = y.eval v)
    (h : ShelfHom (Carrier R) Q) (hg : ∀ g, h (of R g) = v g) :
    h = lift R v hv := by
  have ht : ∀ t : Term G, h (Quotient.mk _ t : Carrier R) = t.eval v := by
    intro t
    induction t with
    | gen g => exact hg g
    | act x y hx hy =>
      change h (Shelf.act (Quotient.mk _ x) (Quotient.mk _ y)) =
        Shelf.act (x.eval v) (y.eval v)
      rw [h.map_act, hx, hy]
    | invAct x y hx hy =>
      change h (Rack.invAct (Quotient.mk _ x) (Quotient.mk _ y)) =
        Rack.invAct (x.eval v) (y.eval v)
      rw [map_invAct, hx, hy]
  apply DFunLike.ext
  intro q
  exact Quotient.inductionOn q ht

end D5.S0.Certificates.Quandles.PresentedQuandle
