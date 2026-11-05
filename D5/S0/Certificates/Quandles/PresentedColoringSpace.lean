/- GID: D5/S0/Certificates/Quandles/PresentedColoringSpace
   generality: G
   anchors: [lake/module/D5.S0.Certificates.Quandles.PresentedQuandle]
   utility: none
   digest: Satisfying generator assignments are equivalent to homomorphisms from a presented quandle.
-/

import D5.S0.Certificates.Quandles.PresentedQuandle

/-!
# Coloring spaces of presented quandles

For a term relation `R`, a coloring is a generator assignment satisfying every
supplied relation.  The universal map of `PresentedQuandle` upgrades such an
assignment to a quandle homomorphism, and the theorem below proves the inverse
construction and uniqueness.  This is the algebraic bridge needed before a
crossing-system coloring count can be transported through Reidemeister moves.
-/

open scoped Quandles

namespace D5.S0.Certificates.Quandles.PresentedQuandle

universe u v

variable {G : Type u} {Q : Type v} [Quandle Q]

/-- Generator colorings satisfying all relations in a presentation. -/
def RelColoring (R : Term G → Term G → Prop) (Q : Type v) [Quandle Q] :=
  {v : G → Q // ∀ x y, R x y → x.eval v = y.eval v}

private theorem map_invAct_of_shelfHom
    (f : ShelfHom (Carrier R) Q) (x y : Carrier R) :
    f (Rack.invAct x y) = Rack.invAct (f x) (f y) := by
  apply (Rack.act' (f x)).injective
  change Shelf.act (f x) (f (Rack.invAct x y)) =
    Shelf.act (f x) (Rack.invAct (f x) (f y))
  rw [← f.map_act, Rack.act_invAct_eq, Rack.act_invAct_eq]

/-- The universal property identifies the coloring space with its hom space. -/
def satisfyingAssignmentsEquiv (R : Term G → Term G → Prop) :
    RelColoring R Q ≃ ShelfHom (Carrier R) Q where
  toFun v := lift R v.1 v.2
  invFun f := ⟨fun g => f (of R g), by
    intro x y hxy
    have eval_eq : ∀ t : Term G,
        t.eval (fun g => f (of R g)) = f (Quotient.mk _ t : Carrier R) := by
      intro t
      induction t with
      | gen g => rfl
      | act x y hx hy =>
          change Shelf.act (x.eval (fun g => f (of R g)))
              (y.eval (fun g => f (of R g))) =
            f (Shelf.act (Quotient.mk _ x : Carrier R) (Quotient.mk _ y))
          rw [hx, hy, f.map_act]
      | invAct x y hx hy =>
          change Rack.invAct (x.eval (fun g => f (of R g)))
              (y.eval (fun g => f (of R g))) =
            f (Rack.invAct (Quotient.mk _ x : Carrier R) (Quotient.mk _ y))
          rw [hx, hy, map_invAct_of_shelfHom f]
    rw [eval_eq x, eval_eq y]
    exact congrArg f (relation_eq R hxy)⟩
  left_inv v := by
    apply Subtype.ext
    funext g
    exact lift_of R v.1 v.2 g
  right_inv f := by
    apply (lift_unique R (fun g => f (of R g)) _ f (fun g => rfl)).symm

@[simp] theorem satisfyingAssignmentsEquiv_apply
    (R : Term G → Term G → Prop) (v : RelColoring R Q) :
    satisfyingAssignmentsEquiv R v = lift R v.1 v.2 := rfl

@[simp] theorem satisfyingAssignmentsEquiv_symm_apply_of
    (R : Term G → Term G → Prop) (f : ShelfHom (Carrier R) Q) (g : G) :
    ((satisfyingAssignmentsEquiv R).symm f).1 g = f (of R g) := rfl

end D5.S0.Certificates.Quandles.PresentedQuandle

#print axioms D5.S0.Certificates.Quandles.PresentedQuandle.satisfyingAssignmentsEquiv
