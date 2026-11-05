/- GID: D5/S0/Certificates/Quandles/BraidColoringTransport
   generality: G
   anchors: [lake/module/Mathlib.Algebra.Quandle]
   utility: none
   digest: A rack crossing is an invertible local coloring transport and satisfies the Yang--Baxter relation.
-/

import Mathlib.Algebra.Quandle

/-!
# Quandle crossing transport

The algebraic content behind a Reidemeister crossing is the rack map
`(x,y) ↦ (x ◃ y,x)`.  Its inverse uses `invAct`, so this is a genuine
boundary-color transport rather than just a restatement of an axiom.  The
three-crossing Yang--Baxter equation is exactly self-distributivity.  These
maps are the local core needed by a later finite crossing-system coloring
invariant.
-/

open scoped Quandles

namespace D5.S0.Certificates.Quandles.BraidColoringTransport

variable {Q : Type*} [Rack Q]

/-- The ordered pair of colors after one oriented rack crossing. -/
def crossing (p : Q × Q) : Q × Q := (p.1 ◃ p.2, p.1)

/-- The inverse local transport, with the boundary colors read backwards. -/
def crossingInv (p : Q × Q) : Q × Q := (p.2, p.2 ◃⁻¹ p.1)

theorem crossingInv_crossing (p : Q × Q) : crossingInv (crossing p) = p := by
  rcases p with ⟨x, y⟩
  simp [crossing, crossingInv]

theorem crossing_crossingInv (p : Q × Q) : crossing (crossingInv p) = p := by
  rcases p with ⟨x, y⟩
  simp [crossing, crossingInv]

/-- A rack crossing is a boundary-preserving bijection of color pairs. -/
def crossingEquiv : Q × Q ≃ Q × Q where
  toFun := crossing
  invFun := crossingInv
  left_inv := crossingInv_crossing
  right_inv := crossing_crossingInv

@[simp] theorem crossingEquiv_apply (p : Q × Q) : crossingEquiv p = crossing p := rfl

@[simp] theorem crossingEquiv_symm_apply (p : Q × Q) : crossingEquiv.symm p = crossingInv p := rfl

/-- Apply the crossing to the first two strands of a three-strand state. -/
def crossing₁ (p : Q × (Q × Q)) : Q × (Q × Q) :=
  (p.1 ◃ p.2.1, (p.1, p.2.2))

/-- Apply the crossing to the last two strands of a three-strand state. -/
def crossing₂ (p : Q × (Q × Q)) : Q × (Q × Q) :=
  (p.1, (p.2.1 ◃ p.2.2, p.2.1))

theorem crossing_yang_baxter (x y z : Q) :
    crossing₁ (crossing₂ (crossing₁ (x, (y, z)))) =
      crossing₂ (crossing₁ (crossing₂ (x, (y, z)))) := by
  simpa only [crossing₁, crossing₂] using
    congrArg (fun w : Q => (w, ((x ◃ y), x)))
      (Shelf.self_distrib (x := x) (y := y) (z := z)).symm

/-- The inverse transport gives the cardinality-preserving local move witness. -/
theorem crossing_card_bijective : Function.Bijective (crossing : Q × Q → Q × Q) :=
  crossingEquiv.bijective

end D5.S0.Certificates.Quandles.BraidColoringTransport

#print axioms D5.S0.Certificates.Quandles.BraidColoringTransport.crossing_yang_baxter
#print axioms D5.S0.Certificates.Quandles.BraidColoringTransport.crossing_card_bijective
