module

public import OmegaBuild.Commands
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
Omega original.

The component part of the regular commutative-monoid refinement argument.
The algebraic preorder is kept as an existence relation: no cancellation or
ambient order is assumed.  In particular, the idempotent identity obtained
for a component is an element of the original additive monoid.
-/

compile_only_with_mathlib

@[expose] public section

namespace Omega.Refinement.Regular

universe u

variable {K : Type u} [AddCommMonoid K]

/-- Regularity in the additive convention used by the refinement theorem. -/
def AddRegular (K : Type u) [AddCommMonoid K] : Prop :=
  ∀ x : K, ∃ y : K, x + y + x = x

/-- The algebraic preorder: `x ≤ₐ y` means that `y` has an additive difference
from `x`.  It is not asserted to be antisymmetric on the whole monoid. -/
def AlgebraicLE (x y : K) : Prop := ∃ t : K, x + t = y

/-- An additive idempotent. -/
def Idempotent (e : K) : Prop := e + e = e

/-- Two elements lie in the same component with idempotent identity `e`. -/
def InComponent (e x : K) : Prop := AlgebraicLE e x ∧ AlgebraicLE x e

theorem algebraicLE_trans {x y z : K} (hxy : AlgebraicLE x y)
    (hyz : AlgebraicLE y z) : AlgebraicLE x z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨v, hv⟩
  refine ⟨u + v, ?_⟩
  calc
    x + (u + v) = (x + u) + v := by ac_rfl
    _ = y + v := by rw [hu]
    _ = z := hv

/-- The algebraic preorder is antisymmetric on idempotents. -/
theorem idempotent_antisymm {e f : K} (he : Idempotent e)
    (hf : Idempotent f) (hef : AlgebraicLE e f) (hfe : AlgebraicLE f e) : e = f := by
  rcases hef with ⟨t, ht⟩
  rcases hfe with ⟨s, hs⟩
  have h₁ : e + f = f := by
    calc
      e + f = e + (e + t) := by rw [ht]
      _ = (e + e) + t := by ac_rfl
      _ = e + t := by rw [he]
      _ = f := ht
  have h₂ : f + e = e := by
    calc
      f + e = f + (f + s) := by rw [hs]
      _ = (f + f) + s := by ac_rfl
      _ = f + s := by rw [hf]
      _ = e := hs
  calc
    e = e + f := by simpa [add_comm] using h₂.symm
    _ = f := h₁

/-- A regular element has an idempotent above and below it in the algebraic
preorder, so it belongs to an idempotent component. -/
theorem regular_component_idempotent (hreg : AddRegular K) (x : K) :
    ∃ e : K, Idempotent e ∧ InComponent e x := by
  rcases hreg x with ⟨y, hy⟩
  refine ⟨x + y, ?_, ?_⟩
  · calc
      (x + y) + (x + y) = (x + y + x) + y := by ac_rfl
      _ = x + y := by rw [hy]
  · exact ⟨⟨x, hy⟩, ⟨y, rfl⟩⟩

/-- The idempotent identity of a regular component is unique. -/
theorem component_idempotent_unique {e f x : K} (he : Idempotent e)
    (hf : Idempotent f) (hxe : InComponent e x) (hxf : InComponent f x) : e = f := by
  exact idempotent_antisymm he hf
    (algebraicLE_trans hxe.1 hxf.2)
    (algebraicLE_trans hxf.1 hxe.2)

/-- Every regular element has a unique idempotent component identity. -/
theorem exists_unique_component_idempotent (hreg : AddRegular K) (x : K) :
    ∃! e : K, Idempotent e ∧ InComponent e x := by
  obtain ⟨e, he, hxe⟩ := regular_component_idempotent hreg x
  refine ⟨e, ⟨he, hxe⟩, ?_⟩
  intro f hf
  exact (component_idempotent_unique he hf.1 hxe hf.2).symm

/-- Components add in the original monoid, with the sum of their identities. -/
theorem component_add {e f x y : K} (he : Idempotent e) (hf : Idempotent f)
    (hxe : InComponent e x) (hyf : InComponent f y) :
    Idempotent (e + f) ∧ InComponent (e + f) (x + y) := by
  rcases hxe.1 with ⟨u, hu⟩
  rcases hxe.2 with ⟨u', hu'⟩
  rcases hyf.1 with ⟨v, hv⟩
  rcases hyf.2 with ⟨v', hv'⟩
  refine ⟨?_, ⟨⟨u + v, ?_⟩, ⟨u' + v', ?_⟩⟩⟩
  · exact IsIdempotentElem.mul
      (S := Multiplicative K) (a := Multiplicative.ofAdd e)
      (b := Multiplicative.ofAdd f) he hf
  · calc
      (e + f) + (u + v) = (e + u) + (f + v) := by ac_rfl
      _ = x + y := by rw [hu, hv]
  · calc
      (x + y) + (u' + v') = (x + u') + (y + v') := by ac_rfl
      _ = e + f := by rw [hu', hv']

/-- The idempotent acts as the identity on its component. Global regularity
is not needed for this component calculation. -/
theorem component_identity {e x : K} (he : Idempotent e)
    (hx : InComponent e x) : e + x = x := by
  obtain ⟨y, hy⟩ := hx.1
  calc
    e + x = e + (e + y) := by rw [hy]
    _ = (e + e) + y := by ac_rfl
    _ = e + y := by rw [he]
    _ = x := hy

/-- Every element in an idempotent component has an inverse in that component,
whose sum with it is the component identity, rather than the global zero. -/
theorem component_inverse {e x : K} (he : Idempotent e)
    (hx : InComponent e x) : ∃ y : K, InComponent e y ∧ x + y = e := by
  obtain ⟨z, hz⟩ := hx.2
  have h : x + (z + e) = e := by
    calc
      x + (z + e) = (x + z) + e := by ac_rfl
      _ = e + e := by rw [hz]
      _ = e := he
  refine ⟨z + e, ⟨⟨z, add_comm _ _⟩, ⟨x, ?_⟩⟩, h⟩
  simpa [add_comm] using h

/-- An idempotent below an element is absorbed by it. -/
theorem idempotent_absorb {e x : K} (he : Idempotent e)
    (h : AlgebraicLE e x) : x + e = x := by
  obtain ⟨t, ht⟩ := h
  calc
    x + e = (e + t) + e := by rw [ht]
    _ = (e + e) + t := by ac_rfl
    _ = e + t := by rw [he]
    _ = x := ht

/-- Adding an idempotent above an element places it in that component. -/
theorem component_offset {e x : K} (he : Idempotent e)
    (h : AlgebraicLE x e) : InComponent e (x + e) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨⟨x, add_comm _ _⟩, ⟨t, ?_⟩⟩
  calc
    (x + e) + t = (x + t) + e := by ac_rfl
    _ = e + e := by rw [ht]
    _ = e := he

end Omega.Refinement.Regular
