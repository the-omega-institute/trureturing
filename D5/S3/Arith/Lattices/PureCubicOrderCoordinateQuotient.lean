/- GID: D5/S3/Arith/Lattices/PureCubicOrderCoordinateQuotient
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PureCubicOrderCoordinateQuotient
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.ZMod.QuotientRing]
   utility: none
   digest: Quotient of the cubic order's triangular coordinate lattice. -/

import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient

/-- Coordinates of the original cubic order in a maximal integral basis. -/
def triangularLattice (c d : ℕ) (k v : ℤ) : AddSubgroup (ℤ × ℤ × ℤ) where
  carrier := {x | ∃ a b t : ℤ,
    x = (a - k * v * t, (c : ℤ) * b - k * v * c * t, v * d * t)}
  zero_mem' := by
    refine ⟨0, 0, 0, ?_⟩
    ext <;> simp
  add_mem' := by
    intro x y hx hy
    obtain ⟨a, b, t, rfl⟩ := hx
    obtain ⟨a', b', t', rfl⟩ := hy
    refine ⟨a + a', b + b', t + t', ?_⟩
    ext <;> simp <;> ring
  neg_mem' := by
    intro x hx
    obtain ⟨a, b, t, rfl⟩ := hx
    refine ⟨-a, -b, -t, ?_⟩
    ext <;> simp <;> ring

/-- A unit sign in the third generator removes the off-diagonal term,
leaving cyclic quotients of orders `c` and `d`. -/
theorem triangular_lattice_quotient (c d : ℕ) (k v : ℤ)
    (hc : 0 < c) (hd : 0 < d) (hv : v = 1 ∨ v = -1) :
    Nonempty (((ℤ × ℤ × ℤ) ⧸ triangularLattice c d k v) ≃+
      ZMod c × ZMod d) := by
  letI : NeZero c := ⟨Nat.ne_of_gt hc⟩
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let φ : (ℤ × ℤ × ℤ) →+ ZMod c × ZMod d := {
    toFun := fun x => ((x.2.1 : ZMod c), (x.2.2 : ZMod d))
    map_zero' := by ext <;> simp
    map_add' := by intro x y; ext <;> simp
  }
  have hmem (x : ℤ × ℤ × ℤ) :
      x ∈ triangularLattice c d k v ↔
        (c : ℤ) ∣ x.2.1 ∧ (d : ℤ) ∣ x.2.2 := by
    constructor
    · rintro ⟨a, b, t, hx⟩
      rw [hx]
      constructor
      · refine ⟨b - k * v * t, ?_⟩
        dsimp
        ring
      · refine ⟨v * t, ?_⟩
        dsimp
        ring
    · rintro ⟨⟨b, hb⟩, ⟨s, hs⟩⟩
      refine ⟨x.1 + k * s, b + k * s, v * s, ?_⟩
      rcases hv with rfl | rfl <;> ext <;> simp [hb, hs] <;> ring
  have hker : φ.ker = triangularLattice c d k v := by
    ext x
    change φ x = 0 ↔ x ∈ triangularLattice c d k v
    rw [hmem]
    change ((x.2.1 : ZMod c), (x.2.2 : ZMod d)) = (0, 0) ↔ _
    simp only [Prod.mk.injEq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsurj : Function.Surjective φ := by
    intro y
    refine ⟨(0, (y.1.val : ℤ), (y.2.val : ℤ)), ?_⟩
    apply Prod.ext
    · change ((y.1.val : ℤ) : ZMod c) = y.1
      simp
    · change ((y.2.val : ℤ) : ZMod d) = y.2
      simp
  refine ⟨?_⟩
  rw [← hker]
  exact QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj

#print axioms triangular_lattice_quotient

end D5.S3.Arith.Lattices.PureCubicOrderCoordinateQuotient
