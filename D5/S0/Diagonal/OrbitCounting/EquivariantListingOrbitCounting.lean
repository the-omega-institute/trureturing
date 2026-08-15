/- GID: D5/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting
   generality: G
   mirror-B: D5/B/S0/Diagonal/OrbitCounting/EquivariantListingOrbitCounting
   mirror-E: none(waiver:finite-cardinality theorem has no separate evidence artifact)
   anchors: [mathlib/module/Mathlib.GroupTheory.GroupAction.Quotient]
   digest: Burnside averaging counts equivariant listings through diagonal-action orbits. -/

import D5.S0.Diagonal.EquivariantEscape
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped BigOperators

universe u v w

namespace D5.S0.Diagonal.OrbitCounting.EquivariantListingOrbitCounting

open D5.S0.Diagonal.EquivariantEscape

variable {G : Type u} {A : Type v} {Y : Type w}

/-- An equivariant listing is exactly a function on the orbits of the diagonal
action on pairs of addresses. -/
noncomputable def equivariantListingOrbitEquiv [Group G] [MulAction G A] :
    EquivariantListing G A Y ≃ (OrbitIndex G (A × A) → Y) where
  toFun g q := Quotient.liftOn' q (fun ab => g.1 ab.1 ab.2) fun ab cd h => by
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨σ, rfl⟩ := h
    change g.1 (σ • cd.1) (σ • cd.2) = g.1 cd.1 cd.2
    exact g.2 σ cd.1 cd.2
  invFun h :=
    ⟨fun a b => h (Quotient.mk'' (a, b)), by
      intro σ a b
      apply congrArg h
      simpa using Quotient.sound' (MulAction.mem_orbit (a, b) σ)⟩
  left_inv g := by
    apply Subtype.ext
    funext a b
    rfl
  right_inv h := by
    funext q
    induction q using Quotient.inductionOn' with
    | _ ab => rfl

/-- The number of equivariant listings is the number of value assignments to
the diagonal-action orbits of address pairs. -/
theorem equivariant_listing_card_orbits [Group G] [MulAction G A]
    [Fintype A] [Fintype Y] :
    Nat.card (EquivariantListing G A Y) =
      Fintype.card Y ^ Fintype.card (OrbitIndex G (A × A)) := by
  classical
  rw [Nat.card_congr
    (equivariantListingOrbitEquiv (G := G) (A := A) (Y := Y))]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun]

/-- Burnside's orbit average supplies the exponent in the equivariant-listing count. -/
theorem equivariant_listing_card_burnside [Fintype G] [Group G] [MulAction G A]
    [Finite A] [Fintype Y] :
    Nat.card (EquivariantListing G A Y) =
      Fintype.card Y ^
        ((∑ σ : G, Nat.card (MulAction.fixedBy (A × A) σ)) /
          Fintype.card G) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI (σ : G) : Fintype (MulAction.fixedBy (A × A) σ) :=
    Fintype.ofFinite _
  have hG : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hBurnside :
      (∑ σ : G, Nat.card (MulAction.fixedBy (A × A) σ)) /
          Fintype.card G =
        Fintype.card (OrbitIndex G (A × A)) := by
    simp_rw [Nat.card_eq_fintype_card]
    rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group]
    rw [Nat.mul_comm (Fintype.card (OrbitIndex G (A × A))) (Fintype.card G)]
    exact Nat.mul_div_right (Fintype.card (OrbitIndex G (A × A))) hG
  rw [equivariant_listing_card_orbits, hBurnside]

#print axioms equivariantListingOrbitEquiv
#print axioms equivariant_listing_card_orbits
#print axioms equivariant_listing_card_burnside

end D5.S0.Diagonal.OrbitCounting.EquivariantListingOrbitCounting
