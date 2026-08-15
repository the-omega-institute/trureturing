/- GID: D5/S0/Diagonal/Probability/GeneralEquivariantEscape
   generality: G
   mirror-B: D5/B/S0/Diagonal/Probability/GeneralEquivariantEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Uniform equivariant escape probability factors over every address orbit. -/

import D5.S0.Diagonal.Probability.EquivariantEscape

open scoped BigOperators ENNReal

universe u v w

namespace D5.S0.Diagonal.Probability.GeneralEquivariantEscape

open D5.S0.Diagonal
open Diagonal.EscapeCount Diagonal.EquivariantEscape

variable {G : Type u} {A : Type v} {Y : Type w}

/- Library-search audit trail (2026-08-15):
   * `D5/` contains the general orbit-product count as `equivariant_escaped_card`
     and only the transitive probability theorem
     `transitive_equivariant_escape_probability`; no general-action probability
     declaration was found.
   * Pinned Mathlib supplies the exact uniform-event bridge
     `PMF.toOuterMeasure_uniformOfFintype_apply`, the finite dependent-product
     count `Fintype.card_pi`, and the finite-product/cast arithmetic used below.
     No theorem packages this orbit-decomposition probability formula. -/

/-- For an arbitrary finite action, uniform equivariant escape probability is the ratio of
the orbit-product escape count to the orbit-product listing count. -/
theorem general_equivariant_escape_probability [Group G] [MulAction G A]
    [Fintype A] [Fintype Y] [Nonempty Y]
    (D : OrbitDecomposition (G := G) (A := A) Y) (f : Y -> Y) :
    (PMF.uniformOfFintype (EquivariantListing G A Y)).toOuterMeasure
        {g | IsEscaped f g.1} =
      (↑(∏ i : OrbitIndex G A,
          (Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) -
            Nat.card {y : Y // f y = y})) : ℝ≥0∞) /
        (↑(∏ i : OrbitIndex G A,
          Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i)) : ℝ≥0∞) := by
  classical
  have hListingCard :
      Nat.card (EquivariantListing G A Y) =
        ∏ i : OrbitIndex G A,
          Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) := by
    rw [Nat.card_congr D.parameters, Nat.card_eq_fintype_card, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro i _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_subtype_compl]
    simp only [Fintype.card_unique]
    rw [← pow_succ']
    congr 1
    exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨diagonalOrbit i⟩)
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hEscapedCard :
      Fintype.card ↥({g | IsEscaped f g.1} : Set (EquivariantListing G A Y)) =
        Nat.card ↥({g | IsEscaped f g.1} : Set (EquivariantListing G A Y)) :=
    Nat.card_eq_fintype_card.symm
  have hTotalCard :
      Fintype.card (EquivariantListing G A Y) =
        Nat.card (EquivariantListing G A Y) :=
    Nat.card_eq_fintype_card.symm
  rw [hEscapedCard, hTotalCard]
  change
    (Nat.card {g : EquivariantListing G A Y // IsEscaped f g.1} : ℝ≥0∞) /
        (Nat.card (EquivariantListing G A Y) : ℝ≥0∞) = _
  rw [equivariant_escaped_card D f, hListingCard]

/-- Under a pretransitive action the general orbit-product formula agrees with the frozen
transitive escape probability. Stated as an equality of the two right-hand sides so that neither
theorem is restated: both are imported and applied in the proof. -/
theorem general_orbit_product_eq_frozen_transitive
    [Group G] [MulAction G A] [Fintype A] [Fintype Y]
    [Nonempty A] [Nonempty Y] [MulAction.IsPretransitive G A]
    (D : OrbitDecomposition (G := G) (A := A) Y) (f : Y -> Y)
    (i₀ : OrbitIndex G A) :
    (↑(∏ i : OrbitIndex G A,
        (Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) -
          Nat.card {y : Y // f y = y})) : ℝ≥0∞) /
      (↑(∏ i : OrbitIndex G A,
        Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i)) : ℝ≥0∞) =
      1 -
        (↑(Nat.card {y : Y // f y = y}) : ℝ≥0∞) /
          (↑(Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀)) : ℝ≥0∞) := by
  classical
  rw [← general_equivariant_escape_probability D f,
    D5.S0.Diagonal.Probability.EquivariantEscape.transitive_equivariant_escape_probability f i₀]

#print axioms general_equivariant_escape_probability
#print axioms general_orbit_product_eq_frozen_transitive

end D5.S0.Diagonal.Probability.GeneralEquivariantEscape
