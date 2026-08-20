/- GID: D5/S0/Diagonal/Equivariance/TransitiveEscapeRate
   generality: G
   mirror-B: D5/B/S0/Diagonal/Equivariance/TransitiveEscapeRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A transitive equivariant ensemble escapes at rate one minus k over n to the omega. -/

import D5.S0.Diagonal.EquivariantEscape
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

open scoped BigOperators

universe u v w

namespace D5.S0.Diagonal.Equivariance.TransitiveEscapeRate

open D5.S0.Diagonal.EscapeCount
open D5.S0.Diagonal.EquivariantEscape

variable {G : Type u} {A : Type v} {Y : Type w}

/- The orbit-coordinate count below re-derives what `EquivariantEscape.off_diagonal_card`
   already knows. That lemma is `private` and its module is frozen, so it cannot be reused
   and cannot be exported; re-deriving it here is the only route that leaves the frozen
   module byte-identical. -/

/-- Every stabilizer-orbit index carries at least the diagonal orbit. -/
theorem stabilizerOrbit_card_pos [Group G] [MulAction G A] [Fintype A]
    (i : OrbitIndex G A) : 0 < Fintype.card (StabilizerOrbit G A i) :=
  Fintype.card_pos_iff.mpr ⟨diagonalOrbit i⟩

/-- The orbit coordinates of an equivariant listing are a diagonal value together with the
remaining stabilizer-orbit coordinates, so they number `n` to the orbit count. -/
theorem orbitParameters_card [Group G] [MulAction G A] [Fintype A] [Fintype Y] :
    Fintype.card (OrbitParameters (G := G) (A := A) Y) =
      ∏ i : OrbitIndex G A, Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i) := by
  classical
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_subtype_compl]
  have hone : Fintype.card {_a : StabilizerOrbit G A i // _a = diagonalOrbit i} = 1 := by
    simp
  rw [hone, ← pow_succ']
  congr 1
  exact Nat.succ_pred_eq_of_pos (stabilizerOrbit_card_pos i)

/-- For a transitive action the equivariant ensemble has exactly `n` to the omega members. -/
theorem transitive_equivariant_listing_card [Group G] [MulAction G A] [Fintype A]
    [Fintype Y] [Nonempty A] [MulAction.IsPretransitive G A]
    (D : OrbitDecomposition (G := G) (A := A) Y) (i₀ : OrbitIndex G A) :
    Nat.card (EquivariantListing G A Y) =
      Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀) := by
  classical
  letI : Unique (OrbitIndex G A) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G A).mp inferInstance)
  rw [Nat.card_congr D.parameters, Nat.card_eq_fintype_card, orbitParameters_card,
    Fintype.prod_unique, Subsingleton.elim default i₀]

/-- Whenever the fixed points do not outnumber the ensemble, the escaped fraction is one
minus the fixed-point fraction. This is the arithmetic step the source states directly. -/
theorem escaped_fraction (N K : ℕ) (hKN : K ≤ N) (hN : N ≠ 0) :
    ((N - K : ℕ) : ℚ) / (N : ℚ) = 1 - (K : ℚ) / (N : ℚ) := by
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [Nat.cast_sub hKN, sub_div, div_self hN']

/-- The three exhaustive readings the source records, in the rate form it states them in. -/
theorem worked_rates :
    (1 : ℚ) - 3 / 3 ^ 3 = 8 / 9 ∧ (1 : ℚ) - 2 / 2 ^ 4 = 7 / 8 ∧
      (1 : ℚ) - 3 / 3 ^ 2 = 2 / 3 := by
  norm_num

/-- The transitive equivariant escape rate packaged: the ensemble has `n` to the omega
members, the escaped ones number that minus the fixed points of the twist, dividing gives
one minus the fixed-point fraction, and the three recorded readings are instances. -/
theorem transitive_equivariant_escape_rate_package [Group G] [MulAction G A] [Fintype A]
    [Fintype Y] [Nonempty A] [MulAction.IsPretransitive G A]
    (D : OrbitDecomposition (G := G) (A := A) Y) (f : Y → Y) (i₀ : OrbitIndex G A) :
    Nat.card (EquivariantListing G A Y) =
        Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀) ∧
      Nat.card {g : EquivariantListing G A Y // IsEscaped f g.1} =
          Fintype.card Y ^ Fintype.card (StabilizerOrbit G A i₀) -
            Nat.card {y : Y // f y = y} ∧
        (∀ N K : ℕ, K ≤ N → N ≠ 0 →
            ((N - K : ℕ) : ℚ) / (N : ℚ) = 1 - (K : ℚ) / (N : ℚ)) ∧
          ((1 : ℚ) - 3 / 3 ^ 3 = 8 / 9 ∧ (1 : ℚ) - 2 / 2 ^ 4 = 7 / 8 ∧
            (1 : ℚ) - 3 / 3 ^ 2 = 2 / 3) :=
  ⟨transitive_equivariant_listing_card D i₀,
    transitive_equivariant_escaped_card D f i₀,
    escaped_fraction, worked_rates⟩

end D5.S0.Diagonal.Equivariance.TransitiveEscapeRate
