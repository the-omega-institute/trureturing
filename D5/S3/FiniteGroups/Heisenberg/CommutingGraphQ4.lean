/- GID: D5/S3/FiniteGroups/Heisenberg/CommutingGraphQ4
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Heisenberg/CommutingGraphQ4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime-sixth-order non-isoclinic groups with isomorphic full commuting graphs. -/

import D5.S3.FiniteGroups.Heisenberg.CommutingGraph
import D5.S3.FiniteGroups.Heisenberg.PrimeSquareCoordinates
import D5.S3.FiniteGroups.SubgroupConjugacyRatio

/-! # The second sentence of Q4 in Aspects of the commuting graph

The groups are Heisenberg triples over the prime-square residue ring and the dual
numbers over its residue field. The graph comparison retains every central coordinate.
-/

namespace D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4

open SubgroupConjugacyRatio

variable (p : ℕ) [Fact p.Prime]

/-- The integer-residue Heisenberg witness. -/
abbrev squareGroup : FiniteGroup where
  Carrier := HeisenbergGroup (PrimeSquare p)
  group := inferInstance
  finite := inferInstance

/-- The dual-number Heisenberg witness. -/
abbrev dualGroup : FiniteGroup where
  Carrier := HeisenbergGroup (PrimeDual p)
  group := inferInstance
  finite := by
    let : Finite (PrimeDual p) := inferInstanceAs (Finite (ZMod p × ZMod p))
    infer_instance

noncomputable def graphIso :
    commutingGraph (squareGroup p).Carrier ≃g commutingGraph (dualGroup p).Carrier :=
  liftGraphIso ((squareCoordinates p).determinantEquiv (dualCoordinates p)) (squareCode p)
    ((squareCoordinates p).determinantEquiv_preserves (dualCoordinates p))

private theorem dual_derived_killed (g : sourceDerived (dualGroup p).Carrier) : g ^ p = 1 := by
  have hxy : g.val.x = 0 ∧ g.val.y = 0 :=
    (sourceDerived_axis (PrimeDual p)).le g.property
  apply Subtype.ext
  change (g.val ^ p : HeisenbergGroup (PrimeDual p)) = 1
  rw [HeisenbergGroup.pow_eq]
  change _ = (⟨0, 0, 0⟩ : HeisenbergGroup (PrimeDual p))
  ext <;> simp [hxy.1, hxy.2]

private def squareDerivedOne : sourceDerived (squareGroup p).Carrier :=
  ⟨⟨0, 0, 1⟩, by rw [sourceDerived_axis]; exact ⟨rfl, rfl⟩⟩

private theorem square_derived_not_killed : (squareDerivedOne p) ^ p ≠ 1 := by
  intro h
  have hz := congrArg (fun a : sourceDerived (squareGroup p).Carrier => a.val.z) h
  change ((squareDerivedOne p).val ^ p).z = (0 : PrimeSquare p) at hz
  have hp : (p : PrimeSquare p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (Fact.out : p.Prime).pos (by
      have := (Fact.out : p.Prime).one_lt
      nlinarith)
  apply hp
  simpa [squareDerivedOne, HeisenbergGroup.pow_eq, nsmul_eq_mul] using hz

/-- The derived-subgroup exponent obstruction rules out source isoclinism. -/
theorem not_isoclinic : ¬ Isoclinic (squareGroup p).Carrier (dualGroup p).Carrier := by
  rintro ⟨a, b, hab⟩
  have h := dual_derived_killed p (b (squareDerivedOne p))
  have h' : (squareDerivedOne p) ^ p = 1 := b.injective (by simpa using h)
  exact square_derived_not_killed p h'

/-- Exact all-prime existence event, with the full simple commuting graphs. -/
def ExactEvent : Prop :=
  ∀ p : ℕ, p.Prime → ∃ G H : FiniteGroup,
    Nat.card G.Carrier = p ^ 6 ∧ Nat.card H.Carrier = p ^ 6 ∧
      Nonempty (commutingGraph G.Carrier ≃g commutingGraph H.Carrier) ∧
      ¬ Isoclinic G.Carrier H.Carrier

/-- Non-isoclinic examples exist at order p⁶ for every prime p, including 2. -/
theorem result : ExactEvent := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨squareGroup p, dualGroup p, ?_, ?_, ⟨graphIso p⟩, not_isoclinic p⟩
  · change Nat.card (HeisenbergGroup (PrimeSquare p)) = p ^ 6
    rw [HeisenbergGroup.card_eq, Nat.card_eq_fintype_card, ZMod.card]
    ring
  · change Nat.card (HeisenbergGroup (PrimeDual p)) = p ^ 6
    rw [HeisenbergGroup.card_eq]
    change Nat.card (ZMod p × ZMod p) ^ 3 = p ^ 6
    rw [Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card]
    ring

end D5.S3.FiniteGroups.Heisenberg.CommutingGraphQ4
