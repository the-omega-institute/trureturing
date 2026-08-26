/- GID: D5/S3/Fourier/CharacterSelection/BinaryCharacterRankAndRedundancy
   generality: G
   mirror-B: D5/B/S3/Fourier/CharacterSelection/BinaryCharacterRankAndRedundancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Binary-character rank counts joint bits and detects redundant roles. -/

import D5.S3.Fourier.BinaryCharacterRedundancyCriterion
import D5.S3.Fourier.CharacterSelection.BinaryCharacterProfileRankCardinality

/- Library-search audit trail (2026-08-26):
   * Exact current-tree searches found the profile-cardinality clause in
     `binary_character_profile_rank_cardinality` and the product-recovery
     clause in `binary_character_redundancy_criterion`, but no single public
     declaration exposes both source clauses.
   * Body-shape searches hit the canonical `AddMonoidHom.pi` profile, binary
     character carrier, span, and finitely supported coefficient product; all
     are imported and instantiated rather than redeclared.
   * Pinned-Mathlib provides `Module.card_eq_pow_finrank`,
     `Finsupp.mem_span_range_iff_exists_finsupp`, and `ofAdd_sum`, but no exact
     theorem combining rank-controlled profiles with redundant-role recovery. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.CharacterSelection.BinaryCharacterRankAndRedundancy

open Module Set
open D5.S3.Fourier.BinaryCharacterRedundancyCriterion
open D5.S3.Fourier.CharacterSelection.BinaryCharacterProfileRankCardinality

set_option maxHeartbeats 2000000 in
-- The imported span-to-product equivalence needs extended elaboration time.
/-- A finite family of binary characters realizes exactly two to its span rank
joint profiles. If one role lies in the span of all other roles, its
multiplicative output is recovered as a finite product of their outputs. -/
theorem binary_character_rank_and_redundancy
    {G : Type*} [AddCommGroup G] [Fintype G]
    {I : Type*} [Fintype I]
    (characters : I -> Module.Dual (ZMod 2) (ModN G 2)) :
    let profileHom : AddMonoidHom G (I -> ZMod 2) :=
      AddMonoidHom.pi fun i =>
        characters i |>.toAddMonoidHom.comp (ModN.mkQ 2)
    let H := Submodule.span (ZMod 2) (Set.range characters)
    let r := Module.finrank (ZMod 2) H
    Fintype.card profileHom.range = 2 ^ r /\
      forall j : I,
        characters j ∈
            Submodule.span (ZMod 2)
              (Set.range
                (fun i : {candidate : I // candidate ≠ j} => characters i.1)) ->
          exists coefficients : {candidate : I // candidate ≠ j} →₀ ZMod 2,
            forall g : G,
              Multiplicative.ofAdd (characters j (ModN.mkQ 2 g)) =
                ∏ i ∈ coefficients.support,
                  Multiplicative.ofAdd
                    (coefficients i * characters i.1 (ModN.mkQ 2 g)) := by
  classical
  dsimp only
  constructor
  · exact (binary_character_profile_rank_cardinality characters).2.1
  · intro j characterInOtherSpan
    exact
      ((binary_character_redundancy_criterion
        (fun i : {candidate : I // candidate ≠ j} => characters i.1)
        (characters j)).out 1 2).mp characterInOtherSpan

#print axioms binary_character_rank_and_redundancy

end D5.S3.Fourier.CharacterSelection.BinaryCharacterRankAndRedundancy
