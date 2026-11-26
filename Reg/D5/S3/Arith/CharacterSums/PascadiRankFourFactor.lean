import D5.S3.Arith.CharacterSums.PascadiRankFourFactor

/-! Positive source law for the rank-four factor, with the universe-polymorphic
finite row type, whole integer matrix, prime and lifts, heights, all three
gaps, and every admissible baseline. A dependent readout would have to
reconstruct the hypotheses and the rank and factor conclusions across the
whole family, including lower-rank fibers and the baseline unit. The lawful
enrollment, realization bridge, source selection, whole-family variation,
sensitivity and observational dependence remain open under issue #31456. -/

namespace Reg.D5.S3.Arith.CharacterSums.PascadiRankFourFactor


abbrev rank_four_root_relevant_factor_scope.{u} :=
  type_of% (@_root_.D5.S3.Arith.CharacterSums.PrimeCube.rank_four_root_relevant_factor.{u})

theorem rank_four_root_relevant_factor_actual.{u} :
    rank_four_root_relevant_factor_scope.{u} :=
  @_root_.D5.S3.Arith.CharacterSums.PrimeCube.rank_four_root_relevant_factor.{u}

end Reg.D5.S3.Arith.CharacterSums.PascadiRankFourFactor
