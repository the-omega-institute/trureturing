/- GID: D5/S3/AnalyticClosure/MetallicAnchorExceptional
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first metallic Beatty anchor holds exactly at parameters zero and one. -/

import Mathlib
import D5.S0.Asymptotics.MetallicFamily
import D5.S3.Analytic.GoldenEulerBeta

/- Provenance: Native proof over pinned mathlib. -/

/- Search receipt (2026-08-21).

   Candidates searched and inspected:
   * Every top-level Lean file in `D5/S0/Asymptotics`: `DensePhaseEscapeIdentity`,
     `DensePhaseUnrealizable`, `EscapeProbabilityMonotone`,
     `FinitePartitionCellMeasure`, `FiniteProgramLevelSet`,
     `FixedPointFreeEscapeProbability`, `GreenClassRadius`, `MetallicFamily`,
     `NameSetDistanceSandwich`, `OddCycleDrift`, `PoissonWeightDecay`, and
     `SkewedEscapeMass`.
   * Every top-level Lean file in `D5/S3/Analytic`: `AlternatingPoleCoefficients`,
     `CompletedZetaMellinReconstruction`, `DiagonalCollapse`, `GoldenEulerBeta`,
     `LedgerLengthGrowth`, `LiCausalTrichotomy`, `PoleLayerSelection`,
     `PrimeCashflowCost`, `ScaledPoleAccumulation`, `TailCertificate`,
     `TailClosure`, and `ZetaGibbs`.
   * Every Lean file then present in `D5/S3/AnalyticClosure`:
     `CofinalTailDiscipline`, `GoldenApproximationConstant`,
     `HeatNormalizationImpossibility`, and `PrimeSpectrumHeatAbscissa`.
   * Both pinned files in `Mathlib/NumberTheory/Real`: `GoldenRatio.lean` and
     `Irrational.lean`. Irrationality candidates inspected there include
     `irrational_nrt_of_notint_nrt`, `irrational_sqrt_natCast_iff`,
     `Nat.Prime.irrational_sqrt`, and the arithmetic closure lemmas in the
     `Irrational` namespace.
   * Every pinned file in `Mathlib/Algebra/Order/Floor`: `Defs.lean`, `Div.lean`,
     `Extended.lean`, `Ring.lean`, `Semifield.lean`, and `Semiring.lean`.
   * Every pinned file in `Mathlib/Analysis/Real`: `Cardinality.lean`,
     `Hyperreal.lean`, `OfDigits.lean`, `Spectrum.lean`, and `Sqrt.lean`.
     The square-root comparison declarations in `Sqrt.lean` supplied the
     shortest route.
   * Repository searches for `metallicValue` together with floors, squares,
     anchors, or quadratic identities, and for the declaration-name fragments
     `MetallicAnchorExceptional` and `metallic_anchor_exceptional`, found no
     equivalent proposition under another name. This was the SL-028 self-check.
   * Existing uses of `Real.goldenRatio_irrational` were inspected, including
     `D5/S1/Words/GoldenFiberCoordinates.lean` and
     `D5/S1/Words/Mechanical/MechanicalPeriodicity.lean`. They show the standard
     `Irrational.natCast_mul` and contradiction patterns, but do not state this
     classification.

   Load-bearing declarations in the proof below:
   * `D5.S0.Asymptotics.MetallicFamily.metallicValue` and
     `metallic_family_value` give the family member and its explicit radical.
   * `Real.sqrt_nonneg`, `Real.sq_sqrt`, and `Real.sqrt_lt'` establish that the
     radical lies above `n` and below `n + 1`; these comparisons yield both
     `n < metallicValue n` and `2 * metallicValue n < 2 * n + 1`.
   * `Int.floor_le_iff` turns the latter strict threshold into the integer bound
     `floor (2 * metallicValue n) <= 2 * n`.
   * `mul_pos` and `sub_pos.mpr` make the final comparison strict once `2 <= n`.
   * `D5.S3.Analytic.GoldenEulerBeta.o5Beta`, `o5_beta_power_law`, and
     `Real.goldenRatio` discharge the affirmative parameter-one case; the
     definitions `metallicBeta` and `metallicValue` discharge parameter zero.
   * `positivity` discharges the nonnegativity side conditions of
     `Real.sq_sqrt` and `Real.sqrt_lt'`; without it neither of those lemmas
     applies. `simpa` closes the parameter-one branch by unfolding `o5Beta`
     onto `o5_beta_power_law`.
   * The tactics `exact_mod_cast`, `norm_num`, `nlinarith`, `omega`, and
     `interval_cases` perform only the displayed cast and arithmetic
     bookkeeping around those declarations.

   Near-neighbours deliberately not used as proof ingredients:
   * `Mathlib/NumberTheory/Real/Irrational.lean:131` gives the exact nonsquare
     criterion `irrational_sqrt_natCast_iff`. The radicand is nonsquare for every
     positive parameter (the squeeze needs a separate parameter-one case), but
     irrationality is unnecessary: the radical and floor inequalities prove
     the stronger strict failure directly.
   * `D5/S1/Words/GoldenFiberCoordinates.lean:48` contains related floor and
     irrationality manipulation for the golden ratio, not for the metallic
     family, so importing it would add an instance-specific dependency without
     shortening this proof.

   Boundary, closure, and address checks:
   * Direct calculation gives `metallicValue 0 = 1`, and its first anchor holds.
     Parameter one has irrational radicand five and also holds. For every
     parameter at least two the proof below gives a strict inequality, not just
     disequality.
   * Run-local probes of the elaborated classification with `decide`, `simp`,
     `omega`, and `norm_num` all left the proposition unclosed.
   * The shortest found proof has four substantive stages after the small
     cases: radical bounds, a floor threshold, the quadratic identity, and a
     positive-gap comparison. It is not a single application of an existing
     declaration.
   * The two thematically nearest homes are unavailable: `D5/S0/Asymptotics`,
     which holds `MetallicFamily`, and `D5/S3/Analytic`, which holds
     `GoldenEulerBeta`, each sit at the split threshold and would cross it.
     `D5/S3/AnalyticClosure` already hosts conclusions that close analytic
     instance questions, and in every tree consulted while preparing this file
     it sits well below the threshold with this file added. Exact occupancy
     counts are deliberately not recorded here: they differ between the
     worktree this proof was written in and the integration branch, and would
     go stale on the next landing in that directory.

   The inspected-candidate and load-bearing lists are separate. The search
   surface is not claimed exhaustive; the load-bearing list is complete for
   the proof body below. -/

namespace D5.S3.AnalyticClosure.MetallicAnchorExceptional

open D5.S0.Asymptotics.MetallicFamily
open D5.S3.Analytic.GoldenEulerBeta

/-- The Beatty-shaped exponent account obtained by replacing the golden ratio
with the parameter-`n` metallic value. -/
noncomputable def metallicBeta (n v : Nat) : Real :=
  ((⌊(((v + 1 : Nat) : Real) * metallicValue n)⌋ : Int) : Real) - 1 -
    (v : Real) * (1 - metallicValue n)

private theorem metallic_beta_first_strict_failure (n : Nat) (hn : 2 ≤ n) :
    metallicBeta n 1 < metallicValue n ^ 2 := by
  let μ := metallicValue n
  have hdef :
      μ = ((n : Real) + Real.sqrt ((n : Real) ^ 2 + 4)) / 2 :=
    metallic_family_value n |>.1
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((n : Real) ^ 2 + 4) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt ((n : Real) ^ 2 + 4) ^ 2 = (n : Real) ^ 2 + 4 := by
    rw [Real.sq_sqrt]
    positivity
  have hnreal : (2 : Real) ≤ n := by
    exact_mod_cast hn
  have hmu_gt : (n : Real) < μ := by
    rw [hdef]
    nlinarith
  have hsqrt_lt :
      Real.sqrt ((n : Real) ^ 2 + 4) < (n : Real) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    nlinarith
  have htwo_mu_lt : 2 * μ < 2 * (n : Real) + 1 := by
    rw [hdef]
    nlinarith
  have hfloor_int : ⌊2 * μ⌋ ≤ 2 * (n : Int) := by
    rw [Int.floor_le_iff]
    norm_num
    exact htwo_mu_lt
  have hfloor : ((⌊2 * μ⌋ : Int) : Real) ≤ 2 * (n : Real) := by
    exact_mod_cast hfloor_int
  have hquad : μ ^ 2 = (n : Real) * μ + 1 := by
    rw [hdef]
    nlinarith
  have hgap : 0 < ((n : Real) - 1) * (μ - (n : Real)) :=
    mul_pos (by nlinarith) (sub_pos.mpr hmu_gt)
  rw [metallicBeta]
  norm_num
  change ((⌊2 * μ⌋ : Int) : Real) - 1 - (1 - μ) < μ ^ 2
  nlinarith

/-- The generalized account's first value equals the quadratic anchor exactly
for parameters zero and one. Thus among positive metallic parameters the
golden member is the unique affirmative case, and every parameter at least two
misses the anchor on the strict lower side. -/
theorem metallic_beta_first_anchor_iff (n : Nat) :
    metallicBeta n 1 = metallicValue n ^ 2 ↔ n ≤ 1 := by
  constructor
  · intro hanchor
    by_contra hn
    have htwo : 2 ≤ n := by omega
    exact (metallic_beta_first_strict_failure n htwo).ne hanchor
  · intro hn
    interval_cases n
    · norm_num [metallicBeta, metallicValue]
    · have hmu : metallicValue 1 = Real.goldenRatio := by
        rw [metallicValue, Real.goldenRatio]
        norm_num
      rw [metallicBeta, hmu]
      simpa [o5Beta] using o5_beta_power_law.1

#print axioms metallic_beta_first_anchor_iff

end D5.S3.AnalyticClosure.MetallicAnchorExceptional
