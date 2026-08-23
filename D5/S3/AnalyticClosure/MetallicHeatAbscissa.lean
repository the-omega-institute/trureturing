/- GID: D5/S3/AnalyticClosure/MetallicHeatAbscissa
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Metallic prime spectra have reciprocal-first-account heat abscissae. -/

import Mathlib
import D5.S3.AnalyticClosure.MetallicAnchorExceptional
import D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa

/- Provenance: Native proof over pinned mathlib. -/

/- Search and proof receipt (2026-08-21).

   Candidates searched and inspected:
   * Every direct Lean file present in `D5/S3/AnalyticClosure` in the worktree
     this proof was written in: `CofinalTailDiscipline`,
     `GoldenApproximationConstant`, `HeatNormalizationImpossibility`,
     `MetallicAnchorExceptional`, and `PrimeSpectrumHeatAbscissa`. That worktree
     trails the integration branch, which holds further files in this directory;
     the enumeration is scoped to what was on disk and is not a claim about the
     integration branch.
   * Every direct Lean file in `D5/S3/Midline`: `AddressableCoefficientFactorization`,
     `AutomaticMidlineDecomposition`, `DualCharacterization`, `GoldenHeatBoundary`,
     `GoldenHeatSpectrum`, `GoldenSpectralMarker`, `HeatTraceConvergence`,
     `HeatTraceHolomorphy`, `OffLineCoefficientScaling`, `OffLineScaling`,
     `UniversalHeatTrace`, and `ZetaHeatTraceBridge`.
   * Every direct Lean file in `D5/S0/Asymptotics`: `DensePhaseEscapeIdentity`,
     `DensePhaseUnrealizable`, `EscapeProbabilityMonotone`,
     `FinitePartitionCellMeasure`, `FiniteProgramLevelSet`,
     `FixedPointFreeEscapeProbability`, `GreenClassRadius`, `MetallicFamily`,
     `NameSetDistanceSandwich`, `OddCycleDrift`, `PoissonWeightDecay`, and
     `SkewedEscapeMass`.
   * Every direct Lean file in `D5/S3/Analytic`: `AlternatingPoleCoefficients`,
     `CompletedZetaMellinReconstruction`, `DiagonalCollapse`, `GoldenEulerBeta`,
     `LedgerLengthGrowth`, `LiCausalTrichotomy`, `PoleLayerSelection`,
     `PrimeCashflowCost`, `ScaledPoleAccumulation`, `TailCertificate`,
     `TailClosure`, and `ZetaGibbs`.
   * Every pinned file in `Mathlib/Algebra/Order/Floor`: `Defs`, `Div`,
     `Extended`, `Ring`, `Semifield`, and `Semiring`; and every pinned direct
     file in `Mathlib/Analysis/Real`: `Cardinality`, `Hyperreal`, `OfDigits`,
     `Spectrum`, and `Sqrt`. The exact floor candidates inspected included
     `Int.le_floor`, `Int.floor_le`, `Int.floor_le_floor`,
     `Int.floor_add_natCast`, and `Int.le_floor_add`.
   * Repository searches by proposition shape covered positivity and linear
     lower bounds for `metallicBeta`, reciprocal heat abscissae, and the name
     fragments `metallic_value_one_le`, `metallic_beta_first_pos`,
     `metallic_beta_succ_ge`, and `metallic_heat_abscissa`. The only metallic
     account declarations found were the definition and exceptional-anchor
     classification in `MetallicAnchorExceptional`; no equivalent result under
     another name was found. This is the SL-028 self-check.

   Declarations and tactics doing real work in the proof body:
   * `D5.S0.Asymptotics.MetallicFamily.metallicValue`, `Real.sq_sqrt`, and
     `Real.sqrt_nonneg` prove the uniform bound `1 <= metallicValue n`.
   * `D5.S3.AnalyticClosure.MetallicAnchorExceptional.metallicBeta` is the
     exponent account. `Int.le_floor` and `Int.floor_le` respectively give the
     first-value floor bound and the shifted floor lower bound.
   * `mul_nonneg`, `sub_nonneg.mpr`, and `Nat.cast_add` support the two real
     inequalities combined around those floor bounds.
   * `prime_spectrum_heat_abscissa` turns positivity, reflexivity at the first
     value, and linear growth into the stated heat abscissa.
   * The complete load-bearing tactic list is `rw`, `positivity`, `nlinarith`,
     `norm_num`, `exact_mod_cast`, `push_cast`, and `exact`; `rfl` supplies the
     definitional first-value equality in the final application.

   Boundary, cheap-closure, address, and thin-wrapper checks:
   * No parameter hypothesis is needed. Direct simplification gives
     `metallicValue 0 = 1` and `metallicBeta 0 1 = 1`; the growth inequality is
     equality for `n = 0`, while `k = 0` is equality for every parameter.
   * At the time of writing, an 80-decimal-digit run-local sweep over
     `0 <= n <= 100` and `0 <= k <= 500` checked 101 positivity instances and
     50,601 growth instances with zero counterexamples. It measured exactly
     the `n = 0` or `k = 0` cases as tight. This is a contemporaneous
     measurement, not evidence used by the proof and not a standing claim.
   * After the statement elaborated in a run-local scratch file, `decide`,
     `simp`, `omega`, and `norm_num` were each tried under a short timeout; none
     closed it.
   * The address was measured against the direct-file bucket rule at writing
     time and remains below the split threshold after this addition. Exact
     occupancy is omitted because it is worktree-dependent and goes stale.
   * The shortest route has four substantive stages: the radical lower bound,
     first-value positivity, the shifted floor-growth inequality, and the
     general heat-abscissa application. The floor step also needs the separately
     proved `1 <= metallicValue n` and the derived `k <= k * metallicValue n`,
     so it is not a one-application consequence of a floor lemma. The golden
     analogue `o5Beta_succ_ge` in `D5/S3/Midline/GoldenHeatSpectrum.lean` splits
     the base case, combines square-root estimates, and applies `o5_beta_growth`;
     the route below needs none of those three, using one uniform lower bound on
     the metallic value instead. No claim is made about which proof is shorter in
     lines.
   * `D5/S3/Midline/GoldenHeatSpectrum.lean` is deliberately not imported:
     its golden instance is superseded here by the already-general
     `PrimeSpectrumHeatAbscissa`, and importing it would add no proof step.
     `MetallicAnchorExceptional` is imported because it is the unique source
     of `metallicBeta`; as an `I`-tagged dependency it forces this file's `I`
     tag.

   Openness provenance:
   * The requested uncorrected value was the reciprocal of
     `metallicValue n ^ 2`. `metallic_beta_first_anchor_iff` proves that this
     identification holds exactly when `n <= 1`, hence fails for every larger
     parameter. The theorem below records the corrected reciprocal of the
     account's first value, valid for the entire metallic family.

   The inspected-candidate list and the load-bearing list are separate. -/

namespace D5.S3.AnalyticClosure.MetallicHeatAbscissa

open D5.S0.Asymptotics.MetallicFamily
open D5.S3.AnalyticClosure.MetallicAnchorExceptional
open D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa
open D5.S3.Midline.UniversalHeatTrace

private theorem metallic_value_one_le (n : Nat) :
    (1 : Real) ≤ metallicValue n := by
  rw [metallicValue]
  have hsqrt_sq :
      Real.sqrt ((n : Real) ^ 2 + 4) ^ 2 = (n : Real) ^ 2 + 4 := by
    rw [Real.sq_sqrt]
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((n : Real) ^ 2 + 4) :=
    Real.sqrt_nonneg _
  have hn : 0 ≤ (n : Real) := by positivity
  nlinarith

private theorem metallic_beta_first_pos (n : Nat) :
    0 < metallicBeta n 1 := by
  have hmu := metallic_value_one_le n
  have hfloor_int : (2 : Int) ≤ ⌊2 * metallicValue n⌋ := by
    rw [Int.le_floor]
    norm_num
    nlinarith
  have hfloor_real :
      (2 : Real) ≤ ((⌊2 * metallicValue n⌋ : Int) : Real) := by
    exact_mod_cast hfloor_int
  rw [metallicBeta]
  norm_num
  nlinarith

private theorem metallic_beta_succ_ge (n k : Nat) :
    metallicBeta n 1 + (k : Real) ≤ metallicBeta n (k + 1) := by
  have hmu := metallic_value_one_le n
  have hkmu : (k : Real) ≤ (k : Real) * metallicValue n := by
    nlinarith [mul_nonneg (show (0 : Real) ≤ k by positivity)
      (sub_nonneg.mpr hmu)]
  have hfloor_int :
      ⌊2 * metallicValue n⌋ + (k : Int) ≤
        ⌊(((k + 1 + 1 : Nat) : Real) * metallicValue n)⌋ := by
    rw [Int.le_floor]
    have hfloor := Int.floor_le (2 * metallicValue n)
    push_cast
    nlinarith
  have hfloor_real :
      ((⌊2 * metallicValue n⌋ : Int) : Real) + (k : Real) ≤
        ((⌊(((k + 1 + 1 : Nat) : Real) * metallicValue n)⌋ : Int) : Real) := by
    exact_mod_cast hfloor_int
  rw [metallicBeta, metallicBeta]
  norm_num [Nat.cast_add] at hfloor_real ⊢
  nlinarith

/-- For every metallic parameter, the prime-by-natural spectrum formed from
the metallic exponent account has heat abscissa equal to the reciprocal of
the account's first value. -/
theorem metallic_heat_abscissa (n : Nat) :
    IsHeatAbscissa
      (fun pk : Nat.Primes × Nat =>
        metallicBeta n (pk.2 + 1) * Real.log (pk.1 : Real))
      (1 / metallicBeta n 1) := by
  exact prime_spectrum_heat_abscissa
    (metallicBeta n) (metallicBeta n 1) (metallic_beta_first_pos n) rfl
    (metallic_beta_succ_ge n)

#print axioms metallic_heat_abscissa

end D5.S3.AnalyticClosure.MetallicHeatAbscissa
