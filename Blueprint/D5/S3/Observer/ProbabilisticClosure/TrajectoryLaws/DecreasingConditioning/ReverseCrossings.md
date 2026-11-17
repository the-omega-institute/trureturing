# Reverse conditional-expectation crossings

## Abstract

Finite-horizon reversal bounds upcrossings of decreasing conditional expectations.

Let Ω belong to an arbitrary universe, let A be any sigma-algebra on Ω, and let μ be a finite measure on A. Let F be a natural-indexed antitone sequence of sigma-algebras with Fₙ contained in A for every n. For a real function f write Xₙ = Eμ[f | Fₙ], using the actual measurable conditional-expectation versions.

**Theorem 1.1 (Finite integral of the original upcrossing count).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings.exists_lintegral_upcrossings_condExp_le`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings.exists_lintegral_upcrossings_condExp_le` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Cameron Freer and the Exchangeability Project contributors (2026). *Reverse crossings and Levy downward conditional expectation convergence*. URL: <https://github.com/TauCetiProject/TauCeti/tree/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f>.

*Commentary.*

For every finite measure space and decreasing family as above, every μ-integrable real function f, and every pair of real numbers a < b, there is an extended nonnegative real C strictly below infinity such that the lower integral of the total upcrossing count U(a,b;X) is at most C. Here U is the supremum over natural horizons N of the number of completed upcrossings from a to b strictly before N. The bound applies to the original sequence Xₙ, with no assumed convergence or measurability of f at any Fₙ.

Fix a natural horizon N. The family n ↦ F_(N−n), with truncated natural subtraction, is an increasing filtration and stays constant once n exceeds N. Its conditional-expectation process is a forward martingale. Doob's upcrossing inequality bounds its expected crossing count by a positive-part integral. The estimate of the positive part of Eμ[f | F_(N−n)] − a by its absolute value, the triangle inequality and conditional L1 contraction bound these integrals uniformly in N and n by the L1 norm of f plus |a| times the total mass.

The pathwise comparison reverses both time and sign: an upcrossing of X from a to b becomes an upcrossing of its negated reversal from −b to −a. If an original crossing starts at τ and finishes at σ, the reflected endpoints are N−σ and N−τ. An induction on the number of crossings bounds each reflected upper crossing time by its reflected original lower crossing time.

The reversed count uses horizon N+1. A crossing starting at original time zero can finish at reflected time N, so it must be included. At the extra index N+1 the hitting-time convention returns N+1 both for a first hit at that index and for no hit. Consequently the crossing count at horizon N+1 depends only on path values at indices zero through N. This free-boundary congruence allows the polynomial horizon reversal to be replaced by truncated subtraction without imposing agreement at N+1. The zero-horizon case is included.

Apply the reversed martingale estimate to −f on the interval from −b to −a. Conditional expectation commutes almost everywhere with negation. A countable intersection over all natural time indices transports this equality to the entire crossing process on one common full-measure set. The pathwise comparison then bounds every original finite-horizon integral by the same finite constant.

The original conditional expectations are strongly measurable for the ambient constant filtration. Their finite-horizon crossing counts are measurable and increase with the horizon. Monotone convergence therefore bounds the integral of their supremum, which is the total original upcrossing count. Finite integral implies almost-everywhere finite crossing counts, the ingredient used in the downward convergence theorem.

The argument allows arbitrary finite measure spaces, unbounded integrable real inputs, constant or genuinely decreasing fields, every natural horizon and changes on null sets. It adds no countable-generation, standard-Borel, stationarity, Markov or eventual-constancy assumption. The construction is the real reverse-crossing argument in Tau Ceti, with Cameron Freer's Exchangeability ancestry and applicable Apache-2.0 notices recorded in the cited source note. It is a classical reverse-martingale estimate.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings.exists_lintegral_upcrossings_condExp_le`
