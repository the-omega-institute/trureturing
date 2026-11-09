# Levy's downward theorem

## Abstract

Decreasing conditional expectations converge almost everywhere and in L1 to the raw-infimum expectation.

Let Ω belong to any universe, equip it with an arbitrary ambient sigma-algebra A and finite measure μ, and let F₀ ⊇ F₁ ⊇ ⋯ be a natural-indexed antitone family of sigma-algebras. Assume only F₀ is contained in A; antitonicity then places every Fₙ inside A. Put M = infimum over n of Fₙ, the raw infimum of measurable spaces. All conditional expectations below are the actual receiving measurable versions under μ.

**Theorem 1.1 (Both fixed-input limits at the raw infimum).**

Lean statement: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/LevyDownward.tendsto_ae_and_eLpNorm_condExp_iInf`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/LevyDownward.tendsto_ae_and_eLpNorm_condExp_iInf` (`✓ std3`). ∎

*Citation.* The Tau Ceti contributors; Cameron Freer and the Exchangeability Project contributors (2026). *Reverse crossings and Levy downward conditional expectation convergence*. URL: <https://github.com/TauCetiProject/TauCeti/tree/c9dbc67d6e3f1254d3da41c391cd1af512ea3b7f>.

*Commentary.*

For every such universe, finite measure space and antitone family, and every real function f on Ω, the following two conclusions hold together. First, for μ-almost every ω, the sequence Eμ[f | Fₙ](ω) tends as n tends to infinity to Eμ[f | M](ω). Second, the exponent-one extended Lp seminorm of Eμ[f | Fₙ] − Eμ[f | M] tends to zero along the same natural-index atTop filter. Thus the first conclusion uses one exceptional null set for the entire sequence, and the second is L1 convergence of the difference of the actual versions.

There is no integrability or ambient-measurability premise on f in this statement. Conditional expectation is defined to be zero on nonintegrable inputs, so in that case all the displayed conditional expectations vanish and both conclusions follow. For integrable f the assertion is the usual analytic Levy downward theorem. In particular, no measurability of f at M or at the intermediate fields is assumed.

For integrable f, conditional L1 contraction gives a uniform L1 bound on Xₙ = Eμ[f | Fₙ]. Fatou's bound for the liminf of their norms makes that liminf finite almost everywhere. The reverse-crossing integral estimate makes the number of upcrossings finite almost everywhere for each rational interval. Intersect these countably many sets. The pathwise convergence criterion for finite rational upcrossings and finite liminf now supplies a real limit. Choose a pointwise representative X∞, setting it to zero where convergence fails. Uniform integrability of the conditional-expectation family makes X∞ integrable.

Vitali convergence upgrades Xₙ → X∞ almost everywhere to exponent-one eLpNorm convergence. This step uses the uniform integrability of conditional expectations of the same integrable input, and does not require the decreasing sequence to be a forward martingale.

The raw-infimum measurability step constructs a common representative rather than replacing M by an intersection of completed fields. A function that has an almost-everywhere strongly measurable representative at every Fₙ has one at M: choose representatives gₙ and take their pointwise liminf. For each fixed N, deleting the first N indices leaves the liminf unchanged, and every later gₙ is F_N-measurable by antitonicity. The liminf is therefore measurable for every F_N and hence for M. On a common countable full-measure set all representatives agree with the original function, so their liminf is an almost-everywhere representative of it.

To apply this observation to X∞, fix N and use the shifted convergent sequence X_(n+N). Its terms are almost-everywhere strongly measurable at F_N. An almost-everywhere limit at a possibly nonambient field is represented by the pointwise limsup of strongly measurable representatives. This proves measurability of X∞ at each F_N, after which the common raw-infimum construction applies.

For every n the tower property gives Eμ[Xₙ | M] = Eμ[f | M] almost everywhere. Conditional expectation is L1 contractive, so the L1 limit of the left side is Eμ[X∞ | M]. The common raw-infimum representative and integrability give Eμ[X∞ | M] = X∞ almost everywhere. These identities identify the previously constructed limit with the actual Eμ[f | M]. Transporting both convergence conclusions across that almost-everywhere equality proves the stated conjunction.

The theorem covers arbitrary finite measure spaces, zero measure, all natural indices including zero, unbounded integrable inputs, constant and nontrivial decreasing fields, and null-set changes of the conditional versions. It assumes no supplied reverse-martingale limit or conditional-expectation convergence, no countable generation, standard-Borel structure, eventual constancy, Markov property or stationarity. It treats one fixed real input. A varying-input limit with two independent tail indices requires an additional dominated tail argument; neither that joint limit nor future-opinion merging is asserted here.

This is the real AE and L1 downward construction in Tau Ceti, based on Cameron Freer's Exchangeability development. The cited source note gives immutable declaration locators, provenance and the applicable Apache-2.0 texts. The source also discusses the classical accounts of reverse-martingale convergence by Kallenberg, Durrett and Williams. General Lp and complex-valued extensions are outside the statement here.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/LevyDownward.tendsto_ae_and_eLpNorm_condExp_iInf`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/DecreasingConditioning/ReverseCrossings](ReverseCrossings.md)
