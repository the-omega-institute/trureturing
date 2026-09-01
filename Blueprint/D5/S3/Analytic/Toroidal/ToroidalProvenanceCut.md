# Toroidal Provenance Cut

## Abstract

A selected nonzero twist makes period vanishing equivalent to base vanishing.

**Theorem 1.1 (A nonzero twist separates base zeros from twist zeros).**

$$\forall Index \in \operatorname{Type}\left(\right), Point \in \operatorname{Type}\left(\right), Scalar \in \operatorname{Type}\left(\right), indexDecision \in \operatorname{DecidableEq}\left(Index\right), scalarDecision \in \operatorname{DecidableEq}\left(Scalar\right), mulZero \in \operatorname{MulZeroClass}\left(Scalar\right), noZeroDivisors \in \operatorname{NoZeroDivisors}\left(Scalar\right), selected \in \operatorname{Finset}\left(Index\right), period \in Index \to \left(Point \to Scalar\right), twist \in Index \to \left(Point \to Scalar\right), base \in Point \to Scalar, s \in Point, i \in Index,\; \left(\operatorname{mem}\left(i, selected\right) \land \left(period\left(i\right)\left(s\right) = base\left(s\right) \times twist\left(i\right)\left(s\right) \land twist\left(i\right)\left(s\right) \ne 0\right)\right) \Rightarrow \left(\left(\operatorname{mem}\left(i, \operatorname{periodZero}\left(\operatorname{toroidalVanishingProfile}\left(selected, period, twist, s\right)\right)\right) \Leftrightarrow base\left(s\right) = 0\right) \land \left(\neg \operatorname{mem}\left(i, \operatorname{twistZero}\left(\operatorname{toroidalVanishingProfile}\left(selected, period, twist, s\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Toroidal/ToroidalProvenanceCut.toroidal_provenance_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The profile retains the selected finite index set and filters it twice at the chosen point: once by period vanishing and once by twist vanishing. The theorem earns that profile definition by giving its per-index membership cut under the displayed factorization.

This is distinct from ToroidalCommonZeroLocus, whose conclusion is a global set equality quantified over all indices. ToroidalObserverSetCover, ToroidalTemperednessCriterion, and ToroidalJetDepth supply the neighbouring observer and jet context.

The nonzero-twist certificate is the C-5 chart-selection precondition: a chart must be chosen where twist is nonzero before projective jet normalization. The same provenance distinction supplies the A-R5 residual cut between a base zero and a twist zero.

## References

- Truth anchor: `D5/S3/Analytic/Toroidal/ToroidalProvenanceCut.toroidal_provenance_cut`
- Dependency: [D5/S3/Analytic/Adelic/ToroidalCommonZeroLocus](../Adelic/ToroidalCommonZeroLocus.md)
- Dependency: [D5/S3/Analytic/Adelic/ToroidalJetDepth](../Adelic/ToroidalJetDepth.md)
- Dependency: [D5/S3/Analytic/Adelic/ToroidalObserverSetCover](../Adelic/ToroidalObserverSetCover.md)
- Dependency: [D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion](../Adelic/ToroidalTemperednessCriterion.md)
