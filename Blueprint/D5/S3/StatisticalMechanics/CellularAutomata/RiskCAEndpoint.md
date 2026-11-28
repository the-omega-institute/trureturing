# Noninjectivity on complete finite boards

## Abstract

A collision in the deterministic RiskCA at the highest active threshold.

**Theorem 1.1 (The zero-growth step has a collision).**

$$\exists X,Y \in S, X \neq Y \land \phi(X) = \phi(Y)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* María Teresa Arias Noguerales (2026). *Territorial Conflict as a Cellular Automaton: Frozen Domains and Active Fronts in a Risk-Derived Local Rule*. DOI: [10.48550/arXiv.2611.34784](https://doi.org/10.48550/arXiv.2611.34784). URL: <https://arxiv.org/abs/2611.34784v1>.

*Commentary.*

Let V be the vertex set of a finite complete simple graph with at least two vertices, let P ≥ 2 be the number of available owner labels, and let M ≥ 3 be the unit capacity. For every fixed priority permutation of V, either fortification setting, and every real 1 < ρ < 2, φ denotes the deterministic local step of §3.2 and Appendix B Algorithm 1 with growth zero and threshold M − 1. Its carrier S is the full product of the owner and unit alphabets over V. Equality of configurations is pointwise.

Choose distinct vertices u and v. Put M units at u and one unit everywhere else. Assign one owner to v and a different owner everywhere else. The unique request is from u to v. Its pre-commit force is M − 1, its post-commit defence is one, and the strict win leaves M − 2 units at v. The output Y has one owner and one unit everywhere except at v. Its threats vanish and the zero-growth step fixes it. The inputs differ at u, giving φ(X) = Y = φ(Y).

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/RiskCAEndpoint.paper_noninjective`
