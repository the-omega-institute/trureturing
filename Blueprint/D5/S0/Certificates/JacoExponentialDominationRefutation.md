# Kok Conjecture 2.12 refutation

## Abstract

The A000149 vertices miss the closed neighborhood of vertex 88, so they do not dominate the infinite linear Jaco graph.

**Definition 1.1 (The proposed exponential dominating set).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.claim`

*Formalization.* `D5/S0/Certificates/JacoExponentialDominationRefutation.claim` (`✓ std3`).

*Citation.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

Conjecture 2.12 on printed page 9 of arXiv:2507.16500v1 proposes that the vertices indexed by A000149 dominate the infinite linear Jaco graph. The formal definition uses the natural floors of powers of e, indexed from exponent zero, and the paper's recursive right endpoints.

**Theorem 1.2 (Vertex 88 is not dominated).**

Lean statement: `D5/S0/Certificates/JacoExponentialDominationRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/JacoExponentialDominationRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johan Kok (2025). *Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs*. DOI: [10.48550/arXiv.2507.16500](https://doi.org/10.48550/arXiv.2507.16500).

*Commentary.*

The recursive endpoint certificate gives right endpoint 143 at vertex 88, while every vertex through 54 has right endpoint below 88. Thus the closed neighborhood of vertex 88 is contained in the interval from 55 through 143.

Mathlib's certified decimal bounds for e imply e to the fourth power is below 55 and e to the fifth power is above 144. Monotonicity of powers and natural floors then excludes every term of A000149 from that interval. Consequently vertex 88 is neither selected nor adjacent to a selected vertex. The result refutes only the printed conjecture; it gives no value for the domination number and proposes no replacement set.

## References

- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.claim`
- Truth anchor: `D5/S0/Certificates/JacoExponentialDominationRefutation.result`
