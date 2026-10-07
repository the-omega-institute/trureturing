# The catalytic change of variables in Rational[t][[q]]

## Abstract

The actual P13 matching series satisfies the rational catalytic H bridge.

**Definition 1.1 (Outer variable).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.q`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

q is the outer power-series variable in the coefficientwise formal series ring.

**Definition 1.2 (Catalytic point).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.zeta`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.zeta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

zeta=q/(1+q)^2 is evaluated only through the HasEval outer-series API.

**Definition 1.3 (Inner change of variables).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.u`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

u(t)=(1+q)(1-t)/(1-qt), with the denominator inverted by the existing unit inverse over polynomial coefficients.

**Definition 1.4 (Actual matching carrier).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.Aq`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.Aq` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Aq is actualSeries from the original P13-avoiding perfect-matching carrier, evaluated at zeta.

**Theorem 1.5 (Actual H bridge).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.catalytic_H_bridge`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.catalytic_H_bridge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The public theorem proves the units 1+q, 1-qt, and 1-q^2t, specializes the reciprocal marker to u(qt), proves the kernel and zeta*u^2 identities, and derives q(1-t)^2 H(qt)+delta*t H=C(Aq-1)(1+qt^2)+(C^2-4qAq)t from the public actual F equation by legitimate evaluation composition.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.Aq`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.catalytic_H_bridge`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.q`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.u`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13CatalyticH.zeta`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Series](P13Series.md)
