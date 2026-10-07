# The actual matching functional equation

## Abstract

Literal continuation counts give a generating series with a polynomial old-block variable.

**Definition 1.1 (Single-block completion series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.completionSeries`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.completionSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For each old block size m, the coefficient of z to degree d is the literal completion count c(m,d), cast to the rationals. The variable z marks future closures.

**Definition 1.2 (The actual matching series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.actualSeries`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.actualSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The coefficient of z to degree n is the number of P13 avoiding perfect matchings on Fin(2n) in the original matching carrier. The empty matching and disconnected matchings are included.

**Definition 1.3 (Finite polynomial at each closure degree).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.countPolynomial`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.countPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

At degree d the polynomial is the sum of c(m,d)u to power m for m from zero through d. Support of literal completions removes every larger old block size.

**Definition 1.4 (The bivariate completion series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.completionBivariate`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.completionBivariate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

F is the power series in z whose degree d coefficient is countPolynomial(d). Thus F belongs to the ring of power series with rational polynomial coefficients in u.

**Definition 1.5 (The old-block variable).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.blockMarker`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.blockMarker` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The marker u is the polynomial coefficient variable, embedded as a constant power series in z.

**Definition 1.6 (The reciprocal marker).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.reciprocalMarker`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.reciprocalMarker` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The reciprocal marker is the unit inverse of 1-zu. It is obtained by rescaling the negative binomial series of exponent one, so its constant coefficient is one.

**Definition 1.7 (Legitimate polynomial substitution).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.evaluateBlock`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Series.evaluateBlock` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For any v in the polynomial coefficient power series ring, evaluate each polynomial coefficient at v and the outer variable at z. Polynomial evaluation permits a nonzero constant coefficient in v. The outer variable z is topologically nilpotent in the coefficientwise topology, and each resulting z coefficient is a finite sum.

**Theorem 1.8 (The concrete catalytic functional equation).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Series.completion_functional_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Series.completion_functional_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every m, the series f_m has order at least m and its degree m coefficient is one. At every z degree d, the u degree of F is at most d. The exact boundaries are f_0=A and f_0=1+f_1. With v the unit inverse of 1-zu, the equation is (u-1-z*u^2)*F = u-(1+z*u^2)*A+z*u^2*F(v,z). The finite triangular law for literal completions proves the equation coefficient by coefficient. The negative binomial coefficient formula evaluates F(v,z), and the original matching continuation law identifies A. No functional equation or abstract recurrence model is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.actualSeries`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.blockMarker`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.completionBivariate`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.completionSeries`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.completion_functional_equation`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.countPolynomial`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.evaluateBlock`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Series.reciprocalMarker`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Counts](P13Counts.md)
