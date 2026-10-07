# Actual H coefficients and boundary elimination inputs

## Abstract

Coefficient extraction from the actual catalytic H proves its boundary laws, bulk recurrence and minimal-solution identity.

The declarations live in D5.S3.Combinatorics.PatternMatchings.P13.CatalyticH. The outer variable X marks formal series degree; t is the polynomial coefficient marker. H is the lawful transform of the literal completion series from the original ordinary perfect-matching carrier. Its rows are extracted from this H, not defined by a recurrence. All series are formal over the rationals; the discrete coefficient topology justifies evaluation and coefficientwise sums.

**Definition 1.1 (Embedding rational series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.scalarEmbed`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.scalarEmbed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

scalarEmbed maps each rational coefficient to a constant polynomial. This ring homomorphism relates the ordinary series A to the polynomial-coefficient series Aq.

**Definition 1.2 (Transposed polynomial coefficients).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.row`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For any f in Rational[t][[X]], coeff n (row k f) is the coefficient of t^k in coeff n f. Each row is a rational power series.

**Theorem 1.3 (Diagonal action of t to Xt).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.row_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.row_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every k and polynomial-coefficient series f, row k (shift f) = X^k row k f. The proof reduces legitimate coefficient evaluation to a finite sum of polynomial monomials, then isolates the coefficient at n-k. This finite-series calculation is used in every actual H boundary and bulk extraction.

**Definition 1.4 (Rows of the actual H).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

h(k) is row k H. It retains the literal completion carrier through H's lawful change of variables.

**Definition 1.5 (Lawful outer substitution).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.Z`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.Z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Z=X invPlus^2, where invPlus is the formal unit inverse of 1+X. Z has zero constant coefficient; Z_hasEval and Z_clear justify evaluation and prove Z(1+X)^2=X.

**Definition 1.6 (The actual counting series at Z).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.A`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

A is actualSeries evaluated at Z through the continuous constant embedding and proved HasEval Z. The original actualSeries counts every P13-avoiding fixed-point-free involution of Fin(2n), including empty and disconnected matchings.

**Theorem 1.7 (Identifying the embedded actual series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.Aq_actual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.Aq_actual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Aq equals scalarEmbed A. Two lawful coefficientwise HasSum evaluations and continuity of scalarEmbed establish this identity. The expanded H equation uses it before taking rows.

**Theorem 1.8 (Boundary at t degree zero).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

X h(0) = (1+X)(A-1). This equation comes from row zero of the actual catalytic H equation.

**Theorem 1.9 (Boundary at t degree one).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

X^2 h(1) + ((1-X)^2-2X) h(0) = (1+X)^2-4XA. This equation comes from row one of the same actual equation.

**Theorem 1.10 (Boundary at t degree two).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_two`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

X^3 h(2) + ((1-X)^2-2X^2) h(1) + X(1-X)h(0) = 0. The X(1-X)h(0) term is retained: row two and X times the degree-zero boundary give this exact law.

**Theorem 1.11 (The actual all-index bulk law).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_bulk`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_bulk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every j at least two, X^(j+2)h(j+1) + ((1-X)^2-2X^(j+1))h(j) + X^j h(j-1) = 0. Extracting row j+1 proves it on the actual H family; no Bulk hypothesis is assumed.

**Theorem 1.12 (Structural divisibility of actual rows).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every natural k, X^k divides h(k). The proof constructs a quotient from the actual degree-two boundary for k=1 and from h_bulk for k at least two, cancelling only the unit (1-X)^2. This is an additional structural support law for the transformed actual series. The final enumeration uses the boundary and bulk laws directly and does not need this divisibility statement.

**Theorem 1.13 (Discharging the scalar Bulk contract).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.actual_Bulk`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.actual_Bulk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The actual family h satisfies P13Scalar.Bulk by h_bulk. This consumed adapter supplies the proved premise of h_minimal_solution; it is not additional mathematical content.

**Theorem 1.14 (Minimality on the actual H family).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_minimal_solution`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_minimal_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every j at least two, (1-X)^2 Phi(j)h(j) + X^j Phi(j+1)h(j-1) = 0. The scalar uniform annihilation theorem applies with actual_Bulk. P13Enumeration.actual_A_eq_G consumes this identity at j=2 together with all three actual boundaries and Phi_difference at j=1, discharging every boundary-elimination premise.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.A`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.Aq_actual`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.Z`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.actual_Bulk`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_one`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_two`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_boundary_zero`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_bulk`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_dvd`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.h_minimal_solution`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.row`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.row_shift`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13HCoefficients.scalarEmbed`
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13CatalyticH](P13CatalyticH.md)
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Scalar](P13Scalar.md)
