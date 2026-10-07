# Explicit P13 scalar q-series and minimality

## Abstract

Explicit finite-coefficient q-series solve the scalar bulk recurrence by uniform formal annihilation.

**Definition 1.1 (Finite denominators).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Den`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Den` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Den(r) is the product of 1-X^i for i=1 through r; Den(0)=1.

**Definition 1.2 (Lawful denominator inverses).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.DenInv`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Scalar.DenInv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

DenInv(r) uses the proved constant coefficient one and the existing formal-series unit inverse.

**Theorem 1.3 (Successor cancellation).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.DenInv_succ`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.DenInv_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every r, multiplying DenInv(r+1) by 1-X^(r+1) gives DenInv(r).

**Theorem 1.4 (The independent coefficient series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.E_rescale`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.E_rescale` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The formal v-series with coefficients DenInv(r) satisfies E(Xv)=(1-v)E(v).

**Definition 1.5 (Explicit finite convolution).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

S(k) is the sum over r=0 through k of DenInv(r) times DenInv(k-r).

**Theorem 1.6 (The first convolution boundary).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The exact boundary is (1-X)S(1)=2, with S(0)=1.

**Theorem 1.7 (The universal convolution recurrence).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every natural k, (1-X^(k+2))S(k+2)=2S(k+1)-S(k). The proof squares the rescale identity.

**Theorem 1.8 (The separate signed boundary).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.c_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.c_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For c(k)=(-1)^k X^choose(k,2) S(k), the k=1 boundary is (1-X)c(1)=-2.

**Theorem 1.9 (Signed higher coefficients).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.c_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.c_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every natural k, (1-X^(k+2))c(k+2)=-2X^(k+1)c(k+1)-X^(2k+1)c(k).

**Definition 1.10 (Finite coefficient Phi).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Phi`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Phi(j) is defined coefficient by coefficient using the finite sum of c(k) point(j)^k for k=0 through the requested coefficient degree.

**Theorem 1.11 (Phi has constant coefficient one).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.constantCoeff_Phi`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.constantCoeff_Phi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every natural j, Phi(j) has constant coefficient one.

**Theorem 1.12 (The exact cleared q-difference).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Phi_difference`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Phi_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every natural j, delta squared times Phi(j) equals delta times (delta-2X^(j+1)) times Phi(j+1), minus X^(2j+3) times Phi(j+2).

**Theorem 1.13 (Derived W shift).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.W_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.W_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

Any ordinary power-series family satisfying the section 6 bulk recurrence has W(j)=-X^(j+2)deltaInv W(j+1) for j at least two. This is derived from the explicit Phi difference.

**Theorem 1.14 (The uniform annihilator).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.W_uniform_dvd`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.W_uniform_dvd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For every n and every j at least two, X^n divides W(j), with only the bulk recurrence as a hypothesis.

**Theorem 1.15 (The formal minimal-solution lemma).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.minimal_solution`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.minimal_solution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For any power-series family h satisfying Bulk(h), and every j at least two, delta Phi(j)h(j)+X^j Phi(j+1)h(j-1)=0. Every coefficient vanishes by the uniform annihilator; no tail or finite-height premise is assumed.

**Theorem 1.16 (Lawful scalar denominator inversion).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.D_mul_DInv`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.D_mul_DInv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

For D=delta(1-2X-X squared)P-X cubed(1+X)R, the proved inverse identity is D times DInv equals one.

**Definition 1.17 (The explicit scalar series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.G`

*Formalization.* `D5/S3/Combinatorics/PatternMatchings/P13Scalar.G` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

G=1+X(1-X) cubed P times the unit inverse of D. P=Phi(1), R=Phi(2), and delta=(1-X) squared. P13Enumeration.actual_A_eq_G proves that this explicit series equals the actual matching series after the lawful substitution X/(1+X) squared. P13Enumeration.actualSeries_eq_G_subst_q recovers the original counting series by substituting the Catalan series minus one.

**Theorem 1.18 (The scalar cancellation).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.G_cleared`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Scalar.G_cleared` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The defined series satisfies (G-1)D=X(1-X) cubed P.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.D_mul_DInv`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Den`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.DenInv`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.DenInv_succ`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.E_rescale`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.G`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.G_cleared`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Phi`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.Phi_difference`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S_one`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.S_recurrence`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.W_shift`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.W_uniform_dvd`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.c_one`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.c_recurrence`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.constantCoeff_Phi`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Scalar.minimal_solution`
