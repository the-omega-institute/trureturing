# Centered Reduced Residue Progressions

## Abstract

The longest positive-step progression in a short centered squarefree reduced residue system has the conjectured length.

**Definition 1.1 (The fixed centered reduced residue system).**

$$\forall n \in \mathbb{N}, x \in \mathbb{Z},\; \operatorname{CenteredReducedResidue}\left(n, x\right) \Leftrightarrow \left(\left(-\operatorname{NatDiv}\left(n + 1, 2\right) + 1 \le x \land x \le -\operatorname{NatDiv}\left(n + 1, 2\right) + 1 + n - 1\right) \land \operatorname{gcd}\left(x, n\right) = 1\right)$$

*Formalization.* `D5/S3/ArithUnits/CenteredReducedResidueProgressions.CenteredReducedResidue` (`✓ std3`).

*Citation.* Chaninat Phothila; Natthakan Thoket; Narakorn Rompurk Kanasri (2026). *Length of the Longest Arithmetic Progressions in a Certain Reduced Residue System*. DOI: [10.5281/zenodo.18154061](https://doi.org/10.5281/zenodo.18154061). URL: <https://math.colgate.edu/~integers/aa6/aa6.pdf>.

*Commentary.*

For a natural modulus n, the centered system consists of the integers in the source interval beginning at minus (n+1)/2 plus one and ending n-1 steps later, subject to gcd one with n.

**Definition 1.2 (Positive-step progression lengths).**

$$\forall n \in \mathbb{N}, s \in \mathbb{N},\; \operatorname{AdmissibleLength}\left(n, s\right) \Leftrightarrow \left(\exists a \in \mathbb{Z}, h \in \mathbb{N},\; 0 < h \land \left(\forall i \in \mathbb{N},\; i < s \Rightarrow \operatorname{CenteredReducedResidue}\left(n, a + i \cdot h\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/CenteredReducedResidueProgressions.AdmissibleLength` (`✓ std3`).

*Citation.* Chaninat Phothila; Natthakan Thoket; Narakorn Rompurk Kanasri (2026). *Length of the Longest Arithmetic Progressions in a Certain Reduced Residue System*. DOI: [10.5281/zenodo.18154061](https://doi.org/10.5281/zenodo.18154061). URL: <https://math.colgate.edu/~integers/aa6/aa6.pdf>.

*Commentary.*

A natural length s is admissible when some integer start and positive natural step place all terms with indices below s in the fixed centered reduced residue system.

**Definition 1.3 (The greatest prime factor).**

$$\forall n \in \mathbb{N},\; \operatorname{GreatestPrimeFactor}\left(n\right) = \operatorname{sup}\left(\operatorname{primeFactors}\left(n\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/CenteredReducedResidueProgressions.GreatestPrimeFactor` (`✓ std3`).

*Citation.* Chaninat Phothila; Natthakan Thoket; Narakorn Rompurk Kanasri (2026). *Length of the Longest Arithmetic Progressions in a Certain Reduced Residue System*. DOI: [10.5281/zenodo.18154061](https://doi.org/10.5281/zenodo.18154061). URL: <https://math.colgate.edu/~integers/aa6/aa6.pdf>.

*Commentary.*

The greatest prime factor is the supremum of the finite set of prime factors. On the theorem's domain that set is nonempty.

**Theorem 1.4 (The exact maximum progression length).**

$$\forall n \in \mathbb{N},\; \operatorname{let} p = \operatorname{GreatestPrimeFactor}\left(n\right); \operatorname{let} d = \operatorname{NatDiv}\left(n, p\right); \left(\left(\left(\operatorname{Even}\left(n\right) \land \operatorname{Squarefree}\left(n\right)\right) \land 3 \le \operatorname{card}\left(\operatorname{primeFactors}\left(n\right)\right)\right) \land d < 2 \cdot p\right) \Rightarrow \operatorname{let} k = p - 1 - \operatorname{NatDiv}\left(2 \cdot p, d\right); \operatorname{IsGreatest}\left(\{s \in \mathbb{N} \mid \operatorname{AdmissibleLength}\left(n, s\right)\}, k\right) \land \lfloor p - \frac{2 \cdot p}{d}\rfloor = k$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/CenteredReducedResidueProgressions.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Chaninat Phothila; Natthakan Thoket; Narakorn Rompurk Kanasri (2026). *Length of the Longest Arithmetic Progressions in a Certain Reduced Residue System*. DOI: [10.5281/zenodo.18154061](https://doi.org/10.5281/zenodo.18154061). URL: <https://math.colgate.edu/~integers/aa6/aa6.pdf>.

*Commentary.*

Let p be the greatest prime factor of n, d=n/p, and k=p-1-floor(2p/d), where the inner floor is natural Euclidean division. For every even squarefree n with at least three distinct prime factors and d<2p, k is an admitted length and bounds every admitted length. The rational floor of p-2p/d is exactly the same natural number k.

## References

- Truth anchor: `D5/S3/ArithUnits/CenteredReducedResidueProgressions.AdmissibleLength`
- Truth anchor: `D5/S3/ArithUnits/CenteredReducedResidueProgressions.CenteredReducedResidue`
- Truth anchor: `D5/S3/ArithUnits/CenteredReducedResidueProgressions.GreatestPrimeFactor`
- Truth anchor: `D5/S3/ArithUnits/CenteredReducedResidueProgressions.result`
- Dependency: [D5/S3/ConceptDynamics/InformationEscape/RegistrationTemplates](../ConceptDynamics/InformationEscape/RegistrationTemplates.md)
