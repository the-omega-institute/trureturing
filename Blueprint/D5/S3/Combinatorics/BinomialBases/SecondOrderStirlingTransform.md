# The complete second-order factorial-Stirling transform

## Abstract

A factorial-Stirling identity holds for every complex sequence satisfying a second-order linear recurrence, including zero parameters and every nonnegative offset.

**Theorem 1.1 (The uniform recurrence identity).**

$$\forall p \in \mathbb{C},\; \forall q \in \mathbb{C},\; \forall ell \in \mathbb{N},\; \forall c \in \mathbb{N},\; \forall u \in \mathbb{N} \to \mathbb{C},\; (\forall n \in \mathbb{N},\; \operatorname{u}\left(n + 2\right) = p \cdot \operatorname{u}\left(n + 1\right) + q \cdot \operatorname{u}\left(n\right)) \Rightarrow (\sum_{m \in \operatorname{range}\left(ell + 1\right)} ((-1)^{m} \cdot ((\operatorname{factorial}\left(m\right) \cdot \operatorname{S}\left(ell + 1, m + 1\right)) : \mathbb{C}) \cdot (q)^{ell - m} \cdot \operatorname{u}\left(2 \cdot m + c\right)) = (-1)^{ell} \cdot \sum_{m \in \operatorname{range}\left(ell + 1\right)} (((\operatorname{factorial}\left(m\right) \cdot \operatorname{S}\left(ell, m\right)) : \mathbb{C}) \cdot (p)^{m} \cdot (q)^{ell - m} \cdot \operatorname{u}\left(m + c\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniele Parisse (2024). *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*. DOI: [10.5281/zenodo.13331499](https://doi.org/10.5281/zenodo.13331499). URL: <https://math.colgate.edu/~integers/y70/y70.pdf>.

*Commentary.*

This is a direct formal polynomial derivation of an all-parameter consequence of classical Stirling and geometric-polynomial identities. Kargin's equation (21) gives the reflection including degree zero. Zeitlin's Theorem 9, equations (4.21) and (4.23), provides the real nonzero-parameter antecedent under the correction on page 182; Kellner's Corollary 3.3 gives the positive-degree polynomial symmetry. The exact normalizations and scope restrictions are recorded in the cited note. No priority claim is made for this sum or its zero-parameter extension.

Here S(n,k) is Nat.stirlingSecond n k. Each factorial-Stirling coefficient is computed in Nat before casting to Complex. A range ending at ell+1 contains precisely 0 through ell; subtraction in the exponent is natural subtraction. The two initial values of u are arbitrary. In particular q=0 imposes no equation between u(0) and u(1). Both sides at ell=0 equal u(c), including c=0 and c=1.

Write Q for the existing ordinary factorial-Stirling row polynomial and H for the shifted row with coefficients m! S(ell+1,m+1). Their differential recurrences prove H(-1-X)=(-1)^ell Q(X) for every degree. Homogenization supplies the powers of q without division. Pair a polynomial with u by summing its coefficients against u(j+c). The recurrence makes this pairing vanish on every multiple of X squared minus p X minus q. The difference-of-powers identity then replaces (q+p X) raised to m by X raised to 2m inside the pairing, yielding both finite sums. This argument retains zero parameters, repeated roots, zero initial data and nonnegative offsets without an inverse shift.

## References

- Truth anchor: `D5/S3/Combinatorics/BinomialBases/SecondOrderStirlingTransform.result`
- Dependency: [D5/S3/Combinatorics/ParisseStirlingFibonacciAlternatingSum](../ParisseStirlingFibonacciAlternatingSum.md)
