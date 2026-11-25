# Signed overlap contributions and degree-sensitive remainder

## Abstract

Conjugate phases resolve each overlap contribution into a signed real square.

**Theorem 1.1 (Signed mixed coefficients).**

$$\begin{aligned}&[x^{d}y^{d}]Q=\sum_{T \subseteq s,|T| \le d}(-1)^{|T|}|\operatorname{C}\left(T\right)|^{2}\\&\forall T \subseteq s, |\operatorname{C}\left(T\right)| \le \operatorname{B}\left(T\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DisjointCharacterRemainder.signed_overlap_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let s be any finite index set and a any complex phase family. Set c to the sum of a over s. Let Q be the product over s of the factors exp(a(j)x) + exp(conj(a(j))y) - 1, and let C(T) be the degree-d coefficient of exp(cx) times the product over T of exp(-a(j)x) - 1. The bound B(T) is zero for |T| > d. For |T| ≤ d it is the product of |a(j)| on T times (|c| plus the sum of |a(j)| on T)^(d-|T|)/(d-|T|)!.

Use the disjoint coefficient factorization. In the second variable each local correction is the negative of the conjugate correction in the first variable. Conjugation commutes with extraction of coefficients and the finite product. A subset therefore contributes a real square with sign determined by its cardinality.

The complex exponential tail at an index is majorized coefficient by coefficient by |a(j)| x exp(|a(j)|x), since 1/n! ≤ 1/(n-1)! for n≥1. The Cauchy product preserves coefficientwise domination of norms by nonnegative coefficients. Multiplying the majorants extracts |T| powers of x and adds the real exponents, proving B(T) including the vanishing at insufficient degree.

**Theorem 1.2 (Parity bounds for a truncated sum).**

$$\begin{aligned}&R=\sum_{T \in E}|\operatorname{C}\left(T\right)|^{2}-\sum_{T \in O}|\operatorname{C}\left(T\right)|^{2}\\&-\sum_{T \in O}\operatorname{B}\left(T\right)^{2} \le R \le \sum_{T \in E}\operatorname{B}\left(T\right)^{2}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/DisjointCharacterRemainder.signed_overlap_remainder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural numbers d and K take the real part of the mixed coefficient and subtract the alternating sum over subsets T with |T|≤min(d,K). Denote the resulting remainder by R. The large subsets satisfy K<|T|≤d. E and O designate their even and odd cardinality classes.

Split the expansion into the retained part and these two classes. The even class contributes positive squares and the odd class contributes negative squares. Their exact difference and the coefficientwise bound give the stated one-sided errors. For K≥d the remainder is zero. For a cyclic character with a(j)=w(j) times the character, the same inequalities can be summed against the nonnegative Fejér weights. Bounds for the remaining weighted character sums of zeta ordinates at the growing degree and time scale require additional arithmetic.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/DisjointCharacterRemainder.signed_overlap_expansion`
- Truth anchor: `D5/S3/Fourier/Concentration/DisjointCharacterRemainder.signed_overlap_remainder`
- Dependency: [D5/S3/Fourier/Concentration/DisjointCharacterEnvelope](DisjointCharacterEnvelope.md)
