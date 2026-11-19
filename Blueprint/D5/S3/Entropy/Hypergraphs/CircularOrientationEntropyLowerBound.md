# Circular orientation entropy: an explicit lower bound

## Abstract

The fixed-uniformity entropy lower bound for circular orientations.

For n > r, circular n r has vertices Fin n and the n labelled edges {i,i+1,...,i+r-1}, with vertex indices reduced modulo n. Independently choose one vertex uniformly from each edge, and let X be the cardinality of the image of the resulting choice function. The entropy is exactly the existing OrientationEntropyBalance.entropyX: the finite sum of -p log₂ p over k=0,...,n, with p the literal orientation count for X=k divided by r^n. The convention at zero is 0 log₂ 0=0. This is not the circular-maximality claim.

**Definition 1.1 (Endpoint avoidance probability).**

$$\forall r \in \mathbb{N},\; \operatorname{a}\left(r\right) = (1 - \frac{1}{r})^{r - 1}$$

*Formalization.* `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exponent r-1 is natural subtraction. The base and division are real. For r≥3 this is the probability that r-1 independent incident edges avoid a fixed endpoint.

**Definition 1.2 (Good-endpoint probability).**

$$\forall r \in \mathbb{N},\; \operatorname{q}\left(r\right) = \operatorname{a}\left(r\right) \cdot (1 - \operatorname{a}\left(r\right))$$

*Formalization.* `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The left incident choices avoid one endpoint, while the disjoint right incident choices hit the other endpoint at least once.

**Definition 1.3 (Bernoulli variance threshold).**

$$\forall r \in \mathbb{N},\; \operatorname{b}\left(r\right) = \frac{r - 1}{r^{2}}$$

*Formalization.* `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator r-1 is subtraction after casting r to the reals. For an integer k between 1 and r-1, p=k/r satisfies p(1-p)≥b(r).

**Definition 1.4 (Characteristic-function decay constant).**

$$\forall r \in \mathbb{N},\; \operatorname{c}\left(r\right) = \operatorname{q}\left(r\right) \cdot (1 - \mathit{Real}.\mathit{exp}\left(-2 \cdot \operatorname{b}\left(r\right)\right))$$

*Formalization.* `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.c` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The proof establishes c(r)>0 for every natural r≥3.

**Definition 1.5 (Explicit entropy offset).**

$$\forall r \in \mathbb{N},\; \operatorname{K}\left(r\right) = \operatorname{max}\left(\frac{1}{2}, \frac{1}{2} \cdot \mathit{Real}.\mathit{logb}\left(2, \frac{\mathit{Real}.\mathit{pi}}{\operatorname{c}\left(r\right)}\right)\right)$$

*Formalization.* `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K depends only on r. The maximum with one half includes every integer in the finite regime r<n<2r, not just sufficiently large n.

**Theorem 1.6 (The full fixed-uniformity lower bound).**

$$\forall r \in \mathbb{N},\; \forall n \in \mathbb{N},\; 3 \le r \Rightarrow \left(r < n \Rightarrow \frac{1}{2} \cdot \mathit{Real}.\mathit{logb}\left(2, \frac{n}{r}\right) - \operatorname{K}\left(r\right) \le \mathit{OrientationEntropyBalance}.\mathit{entropyX}\left(r, \mathit{CircularOrientationEntropy}.\mathit{circular}\left(n, r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.whole_theorem_one_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All natural r≥3 and n>r are quantified. The functions circular and entropyX in the formula are the existing CircularOrientationEntropy.circular and OrientationEntropyBalance.entropyX, not new distributions or abstract hypotheses. All fractions and logarithms in the inequality are real-valued; logb 2 is the base-two logarithm.

For n≥2r, choose m=⌊n/(2r)⌋ edges starting at 2rj. The proof verifies their actual cyclic geometry, including the neighbourhood crossing zero. Splitting the finite choice space into selected and revealed coordinates gives, on every actual fibre, X=B+Σ Zj. Disjoint coordinate supports give the joint generating function of the good-endpoint events, each with probability q(r). Their occurrence forces the corresponding unseen-vertex count between 1 and r-1. These are proved properties of the original orientation law, not assumptions of the theorem.

Averaging the fibre characteristic functions after taking absolute values removes the random phase B. The resulting decay is exp(-m c(r) sin²(t/2)). Finite Fourier inversion, the sine lower bound and the Gaussian integral bound every point mass by √(πr/(c(r)n)). The largest-atom entropy inequality yields the displayed bound. Nonnegativity of the same finite entropy handles r<n<2r. The constant is not asserted uniform in r, and no entropy-maximality conclusion is made.

## References

- Truth anchor: `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.K`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.a`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.b`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.c`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.q`
- Truth anchor: `D5/S3/Entropy/Hypergraphs/CircularOrientationEntropyLowerBound.whole_theorem_one_two`
- Dependency: [D5/S0/Certificates/Hypergraphs/CircularOrientationEntropy](../../../S0/Certificates/Hypergraphs/CircularOrientationEntropy.md)
- Dependency: [D5/S3/Entropy/Hypergraphs/FiniteFiber](FiniteFiber.md)
- Dependency: [D5/S3/Entropy/Hypergraphs/FiniteFourier](FiniteFourier.md)
