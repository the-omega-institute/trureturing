# Signed cardinality need not be zero-mesic

## Abstract

A literal 73-state orbit on a 3 by 12 rectangle has signed-cardinality sum minus one.

**Definition 1.1 (The signed point statistic).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall x \in \operatorname{Point}\left(m, n\right),\; \operatorname{signedWeight}\left(x\right) = \operatorname{ite}\left(\operatorname{Even}\left(\operatorname{val}\left(x.1\right) + \operatorname{val}\left(x.2\right)\right), 1, -1\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.signedWeight` (`✓ std3`).

*Citation.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Commentary.*

Definition 3.17 (p. 21) reads: “Fix a finite poset P. For each x ∈ P, define the signed cardinality statistic SC(x): P → {−1, 1} as follows:” followed by SC(x) = 1 if rk(x) is even and −1 if rk(x) is odd. The zero-based point x in Point(m,n) = Fin m × Fin n has rank val(x.1) + val(x.2), equal to i + j − 2 for the paper's one-based coordinates (i,j). The integer conditional ite has its usual if-then-else meaning.

**Definition 1.2 (The signed statistic on a set).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall I \in \operatorname{Set}\left(\operatorname{Point}\left(m, n\right)\right),\; \operatorname{signedCardinality}\left(I\right) = \sum_{x \in \{x \in \operatorname{Point}\left(m, n\right) \mid \operatorname{mem}\left(x, I\right)\}} \operatorname{signedWeight}\left(x\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.signedCardinality` (`✓ std3`).

*Citation.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Commentary.*

Definition 3.17 (p. 21) reads: “For an interval-closed set I, SC(I) = ∑_{x∈I} SC(x).” The finite sum selects the members of I from all points of the rectangle. The same expression defines the statistic on every set, including the empty set.

**Definition 1.3 (Conjecture 4.12).**

$$claim \Leftrightarrow \left(\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall N \in \mathbb{N},\; ((m = 2) \lor (m = 3)) \Rightarrow \left((1 \le n) \Rightarrow \left((\operatorname{Even}\left(m + n - 1\right)) \Rightarrow \left(\forall e \in \operatorname{Equiv}\left(\operatorname{Fin}\left(N\right), \operatorname{Point}\left(m, n\right)\right),\; (\operatorname{ReverseExtension}\left(e\right)) \Rightarrow \left(\forall I \in \operatorname{Set}\left(\operatorname{Point}\left(m, n\right)\right),\; (\operatorname{OrdConnected}\left(I\right)) \Rightarrow \sum_{S \in \operatorname{literalOrbit}\left(e, I\right)} \operatorname{signedCardinality}\left(S\right) = 0\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.claim` (`✓ std3`).

*Citation.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Commentary.*

Conjecture 4.12 (p. 29) reads: “If m = 2 or m = 3, then the signed cardinality statistic is 0-mesic under rowmotion on interval-closed sets of [m]×[n] whenever m + n − 1 is even.” Definition 3.17 (p. 21) defines SC(x) = 1 if rk(x) is even and −1 if rk(x) is odd, and states: “For an interval-closed set I, SC(I) = ∑_{x∈I} SC(x).” Definition 2.6 (p. 4) reads: “Let x ∈ P and I ∈ IC(P) an interval-closed set of P. Define the toggle t_x: IC(P) → IC(P) as follows:” If x ∈ I, t_x(I) = I − {x} if I − {x} ∈ IC(P), and I otherwise. If x ∉ I, t_x(I) = I ∪ {x} if I ∪ {x} ∈ IC(P), and I otherwise. Its final sentence is: “That is, x is toggled in/out of I if doing so results in another interval-closed set.” Definition 2.9 (p. 5) reads: “Given an interval-closed set I ∈ IC(P), the rowmotion of I, Row(I), is given by applying all toggles in the reverse order of any linear extension.” Definition 2.24 (p. 10) reads: “We say that a statistic exhibits homomesy under some action when every orbit of that action has the same average when the statistic is calculated over the orbit.” Here N ranges over all enumeration lengths and e ranges over all equivalences Fin N ≃ Point(m,n); ReverseExtension(e) is precisely a complete enumeration in the reverse order of a linear extension. The reused trace applies the actual toggles, using symmetric difference and OrdConnected, and literalOrbit contains every distinct forward iterate once. Zero average on this nonempty finite orbit is equivalent to zero sum. The dimension n is positive, and subtraction in m + n − 1 is natural-number subtraction. Every linear extension and every interval-closed set are quantified. The follow-up retains the m = 3 case as a conjecture.

**Theorem 1.4 (The conjecture is refuted).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Jennifer Elder, Nadia Lafrenière, Erin McNicholas, Jessica Striker, Amanda Welch (2024). *Toggling, rowmotion, and homomesy on interval-closed sets*. DOI: [10.48550/arXiv.2307.08520](https://doi.org/10.48550/arXiv.2307.08520). URL: <https://arxiv.org/abs/2307.08520v2>.

*Acknowledgement.* Nadia Lafrenière, Joel Brewster Lewis, Erin McNicholas, Jessica Striker, Amanda Welch (2025). *Interval-closed set rowmotion and homomesy on products of two chains*. DOI: [10.48550/arXiv.2505.04000](https://doi.org/10.48550/arXiv.2505.04000). URL: <https://arxiv.org/abs/2505.04000v1>.

*Commentary.*

Take m = 3, n = 12 and the row-major linear extension. In one-based coordinates the initial set is {(1,7),(3,2),(3,3),(3,4),(3,5)}. Its literal rowmotion orbit has 73 distinct states and signed-cardinality sum −1, giving average −1/73. A bitmask uses bit j + 12i for the zero-based point (i,j). Lower- and upper-set masks certify order-convexity: a missing point cannot have both an included point below it and an included point above it. The encoding commutes with every actual toggle and every trace step. All 73 transitions, including the return to the seed, and the sum are checked; injectivity of the decoded cycle and induction identify it with the full distinct-state orbit. The even number of ranks does not force cancellation within an orbit.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.signedCardinality`
- Truth anchor: `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.signedWeight`
- Dependency: [D5/S3/Combinatorics/Geometry/RectangleRowmotionHomomesy](RectangleRowmotionHomomesy.md)
