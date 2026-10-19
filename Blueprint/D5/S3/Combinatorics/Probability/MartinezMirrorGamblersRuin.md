# Martinez's mirror-step gambler's ruin limit

## Abstract

The mirror-step ruin probability has Martinez's conjectured limit.

**Definition 1.1 (The boundary recurrence).**

$$\forall p \in \mathbb{R},\; \forall N \in \mathbb{N},\; \forall f \in \mathbb{N} \to \mathbb{R},\; \operatorname{IsWinProbability}\left(p, N, f\right) = ((\operatorname{f}\left(0\right) = 0) \land ((\operatorname{f}\left(N\right) = 1) \land (\forall x \in \mathbb{N},\; (0 < x) \Rightarrow ((x < N) \Rightarrow (\operatorname{f}\left(x\right) = \frac{1 - p}{2} \cdot \operatorname{f}\left(x - 1\right) + p \cdot \operatorname{f}\left(x + 1\right) + \frac{1 - p}{2} \cdot \operatorname{f}\left(N - x\right))))))$$

*Formalization.* `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.IsWinProbability` (`✓ std3`).

*Citation.* L. Martinez (2024). *A symbolic computational approach to the generalized gambler's ruin problem in one and two dimensions*. DOI: [10.48550/arXiv.2412.07667](https://doi.org/10.48550/arXiv.2412.07667). URL: <https://arxiv.org/abs/2412.07667v1>.

*Commentary.*

Section 4.1 (page 11) states: “Define f(x)=f_N^{(p)}(x) as the probability that a particle starting at x will eventually reach N.” The boundary values are f(0)=0 and f(N)=1. Conjecture 5.1 (page 16) specifies: “whenever we restrict the particle moves by either moving from x to x − 1 with probability q₁, or from x to x + 1 with probability p, or from x to N − x with probability q₂ where q₁ = q₂ = (1 − p)/2.” Thus the right-step probability is p and both the left and mirror probabilities are (1 − p)/2. N and x are natural numbers; subtraction of natural indices is truncated. The equation adds transition weights when two destinations coincide. Values beyond N are unrestricted.

**Definition 1.2 (The conjectured radical).**

$$\forall p \in \mathbb{R},\; \operatorname{limitValue}\left(p\right) = \frac{\operatorname{Real}.\operatorname{sqrt}\left((p + 1) \cdot (1 - 3 \cdot p + 4 \cdot p^{2})\right) - (1 - 2 \cdot p) \cdot (p + 1)}{2 \cdot p \cdot (p + 1)}$$

*Formalization.* `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.limitValue` (`✓ std3`).

*Citation.* L. Martinez (2024). *A symbolic computational approach to the generalized gambler's ruin problem in one and two dimensions*. DOI: [10.48550/arXiv.2412.07667](https://doi.org/10.48550/arXiv.2412.07667). URL: <https://arxiv.org/abs/2412.07667v1>.

*Commentary.*

Conjecture 5.1 (page 16): “Consider the generalization of the gambler’s ruin problem when we add a mirror step. If the particle starts at x = 1, then lim_{N→∞} f_N^{(p)}(1) = [√((p + 1)(1 − 3p + 4p²)) − (1 − 2p)(p + 1)] / [2p(p + 1)] whenever we restrict the particle moves by either moving from x to x − 1 with probability q₁, or from x to x + 1 with probability p, or from x to N − x with probability q₂ where q₁ = q₂ = (1 − p)/2.”

**Definition 1.3 (Conjecture 5.1 as a limit statement).**

$$claim = (\forall p \in \mathbb{R},\; (0 < p) \Rightarrow ((p < 1) \Rightarrow (\forall f \in \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right),\; (\forall N \in \mathbb{N},\; (2 \le N) \Rightarrow (\operatorname{IsWinProbability}\left(p, N, \operatorname{f}\left(N\right)\right))) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((N:\mathbb{N} \mapsto \operatorname{f}\left(N, 1\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\operatorname{limitValue}\left(p\right)\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.claim` (`✓ std3`).

*Citation.* L. Martinez (2024). *A symbolic computational approach to the generalized gambler's ruin problem in one and two dimensions*. DOI: [10.48550/arXiv.2412.07667](https://doi.org/10.48550/arXiv.2412.07667). URL: <https://arxiv.org/abs/2412.07667v1>.

*Commentary.*

Conjecture 5.1 (page 16): “Consider the generalization of the gambler’s ruin problem when we add a mirror step. If the particle starts at x = 1, then lim_{N→∞} f_N^{(p)}(1) = [√((p + 1)(1 − 3p + 4p²)) − (1 − 2p)(p + 1)] / [2p(p + 1)] whenever we restrict the particle moves by either moving from x to x − 1 with probability q₁, or from x to x + 1 with probability p, or from x to N − x with probability q₂ where q₁ = q₂ = (1 − p)/2.” The parameter p ranges over all real numbers strictly between zero and one. The family f assigns a real-valued function on the natural numbers to every N. For every N at least two its restriction to zero through N satisfies IsWinProbability. The conclusion is convergence of f N 1 along the natural-number filter atTop.

**Theorem 1.4 (Proof of the complete limit conjecture).**

$$\forall p \in \mathbb{R},\; (0 < p) \Rightarrow ((p < 1) \Rightarrow (\forall f \in \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right),\; (\forall N \in \mathbb{N},\; (2 \le N) \Rightarrow (\operatorname{IsWinProbability}\left(p, N, \operatorname{f}\left(N\right)\right))) \Rightarrow (\operatorname{Filter}.\operatorname{Tendsto}\left((N:\mathbb{N} \mapsto \operatorname{f}\left(N, 1\right)), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\operatorname{limitValue}\left(p\right)\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* L. Martinez (2024). *A symbolic computational approach to the generalized gambler's ruin problem in one and two dimensions*. DOI: [10.48550/arXiv.2412.07667](https://doi.org/10.48550/arXiv.2412.07667). URL: <https://arxiv.org/abs/2412.07667v1>.

*Commentary.*

For positive left, right and mirror weights a,b,c with a+b+c=1, put T=(a+b)/(ab)−2 and r=(T−√(T²−4))/2. Then 0<r<1. Set K₁=1−a/r−br, K₂=1−ar−b/r and R=K₁/c. The identity K₁K₂=c² and the inequality K₁+K₂<0 give R<0. The two coefficient equations are 1=a/r+br+cR and R=aRr+bR/r+c. They verify the finite formula (1−rˣ)(1−Rr^{N − x})/((1−R)(1−rᴺ)). The numerator is a constant plus a linear combination of rˣ and r^{N − x}, so the coefficient equations give the recurrence, and the two endpoint values are zero and one.

Uniqueness requires only a>0 and b,c≥0. The difference of two solutions has zero boundary values. Choose a maximum on the finite interval. At an interior maximizer the averaging equation and the positive left weight force the left neighbour to attain the same maximum. Strong induction reaches a boundary and makes the maximum zero. Applying the argument to both differences proves equality throughout the interval.

At x=1 the powers rᴺ and r^{N−1} tend to zero, giving the limit (1−r)/(1−R). For a=c=(1 − p)/2 and b=p this positive limit L satisfies p(p + 1)L²+(1 − 2p)(p + 1)L−p(1−p)=0. The positive square-root branch gives limitValue p. Equality of the finite solutions for every N≥2 transfers convergence to every family in claim. The expected duration of the walk is a separate question.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.IsWinProbability`
- Truth anchor: `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.claim`
- Truth anchor: `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.limitValue`
- Truth anchor: `D5/S3/Combinatorics/Probability/MartinezMirrorGamblersRuin.result`
