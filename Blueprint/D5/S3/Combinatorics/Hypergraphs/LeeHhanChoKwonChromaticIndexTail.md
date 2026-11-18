# The chromatic-index tail conjecture of Lee, Hhan, Cho and Kwon

## Abstract

A fixed nonempty hyperedge prefix refutes the proposed chromatic-index failure bound.

**Definition 1.1 (Chromatic index of labelled hyperedges).**

$$\forall k \in \operatorname{Nat},\; \forall alpha \in \operatorname{Nat},\; \forall e \in \operatorname{Fin}\left(alpha\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right),\; \operatorname{chromaticIndex}\left(e\right) = \operatorname{sInf}\left(\{c: \operatorname{Nat} \mid \exists f \in \operatorname{Fin}\left(alpha\right) \to \operatorname{Fin}\left(c\right),\; \forall i \in \operatorname{Fin}\left(alpha\right),\; \forall j \in \operatorname{Fin}\left(alpha\right),\; (i \ne j) \Rightarrow ((\operatorname{Finset}.\operatorname{Nonempty}\left(\operatorname{Finset}.\operatorname{inter}\left(e\left(i\right), e\left(j\right)\right)\right)) \Rightarrow (f\left(i\right) \ne f\left(j\right)))\}\right)$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.chromaticIndex` (`✓ std3`).

*Citation.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Supplemental Material §4, p. 17: “Then, the chromatic index χ′(H) of H is exactly the minimum depth of applying all the gates.” The vertices are Fin k and the labelled edge occurrences are Fin alpha. The least natural colour count is taken over functions assigning different colours to distinct intersecting occurrences. Equal nonempty edge sets retain distinct occurrence indices.

**Definition 1.2 (The uniform chromatic-index tail).**

$$\forall k \in \operatorname{Nat},\; \forall m \in \operatorname{Nat},\; \forall alpha \in \operatorname{Nat},\; \forall x \in \operatorname{Real},\; \operatorname{tailProb}\left(k, m, alpha, x\right) = \frac{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left((\operatorname{fun} (e: \operatorname{Fin}\left(alpha\right) \to \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right)) \mapsto x < (\operatorname{chromaticIndex}\left(e\right): \operatorname{Real})), \operatorname{Fintype}.\operatorname{piFinset}\left(\operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(alpha\right), \operatorname{Finset}.\operatorname{powersetCard}\left(m, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))\right)\right)\right)\right)\right): \operatorname{Real})}{(\operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{powersetCard}\left(m, (\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(k\right)\right))\right)\right)^{alpha}: \operatorname{Real})}$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.tailProb` (`✓ std3`).

*Citation.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Supplemental Material §4, p. 17: “Each edge of H contains v with the probability of m/k. Since each edge is sampled independently”. Each of the alpha coordinates ranges independently over Finset.univ.powersetCard m on Fin k. The numerator counts ordered tuples whose chromatic index exceeds the real threshold x; the denominator counts all ordered tuples. Repeated edges are allowed. Both counts are coerced to Real before division.

**Definition 1.3 (A particular failure-level family).**

$$\forall c \in \operatorname{Real},\; \forall t \in \operatorname{Nat},\; \operatorname{eps}\left(c, t\right) = (2: \operatorname{Real})^{-(t: \operatorname{Real})^{1 + c}}$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.eps` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Choose eps(c,t) = 2 raised to minus t raised to 1+c, a particular family in the regime of Supplemental Material §4, p. 18: “if log(1/ϵ) scales with t^{1+c} for some c > 0”. For positive t this gives log₂(1/eps(c,t)) = t^(1+c). The exponent and base in eps are real.

**Definition 1.4 (The number of vertices).**

$$\forall c \in \operatorname{Real},\; \forall t \in \operatorname{Nat},\; \operatorname{kParam}\left(c, t\right) = \operatorname{Nat}.\operatorname{ceil}\left(3 \cdot \operatorname{Real}.\operatorname{logb}\left(2, \frac{(t: \operatorname{Real})^{2}}{\operatorname{eps}\left(c, t\right)}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.kParam` (`✓ std3`).

*Citation.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Supplemental Material §4, p. 17: “Additionally, let us set k = 3 log(t²/ϵ), m = log t, and α = βt log(1/ϵ).” Logarithms are base two. The number of vertices is the natural ceiling of 3 log₂(t²/eps(c,t)); Nat.ceil is the natural ceiling, including its truncation at zero.

**Definition 1.5 (The number of edge occurrences).**

$$\forall c \in \operatorname{Real},\; \forall beta \in \operatorname{Real},\; \forall t \in \operatorname{Nat},\; \operatorname{alphaParam}\left(c, beta, t\right) = \operatorname{Nat}.\operatorname{ceil}\left(beta \cdot (t: \operatorname{Real}) \cdot \operatorname{Real}.\operatorname{logb}\left(2, \frac{1}{\operatorname{eps}\left(c, t\right)}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.alphaParam` (`✓ std3`).

*Citation.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Supplemental Material §4, p. 17: “Additionally, let us set k = 3 log(t²/ϵ), m = log t, and α = βt log(1/ϵ).” The number of independently sampled edge occurrences is the natural ceiling of beta times t times log₂(1/eps(c,t)). All products inside Nat.ceil are real.

**Definition 1.6 (The failure-probability conjecture).**

$$\operatorname{claim} = (\forall c \in \operatorname{Real},\; \forall beta \in \operatorname{Real},\; (0 < c) \Rightarrow ((1 + c < beta) \Rightarrow (\exists C \in \operatorname{Real},\; \exists T \in \operatorname{Nat},\; \forall t \in \operatorname{Nat},\; (T \le t) \Rightarrow (\operatorname{tailProb}\left(\operatorname{kParam}\left(c, t\right), \operatorname{Nat}.\operatorname{ceil}\left(\operatorname{Real}.\operatorname{logb}\left(2, (t: \operatorname{Real})\right)\right), \operatorname{alphaParam}\left(c, beta, t\right), C \cdot (t: \operatorname{Real}) \cdot \operatorname{Real}.\operatorname{logb}\left(2, (t: \operatorname{Real})\right)\right) < \operatorname{eps}\left(c, t\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.claim` (`✓ std3`).

*Citation.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Supplemental Material §4, p. 18, after Eq. (87): “We conjecture that in this regime, χ′(H) is upper bounded by O(t log t) with a failure probability smaller than ϵ.” The preceding regime is “if log(1/ϵ) scales with t^{1+c} for some c > 0, and β is set by β > 1 + c”. The encoding uses real c and beta with 0 < c and 1+c < beta, the particular family eps(c,t), natural t, m = Nat.ceil(log₂ t), kParam and alphaParam. The big-O bound means that a real constant C works for all natural t beyond a natural threshold T. The probability inequality is strict.

**Theorem 1.7 (Refutation by a fixed-edge prefix).**

$$\neg (\forall c \in \operatorname{Real},\; \forall beta \in \operatorname{Real},\; (0 < c) \Rightarrow ((1 + c < beta) \Rightarrow (\exists C \in \operatorname{Real},\; \exists T \in \operatorname{Nat},\; \forall t \in \operatorname{Nat},\; (T \le t) \Rightarrow (\operatorname{tailProb}\left(\operatorname{kParam}\left(c, t\right), \operatorname{Nat}.\operatorname{ceil}\left(\operatorname{Real}.\operatorname{logb}\left(2, (t: \operatorname{Real})\right)\right), \operatorname{alphaParam}\left(c, beta, t\right), C \cdot (t: \operatorname{Real}) \cdot \operatorname{Real}.\operatorname{logb}\left(2, (t: \operatorname{Real})\right)\right) < \operatorname{eps}\left(c, t\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result` (`✓ std3`). ∎

*Resolves.* `Problems/lee-hhan-cho-kwon-2025-chromatic-index-tail` (refuted) by `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lee-hhan-cho-kwon-2025-chromatic-index-tail","declaration_gid":"D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* W. Lee; M. Hhan; G. Y. Cho; H. Kwon (2025). *Shallow quantum circuit for generating extremely low-entangled approximate state designs*. DOI: [10.48550/arXiv.2507.17871](https://doi.org/10.48550/arXiv.2507.17871). URL: <https://arxiv.org/abs/2507.17871v3>.

*Commentary.*

Take c = 1 and beta = 3. A prefix of r copies of one nonempty m-edge needs at least r colours. Counting all possible suffixes gives the lower bound 1/k^(m*r) for the tail whenever the threshold is below r. For any proposed C and T, choose L = max(1,Nat.ceil C), s = max(64,max(T,32*(L+1))), q = 2^s, t = 2^q and r = L*t*q+1. Then k = 3*t²+6*q, m = q and alpha = 3*t³. The inequalities r ≤ alpha, C*t*log₂(t) < r, k ≤ 2^(2*q+3) and (2*q+3)*q*r < t² give tailProb > 2^(−t²) = eps(1,t). The exact binomial bound (m/k)^r and a variant requiring pairwise distinct edges are outside this proof. The weaker probability 1 − O(1/log t) in Eq. (87) is not refuted.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.alphaParam`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.chromaticIndex`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.claim`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.eps`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.kParam`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.result`
- Truth anchor: `D5/S3/Combinatorics/Hypergraphs/LeeHhanChoKwonChromaticIndexTail.tailProb`
