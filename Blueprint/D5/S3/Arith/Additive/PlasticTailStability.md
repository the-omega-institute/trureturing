# Right-endpoint defects and consecutive tails

## Abstract

The deficit in the plastic-template count controls missing endpoint patterns, large gaps, and actual consecutive intervals in the tail.

All exponent sets are finite subsets of the integers. Write C(E) for the count of the four plastic templates, represented by their unique right endpoints. The indicator ind(Q) is 1 when Q holds and 0 otherwise. The integer interval I(a,b) is {t ∈ Z : a ≤ t ≤ b}. For x : N → Z, P(x,k) consists of x(0),…,x(k−1). The values of x outside the first n positions are unrestricted. Strict increase is required only for 0 ≤ i < j < n, so every increasingly enumerated finite integer set is included, without any restriction on signs or gap sizes.

**Definition 1.1 (Completed patterns at an endpoint).**

$$\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), \forall (t : \mathbb{Z}), \operatorname{completed}\left(E, t\right) = \operatorname{ind}\left(((t - 1 \in E) \land (t - 2 \in E)) \land (t - 4 \in E)\right) + \operatorname{ind}\left(((t - 1 \in E) \land (t - 3 \in E)) \land (t - 6 \in E)\right) + \operatorname{ind}\left((t - 2 \in E) \land (t - 7 \in E)\right) + \operatorname{ind}\left(((t - 1 \in E) \land (t - 4 \in E)) \land (t - 9 \in E)\right)$$

*Formalization.* `D5/S3/Arith/Additive/PlasticTailStability.completed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Each summand tests the earlier points required by one of the four right-endpoint offset sets {1,2,4}, {1,3,6}, {2,7}, and {1,4,9}. Only membership of these predecessors is tested; the endpoint itself need not belong to E in this definition.

**Definition 1.2 (The finite prefix set).**

$$\forall (x : \mathbb{N} \to \mathbb{Z}), \forall (k : \mathbb{N}), \operatorname{P}\left(x, k\right) = \operatorname{image}\left(x, \operatorname{range}\left(k\right)\right)$$

*Formalization.* `D5/S3/Arith/Additive/PlasticTailStability.prefixSet` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Here range(k) is {0,…,k−1} and image(x,S) is the finite image {x(i) : i ∈ S}. Under strict increase on the first n positions, this prefix has cardinality k whenever k ≤ n.

For the theorem, set E=P(x,n), P=P(x,10), T=E∖P, c(i)=completed(P(x,i),x(i)), δ=4n−26−C(E), and K=1+floor(δ/3). Define B={i ∈ N : 10 ≤ i < n and c(i)<4}, B₂={i ∈ N : 10 ≤ i < n and x(i)−x(i−1)=2}, and B₃={i ∈ N : 10 ≤ i < n and x(i)−x(i−1)≥3}. Union(R) denotes the union of the finite family R, and tailImage(x,m,n)={x(i) : m ≤ i < n}. The zero-based indices 10,…,n−1 are precisely the endpoints after the first ten points; index 9 is the tenth point. The count bound makes δ the ordinary nonnegative integer deficit. Likewise C(P) ≤ 14 and every c(i) ≤ 4, so the subtractions in the deficit identity are not truncated. Since K is positive, floor((n−10+K−1)/K) equals ceil((n−10)/K).

**Theorem 1.3 (Defect accounting and tail stability).**

$$\forall (n : \mathbb{N}), (10 \le n) \Rightarrow (\forall (x : \mathbb{N} \to \mathbb{Z}), (\forall (i : \mathbb{N}), \forall (j : \mathbb{N}), ((i < j) \land (j < n)) \Rightarrow (x\left(i\right) < x\left(j\right))) \Rightarrow ((((((\operatorname{C}\left(E\right) \le 4 \cdot n - 26) \land (\delta = 14 - \operatorname{C}\left(P\right) + \sum_{(10 \le i) \land (i < n)} (4 - c\left(i\right)))) \land (\lvert B\rvert  \le \delta)) \land (3 \cdot \lvert B_{2}\rvert  + 4 \cdot \lvert B_{3}\rvert  \le \delta)) \land ((10 < n) \Rightarrow ((\exists (R : \operatorname{Finset}\left(\operatorname{Finset}\left(\mathbb{Z}\right)\right)), (\operatorname{Union}\left(R\right) = T) \land ((\lvert R\rvert  \le K) \land (\forall (J : \operatorname{Finset}\left(\mathbb{Z}\right)), (J \in R) \Rightarrow (\exists (a : \mathbb{Z}), \exists (b : \mathbb{Z}), (a \le b) \land (J = \operatorname{I}\left(a, b\right)))))) \land (\exists (a : \mathbb{Z}), \exists (b : \mathbb{Z}), (\operatorname{I}\left(a, b\right) \subseteq T) \land ((a \le b) \land (\lfloor\frac{n - 10 + K - 1}{K}\rfloor \le \lvert \operatorname{I}\left(a, b\right)\rvert )))))) \land ((\delta \le 2) \Rightarrow (\operatorname{tailImage}\left(x, 9, n\right) = \operatorname{I}\left(x\left(9\right), x\left(n - 1\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticTailStability.whole_theorem_three_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Every completed template has one right endpoint, so C(E) is the sum of its endpoint contributions. Positive offsets ensure that the contribution at x(i) is already determined by its preceding prefix. Splitting this sum after ten points gives the exact defect identity. The ten-point bound gives C(P) ≤ 14; each incomplete endpoint contributes at least one unit of deficit. A gap of two excludes all three patterns requiring offset one, and a gap of at least three excludes every pattern, since each requires offset one or two. Their losses are therefore at least three and four, respectively. The starts of consecutive runs in T are its least point and some of the gap endpoints. Thus their number is at most 1+|B₂|+|B₃| ≤ K. Taking the longest interval among these runs and bounding the cardinality of their union proves the rounded-up length bound. If δ ≤ 2, no gap after the tenth point can exceed one, so all points from x(9) through x(n−1) fill their integer interval. When n=10 this last interval is a singleton; the separate nonempty-tail conclusion is asserted only when n>10.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticTailStability.completed`
- Truth anchor: `D5/S3/Arith/Additive/PlasticTailStability.prefixSet`
- Truth anchor: `D5/S3/Arith/Additive/PlasticTailStability.whole_theorem_three_three`
- Dependency: [D5/S3/Arith/Additive/PlasticExtremal](PlasticExtremal.md)
