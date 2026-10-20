# Digit-Sum Arcs: Infinitude and Natural Density

## Abstract

The attainable positive digit sums of multiples form an additive semigroup whose gcd determines its eventual support and density.

All number variables are natural numbers, with positivity stated explicitly. Nat.digits lists the digits from least to most significant. The digit sum is List.sum (Nat.digits b N). Set.ncard counts the finite intersection with the inclusive interval [1,x]; ratios and density values are real.

**Definition 1.1 (Positive outgoing digit-sum arcs).**

$$\forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; \operatorname{Out}\left(b, n\right) = (\{u : \mathbb{N} \mid (0 < u) \land (\exists N \in \mathbb{N},\; (0 < N) \land ((n \mid N) \land (\operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(b, N\right)\right) = (u))))\})$$

*Formalization.* `D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.Out` (`✓ std3`).

*Citation.* P. N. Phunphayap; P. Noppakaew; P. Pongsriiam (2023). *Directed graphs of integers with arcs determined by an arithmetic function*. DOI: [10.61091/um124-06](https://doi.org/10.61091/um124-06). URL: <https://arxiv.org/abs/2303.13017v1>.

*Commentary.*

The source defines an arc on p. 2: “We say that there exists a g-directed edge or g-arc from n to u if there exists a positive integer N such that N is divisible by n and g(N) = u.” It then sets “Out(g, n) = {u ∈ ℕ | n →g u}.” Here g is the base-b digit sum, and both u and N are positive. On p. 3 the examples are s₁₀(123) = 6 and s₅(123) = 11.

**Definition 1.2 (The answer to Question 3).**

$$(claim) \Leftrightarrow (\forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; (2 \le b) \Rightarrow ((1 \le n) \Rightarrow (((\operatorname{Set}.\operatorname{Infinite}\left((\operatorname{Out}\left(b, n\right) \setminus \{u : \mathbb{N} \mid \operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(b, n\right)\right) \mid u\})\right)) \Leftrightarrow (\operatorname{Nat}.\operatorname{gcd}\left((b - 1), n\right) < \operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(b, n\right)\right))) \land (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (x: \mathbb{N}) \mapsto \frac{(\operatorname{Set}.\operatorname{ncard}\left(\operatorname{Set}.\operatorname{inter}\left(\operatorname{Out}\left(b, n\right), \operatorname{Set}.\operatorname{Icc}\left(1, x\right)\right)\right): \mathbb{R})}{(x: \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\frac{1}{(\operatorname{Nat}.\operatorname{gcd}\left((b - 1), n\right): \mathbb{R})}\right)\right)))))$$

*Formalization.* `D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* P. N. Phunphayap; P. Noppakaew; P. Pongsriiam (2023). *Directed graphs of integers with arcs determined by an arithmetic function*. DOI: [10.61091/um124-06](https://doi.org/10.61091/um124-06). URL: <https://arxiv.org/abs/2303.13017v1>.

*Commentary.*

Question 3 (arXiv:2303.13017v1, p. 10): “We obtain in Theorem 2 that Out(s_b, n) contains every multiple of s_b(n). Does Out(s_b, n) contain an infinite number of positive integers that are not divisible by s_b(n)? When d = 1 and s_b(n) ≥ 2, the answer is yes. Can we determine a simple necessary and sufficient condition for the infinitely many elements in A ∩ Out(s_b, n) where A is the set of positive integers that are not divisible by s_b(n)? In that case, does Out(s_b, n) has a natural density?” The answer holds for every base b ≥ 2 and positive n. Writing d = Nat.gcd (b − 1) n, the intersection in the question is infinite exactly when d is smaller than List.sum (Nat.digits b n), and the density is 1/d.

**Theorem 1.3 (Infinitude Criterion and Density).**

$$\forall b \in \mathbb{N},\; \forall n \in \mathbb{N},\; (2 \le b) \Rightarrow ((1 \le n) \Rightarrow (((\operatorname{Set}.\operatorname{Infinite}\left((\operatorname{Out}\left(b, n\right) \setminus \{u : \mathbb{N} \mid \operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(b, n\right)\right) \mid u\})\right)) \Leftrightarrow (\operatorname{Nat}.\operatorname{gcd}\left((b - 1), n\right) < \operatorname{List}.\operatorname{sum}\left(\operatorname{Nat}.\operatorname{digits}\left(b, n\right)\right))) \land (\operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (x: \mathbb{N}) \mapsto \frac{(\operatorname{Set}.\operatorname{ncard}\left(\operatorname{Set}.\operatorname{inter}\left(\operatorname{Out}\left(b, n\right), \operatorname{Set}.\operatorname{Icc}\left(1, x\right)\right)\right): \mathbb{R})}{(x: \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, \operatorname{nhds}\left(\frac{1}{(\operatorname{Nat}.\operatorname{gcd}\left((b - 1), n\right): \mathbb{R})}\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* P. N. Phunphayap; P. Noppakaew; P. Pongsriiam (2023). *Directed graphs of integers with arcs determined by an arithmetic function*. DOI: [10.61091/um124-06](https://doi.org/10.61091/um124-06). URL: <https://arxiv.org/abs/2303.13017v1>.

*Commentary.*

Concatenation of digit blocks closes Out under addition. If n < b^L, the multiple n(b^L−1) has digit sum (b−1)L. Two adjacent lengths show that the gcd of Out is Nat.gcd (b−1) n. The numerical semigroup theorem then puts every sufficiently large positive multiple of this gcd in Out. If the digit sum of n exceeds the gcd, an arithmetic progression gives infinitely many such elements not divisible by that digit sum; if they are equal, none exists. The count of multiples differs from the count of Out in [1,x] by a bounded amount, giving density 1/d.

## References

- Truth anchor: `D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.Out`
- Truth anchor: `D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.claim`
- Truth anchor: `D5/S1/Digit/PhunphayapNoppakaewPongsriiamDigitSumArcs.result`
- Dependency: [D5/S1/Digit/MaxDigitSumBase](MaxDigitSumBase.md)
- Dependency: [D5/S3/Arith/Density/AsymptoticDensity](../../S3/Arith/Density/AsymptoticDensity.md)
- Dependency: [D5/S3/ArithSums/A400361PillaiMean](../../S3/ArithSums/A400361PillaiMean.md)
