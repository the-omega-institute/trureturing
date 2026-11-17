# Eldar's antiharmonic adjacency conjecture

## Abstract

Adjacent totative antiharmonic means agree exactly at consecutive Moebius signs one and minus one.

The sums use natural indices and rational means. Positive totatives are taken up to and including the modulus. At modulus one the single totative is one, so its antiharmonic mean is one. For larger moduli, coprimality excludes the upper endpoint.

**Definition 1.1 (Positive totative moments).**

$$\forall j \in \mathrm{Nat},\; \forall n \in \mathrm{Nat},\; \operatorname{totativeMoment}\left(j, n\right) = \sum_{k \in \operatorname{Finset}.\operatorname{Icc}\left(1, n\right)} \operatorname{ite}\left(\operatorname{Nat}.\operatorname{Coprime}\left(k, n\right), k^{j}, 0\right)$$

*Formalization.* `D5/S3/ArithSums/EldarAntiharmonicAdjacency.totativeMoment` (`✓ std3`).

*Citation.* Amiram Eldar; Jaroslav Krizek; OEIS Foundation Inc. (2021). *OEIS A179875: equal adjacent totative antiharmonic means*. URL: <https://oeis.org/A179875>.

*Commentary.*

OEIS A053818, NAME: "a(n) = Sum_{k=1..n, gcd(n,k) = 1} k^2." OEIS A023896, NAME: "Sum of positive integers in smallest positive reduced residue system modulo n. a(1) = 1 by convention." These web entries have no page numbers. The exponent j is natural; j=2 and j=1 give these two sequences. The inclusive sum gives one at n=1 for every j. Petridi, Section 1, page 1, writes the general power sum over the Euler set for moduli greater than one.

**Definition 1.2 (The rational antiharmonic mean).**

$$\forall n \in \mathrm{Nat},\; \operatorname{antiharmonicMean}\left(n\right) = \frac{(\operatorname{totativeMoment}\left(2, n\right): \mathrm{Rat})}{(\operatorname{totativeMoment}\left(1, n\right): \mathrm{Rat})}$$

*Formalization.* `D5/S3/ArithSums/EldarAntiharmonicAdjacency.antiharmonicMean` (`✓ std3`).

*Citation.* Amiram Eldar; Jaroslav Krizek; OEIS Foundation Inc. (2021). *OEIS A179875: equal adjacent totative antiharmonic means*. URL: <https://oeis.org/A179875>.

*Commentary.*

OEIS A179875, COMMENT: "Antiharmonic mean B(h) of numbers k such that gcd(k, h) = 1 for numbers h >= 1 and k < h = A053818(n) / A023896(n) = A175505(h) / A175506(h)." This web entry has no page number. Here n is h, and division takes place in Rat after both natural sums are cast to Rat. The term k=1 makes the first moment positive whenever n is positive.

**Definition 1.3 (The complete adjacency criterion).**

$$\operatorname{claim} = \left(\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((\operatorname{antiharmonicMean}\left(n\right) = \operatorname{antiharmonicMean}\left((n + 1)\right)) \Leftrightarrow ((\operatorname{ArithmeticFunction}.\operatorname{moebius}\left(n\right) = 1) \land (\operatorname{ArithmeticFunction}.\operatorname{moebius}\left((n + 1)\right) = -1)))\right)$$

*Formalization.* `D5/S3/ArithSums/EldarAntiharmonicAdjacency.claim` (`✓ std3`).

*Citation.* Amiram Eldar; Jaroslav Krizek; OEIS Foundation Inc. (2021). *OEIS A179875: equal adjacent totative antiharmonic means*. URL: <https://oeis.org/A179875>.

*Commentary.*

OEIS A179875, COMMENT, revision 13: "Conjecture: also numbers k such that mu(k) = 1 and mu(k+1) = -1, where mu is the Möbius function (tested on the first 10^4 terms)." The NAME is: "Numbers h such that h and h+1 have same antiharmonic mean of the numbers k < h such that gcd(k, h) = 1." This web entry has no page number. The index n is the source's h and the COMMENT's k. ArithmeticFunction.moebius is integer-valued. The assertion quantifies over every n at least one and includes both directions.

**Theorem 1.4 (Equal adjacent means and Moebius signs).**

$$\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow ((\operatorname{antiharmonicMean}\left(n\right) = \operatorname{antiharmonicMean}\left((n + 1)\right)) \Leftrightarrow ((\operatorname{ArithmeticFunction}.\operatorname{moebius}\left(n\right) = 1) \land (\operatorname{ArithmeticFunction}.\operatorname{moebius}\left((n + 1)\right) = -1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithSums/EldarAntiharmonicAdjacency.result` (`✓ std3`). ∎

*Resolves.* `Problems/a179875-antiharmonic-adjacency` (proved) by `D5/S3/ArithSums/EldarAntiharmonicAdjacency.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"a179875-antiharmonic-adjacency","declaration_gid":"D5/S3/ArithSums/EldarAntiharmonicAdjacency.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amiram Eldar; Jaroslav Krizek; OEIS Foundation Inc. (2021). *OEIS A179875: equal adjacent totative antiharmonic means*. URL: <https://oeis.org/A179875>.

*Acknowledgement.* Constantin M. Petridi (2016). *The Sums of the k-powers of the Euler set and their connection with Artin's conjecture for primitive roots*. DOI: [10.48550/arXiv.1612.07632](https://doi.org/10.48550/arXiv.1612.07632). URL: <https://arxiv.org/abs/1612.07632v2>.

*Commentary.*

Möbius inversion expresses each literal totative moment as a divisor sum of ordinary power sums. The classical first and second moments give three times the mean as twice the modulus plus the signed radical divided by the modulus. Its absolute value is at most one. Equality at either endpoint occurs precisely at the corresponding Möbius sign. Equal adjacent means force the two opposite endpoints; the same endpoint identities prove the converse. Direct evaluation includes n=1. The argument makes no assertion about infinitely many equal pairs, integral means, or higher moments.

## References

- Truth anchor: `D5/S3/ArithSums/EldarAntiharmonicAdjacency.antiharmonicMean`
- Truth anchor: `D5/S3/ArithSums/EldarAntiharmonicAdjacency.claim`
- Truth anchor: `D5/S3/ArithSums/EldarAntiharmonicAdjacency.result`
- Truth anchor: `D5/S3/ArithSums/EldarAntiharmonicAdjacency.totativeMoment`
- Dependency: [D5/S3/Weil/Mertens/Cryptids/VonMangoldtCount/Foundation](../Weil/Mertens/Cryptids/VonMangoldtCount/Foundation.md)
