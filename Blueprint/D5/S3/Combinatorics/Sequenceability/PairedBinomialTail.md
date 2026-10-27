# Uniform finite paired binomial tail

## Abstract

Uniform finite paired binomial tail

**Theorem 1.1 (Uniform finite paired binomial tail).**

$$\forall r \in \mathrm{Nat},\; (6 \le r) \Rightarrow (r \cdot \sum_{j\in\mathrm{Icc}\left(2, r - 2\right)}(\mathrm{density}\left(r, j\right)) \le \frac{r \cdot \left(27 \cdot r - 105\right)}{\left(2 \cdot r - 1\right) \cdot \left(2 \cdot r - 3\right) \cdot \left(2 \cdot r - 5\right)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Sequenceability/PairedBinomialTail.paired_tail_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum runs over every integer j from two through r minus two. Density(r,j) is choose(r,j) divided by choose(2r,2j), in the rationals.

Let f(r,j) be binomial(r,j) divided by binomial(2r,2j), with rational division. The exact adjacent-index ratio is (2j+1)/(2r-2j-1), and complementation gives f(r,r-j)=f(r,j). Hence the sequence decreases toward the middle.

For r at least six, the tail from j=2 through r-2 has two endpoint terms f(r,2) and exactly r-5 middle terms bounded by f(r,3). The endpoint values are 3/((2r-1)(2r-3)) and 15/((2r-1)(2r-3)(2r-5)). This yields the explicit residual mass r(27r-105)/((2r-1)(2r-3)(2r-5)), uniformly in r.

## References

- Truth anchor: `D5/S3/Combinatorics/Sequenceability/PairedBinomialTail.paired_tail_bound`
