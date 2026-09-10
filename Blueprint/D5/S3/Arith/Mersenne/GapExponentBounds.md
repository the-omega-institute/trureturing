# The exponent conjecture of A390871

## Abstract

The binary exponent interval for square differences of Mersenne form.

**Theorem 1.1 (Both exponent bounds).**

$$\forall k,r,m\in\mathbb{N}, (8<k \land (\forall u\in\mathbb{N}, k \neq 2^{u}) \land r<k \land m \le k \land k^{2}+1=r^{2}+2^{m}) \implies \lfloor\log_2 k\rfloor+3 \le m \land m \le 2\lfloor\log_2 k\rfloor+1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Mersenne/GapExponentBounds.mersenne_gap_exponent_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ctibor O. Zizka (2025). *A390871 — square differences of Mersenne form*. URL: <https://oeis.org/A390871>.

*Commentary.*

All variables range over natural numbers. The integer t is the floor of the base-two logarithm of k. The OEIS entry explicitly conjectures this exponent interval. Israel's comments there prove the divisibility observation and a factor construction.

Exponent zero is impossible when r is smaller than k. A difference k minus r of one forces k to be a power of two. A difference of two contradicts parity. Therefore r plus three is at most k. Comparing r squared with k minus three squared gives six times k at most two to the m plus eight.

Write p as two to the t. The integer logarithm gives p at most k and k smaller than twice p. The first inequality and the gap estimate give four times p smaller than two to the m. The second gives k squared plus one smaller than two to the power two t plus two. Strict monotonicity of powers yields both bounds. The proof includes r equal to zero and retains the defining restriction m at most k. The solution k=12, r=9, m=6 attains the lower bound.

## References

- Truth anchor: `D5/S3/Arith/Mersenne/GapExponentBounds.mersenne_gap_exponent_bounds`
