# The Cassini and Leg Identities of the Bronze Ladder

## Abstract

The bronze ladder obeys a Cassini determinant law and lies on the Pell conic 13x^2 - y^2 = pm 4.

**Theorem 1.1 (The leg identity of the bronze ladder).**

$$p_0=1, p_1=3, p_{n+2}=3p_{n+1}+p_n,\\p_n p_{n+2}-p_{n+1}^2=(-1)^n,\\13p_{n+1}^2-(3p_{n+1}+2p_n)^2=4(-1)^{n+1}$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/BronzeLadderLeg.bronze_leg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bronze ladder p is the integer sequence p 0 = 1, p 1 = 3, p (n+2) = 3 p(n+1) + p n, whose k-th term is the top-left entry of the k-th power of the crossing matrix [[3,1],[1,0]] of trace 3 and determinant -1 — the square-root-of-13 analogue of the Fibonacci and Pell ladders.

Two identities hold for every n. The Cassini identity p n * p(n+2) - p(n+1)^2 = (-1)^n has right side (det T)^n = (-1)^n for the crossing matrix of determinant -1 (the left side is det of T^(n+2)); it is proved by induction. The leg identity evaluates the indefinite binary form 13 x^2 - y^2 at the ladder point (x,y) = (p(n+1), 3 p(n+1) + 2 p n) and returns 4 (-1)^(n+1), so every ladder point lies on the Pell conic 13 x^2 - y^2 = +-4; that value is minus four times the Cassini value (-1)^n, hence a one-line consequence of it.

Only the ladder's arithmetic core — the Cassini determinant law and this leg identity — is recorded here. The geometric crossing (1,2,3^k) = M T^k, the spectral four-accumulation limit of the crossing angles, and the wider narrative clauses of the source are not covered by these statements.

## References

- Truth anchor: `D5/S3/PrimeForms/BronzeLadderLeg.bronze_leg`
