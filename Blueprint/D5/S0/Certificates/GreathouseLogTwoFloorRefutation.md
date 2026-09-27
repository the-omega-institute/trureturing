# The OEIS A175406 Greathouse Floor Formula

## Abstract

The OEIS A175406 floor formula is refuted at a large explicit index.

**Definition 1.1 (The sequence value).**

$$
\begin{gathered}\forall n\in\mathbb{N},\\\ {}a(n)=\mathrm{sSup}\begin{Bmatrix}k\in\mathbb{N}\mid (1+1/n)^{k}\leq2\end{Bmatrix}\end{gathered}
$$

*Formalization.* `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.a` (`✓ std3`).

*Citation.* Charles R Greathouse IV; Zak Seidov (2012). *OEIS A175406, The greatest integer k such that (1+1/n)^k <= 2*. URL: <https://oeis.org/A175406>.

*Commentary.*

For each natural n, including zero, a(n) takes the natural sSup of exponents k satisfying the displayed bound. Powers and division are real, with Lean's 1/0 = 0 convention. Natural sSup is 0 for unbounded sets, so a is total.

**Definition 1.2 (Greathouse's floor conjecture).**

$$
\begin{gathered}\mathrm{claim}\Leftrightarrow\\\ {}\forall n\in\mathbb{N},\ n\geq1\Rightarrow\\\ {}a(n)=\lfloor(n+1/2)\log 2\rfloor_+\end{gathered}
$$

*Formalization.* `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim` (`✓ std3`).

*Citation.* Charles R Greathouse IV; Zak Seidov (2012). *OEIS A175406, The greatest integer k such that (1+1/n)^k <= 2*. URL: <https://oeis.org/A175406>.

*Commentary.*

For every positive natural n, the conjecture identifies a(n) with the displayed natural floor. The subscript plus denotes Nat.floor, and log is the natural logarithm.

**Theorem 1.3 (The floor conjecture is false).**

$$
\neg\mathrm{claim}
$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a175406-log-two-floor-refutation` (refuted) by `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a175406-log-two-floor-refutation","declaration_gid":"D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Charles R Greathouse IV; Zak Seidov (2012). *OEIS A175406, The greatest integer k such that (1+1/n)^k <= 2*. URL: <https://oeis.org/A175406>.

*Commentary.*

At n0 = 1121626023352383, let M = 777451915729368. The certified log-series estimates give the stated natural floor as M, while the defining supremum is M - 1: the M-th power is greater than 2 and the (M - 1)-st power is at most 2. The proof uses 36 positive terms and a geometric tail for log 2, two positive terms for the witness logarithm, and log(1+x) <= x. No minimality claim is made.

## References

- Truth anchor: `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.a`
- Truth anchor: `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim`
- Truth anchor: `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.result`
