# The OEIS A175406 Greathouse Floor Formula

## Abstract

The OEIS A175406 floor formula is refuted at a large explicit index.

**Definition 1.1 (The greatest admissible exponent).**

$$\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n\right) = \operatorname{sSup}\left(\{k \in \mathrm{Nat} | \left(1 + \frac{1}{(n : \mathrm{Real})}\right)^{k} \le 2\}\right)$$

*Formalization.* `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.a` (`✓ std3`).

*Citation.* Charles R Greathouse IV; Zak Seidov (2012). *OEIS A175406, The greatest integer k such that (1+1/n)^k <= 2*. URL: <https://oeis.org/A175406>.

*Commentary.*

For each natural n, a(n) is the supremum of the natural exponents whose real power of 1 + 1/n is at most 2. The cast (n : R) is the real-number cast used in the Lean definition. In the natural conditionally complete order, sSup of an unbounded set is 0, so this definition is total.

**Definition 1.2 (Greathouse's floor conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; (1 \le n) \Rightarrow (\operatorname{a}\left(n\right) = \lfloor\left((n : \mathrm{Real}) + \frac{1}{2}\right) \cdot Real.log\left(2\right)\rfloor_+))$$

*Formalization.* `D5/S0/Certificates/GreathouseLogTwoFloorRefutation.claim` (`✓ std3`).

*Citation.* Charles R Greathouse IV; Zak Seidov (2012). *OEIS A175406, The greatest integer k such that (1+1/n)^k <= 2*. URL: <https://oeis.org/A175406>.

*Commentary.*

For every natural n with 1 <= n, the conjecture identifies a(n) with the natural floor of (n + 1/2) times Real.log 2. The symbol shown as floor with a subscript plus is Nat.floor.

**Theorem 1.3 (The floor conjecture is false).**

$$\neg claim$$

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
