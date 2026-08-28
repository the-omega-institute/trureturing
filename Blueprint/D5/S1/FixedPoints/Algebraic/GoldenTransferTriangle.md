# Golden Transfer Triangle

## Abstract

The positive critical radius, the positive first Gauss fixed point, its local multiplier, and the shortest golden geodesic obey the golden transfer triangle.

**Theorem 1.1 (The golden radius links the Gauss branch and shortest geodesic).**

$$\forall r_{*}, x_{*}, \ell_{\varphi} \in \mathbb{R}, (0 < r_{*} \land \left(r_{*}\right)^{2} = r_{*} + 1 \land 0 < x_{*} \land \psi_{1}(x_{*}) = x_{*} \land \ell_{\varphi} = 4 \cdot \log(\varphi)) \Rightarrow ((r_{*} = \varphi \land x_{*} = r_{*} - 1 \land x_{*} = \varphi^{-1} \land \left|\psi_{1}'(x_{*})\right| = \left(r_{*}\right)^{-2}) \land \exp(-\ell_{\varphi}) = \left(r_{*}\right)^{-4}).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle.golden_transfer_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let psi_1(x) = 1/(x+1). The five hypotheses are the adjacent-source characterizations: r_* is positive and satisfies its critical quadratic, x_* is positive and fixed by psi_1, and ell_phi is four times log(phi). These are assumptions about the source objects, not restatements of any conclusion leaf.

The first boxed group has exactly four equality leaves: r_* = phi, x_* = r_* - 1, x_* = phi^(-1), and the absolute derivative equals r_*^(-2). The second boxed group is the fifth leaf, exp(-ell_phi) = r_*^(-4).

The proof imports the repository's positive golden fixed-point uniqueness theorem, uses Mathlib's derivative rule for inversion, and rewrites the sourced length equation with elementary exponential and logarithm identities. It uses no conjectural or Riemann-hypothesis premise.

## References

- Truth anchor: `D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle.golden_transfer_triangle`
- Dependency: [D5/S1/FixedPoints/Algebraic/GoldenFixedPoint](GoldenFixedPoint.md)
