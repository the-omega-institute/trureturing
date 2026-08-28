# Golden Transfer Triangle

## Abstract

The maximal real disk, the Mayer operator, its first fixed branch, and the shortest modular geodesic select the golden transfer triangle without caller premises.

**Theorem 1.1 (The maximal disk and Mayer operator select the golden triangle).**

$$\exists r_{*}, x_{*}, \ell_{\varphi} \in \mathbb{R}, \operatorname{IsLUB}(\{r \mid 1 \le r \land r < 2 \land 1 / (2 - r) < 1 + r\}, r_{*}) \land r_{*} = \varphi \land x_{*} = r_{*} - 1 \land x_{*} = \varphi^{-1} \land \psi_{1}(x_{*}) = x_{*} \land \left|\psi_{1}'(x_{*})\right| = \left(r_{*}\right)^{-2} \land \operatorname{IsLeast}(\operatorname{L}_{\operatorname{PSL}_2(\mathbb{Z})}, \ell_{\varphi}) \land \exp(-\ell_{\varphi}) = \left(r_{*}\right)^{-4} \land (\forall w \in \mathbb{N}, f: \mathbb{R} \to \mathbb{R}, x \in \mathbb{R}, \operatorname{M}_{w}(f)(x) = \sum_{n \ge 1} \psi_{n}(x)^{2w} f(\psi_{n}(x))).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle.golden_transfer_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are no public premises. The proof chooses r_*, x_*, and ell_phi from concrete source carriers: the sharp real disk IsLUB, the first branch of the full Mayer operator, and the least positive PSL_2(Z) hyperbolic-trace length.

The modular length carrier consists of positive ell for which 2 cosh(ell/2) is an integer trace at least three. Its least member is 4 log(phi), and exp(-ell_phi) = r_*^(-4).

For every natural weight, the Mayer operator is exactly the sum over psi_n(x) = 1/(x+n), n >= 1. Its defining formula contains no golden parameter; phi is selected by maximality and the fixed branch. The proof uses no conjectural premise.

## References

- Truth anchor: `D5/S1/FixedPoints/Algebraic/GoldenTransferTriangle.golden_transfer_triangle`
- Dependency: [D5/S1/FixedPoints/Algebraic/GoldenFixedPoint](GoldenFixedPoint.md)
