# The Second Semi-Meander Diagonal

## Abstract

Connected semi-meanders with n crossings and winding n minus four have the second-diagonal count for every n at least four.

**Definition 1.1 (Noncrossing upper arches).**

$$U_{n} = \{M \in \operatorname{Fin}\left(2 \cdot n\right) \to \operatorname{Fin}\left(2 \cdot n\right) \mid \left(\forall x \in \operatorname{Fin}\left(2 \cdot n\right),\; M\left(M\left(x\right)\right) = x \land M\left(x\right) \ne x\right) \land \left(\forall a \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall b \in \operatorname{Fin}\left(2 \cdot n\right),\; \neg \left(a < b \land \left(b < M\left(a\right) \land M\left(a\right) < M\left(b\right)\right)\right)\right)\}$$

*Formalization.* `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Model.UpperMatching` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Hunter Hogan (2026). *OEIS A400429, semi-meanders by crossings and winding number*. URL: <https://oeis.org/A400429>.

*Commentary.*

Endpoints are numbered from zero to 2n minus one. An upper matching is a fixed-point-free involution M: each endpoint has one distinct partner, and no two upper arches have alternating endpoints a < b < M(a) < M(b). The fixed lower matching is the rainbow r(x) = 2n - 1 - x.

**Remark 1.2 (Midpoint winding).**

$$
L_{n}: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(2 \cdot n\right), \forall x \in \operatorname{Fin}\left(n\right),\; \operatorname{val}\left(\left(L_{n}\right)\left(x\right)\right) = \operatorname{val}\left(x\right), \operatorname{winding}\left(M\right) = \left|\{x \in \operatorname{Fin}\left(n\right) \mid n \le \operatorname{val}\left(M\left(\left(L_{n}\right)\left(x\right)\right)\right)\}\right|
$$

*Source.* Repository-derived.

*Acknowledgement.* Hunter Hogan (2026). *OEIS A400429, semi-meanders by crossings and winding number*. URL: <https://oeis.org/A400429>.

*Commentary.*

L_n embeds Fin n into Fin(2n) without changing the endpoint value. The winding counts left-half endpoints whose upper partner lies in the right half. Each upper arch crossing the midpoint contributes exactly once.

**Remark 1.3 (One loop with the lower rainbow).**

$$
\forall u \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall v \in \operatorname{Fin}\left(2 \cdot n\right),\; \left(R_{M}\right)\left(u, v\right) \Leftrightarrow \left(M\left(u\right) = v \lor 2 \cdot n - 1 - \operatorname{val}\left(u\right) = \operatorname{val}\left(v\right)\right),  \operatorname{oneLoop}\left(M\right) \Leftrightarrow \left(\forall x \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall y \in \operatorname{Fin}\left(2 \cdot n\right),\; \operatorname{RTC}\left(R_{M}, x, y\right)\right)
$$

*Source.* Repository-derived.

*Acknowledgement.* Hunter Hogan (2026). *OEIS A400429, semi-meanders by crossings and winding number*. URL: <https://oeis.org/A400429>.

*Commentary.*

The step relation R_M joins x to y when either M(x) = y or r(x) = y, with r(x) = 2n - 1 - x. Its reflexive transitive closure connects every ordered pair of endpoints exactly when the union of upper arches and the fixed lower rainbow is one loop.

**Theorem 1.4 (Exact second-diagonal count).**

$$\forall n \in \mathrm{Nat},\; 4 \le n \Rightarrow \left|\{M \in U_{n} \mid \operatorname{winding}\left(M\right) = n - 4 \land \operatorname{oneLoop}\left(M\right)\}\right| = \frac{n^{2} + 2 \cdot n + n \bmod 2 - 20}{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SemiMeanderSecondDiagonal.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a400429-semi-meander-second-diagonal` (proved) by `D5/S3/Combinatorics/SemiMeanderSecondDiagonal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a400429-semi-meander-second-diagonal","declaration_gid":"D5/S3/Combinatorics/SemiMeanderSecondDiagonal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Hunter Hogan (2026). *OEIS A400429, semi-meanders by crossings and winding number*. URL: <https://oeis.org/A400429>.

*Commentary.*

For every n at least four, count exactly the noncrossing upper matchings whose midpoint winding is n minus four and whose union with the lower rainbow is one loop. The second diagonal of OEIS A400429 is this set: its source index k = floor(n/2) - 1 gives winding n - 4. At n = 4 the count is two. Di Francesco, Golinelli and Guitter predicted this same polynomial from the resummation in Appendix D (1996); the count here is an independent exact proof for the stated model and full range.

## References

- Truth anchor: `D5/S3/Combinatorics/SemiMeanderSecondDiagonal.result`
- Truth anchor: `D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Model.UpperMatching`
- Dependency: [D5/S3/Combinatorics/SemiMeanderSecondDiagonal/Stage5](SemiMeanderSecondDiagonal/Stage5.md)
