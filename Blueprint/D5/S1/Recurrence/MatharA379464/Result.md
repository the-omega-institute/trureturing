# The A379464 recurrence

## Abstract

The literal OEIS A379464 path count satisfies the eight-term recurrence.

The source states: “Conjecture D-finite with recurrence +3*(n+4)*(3*n+4)*(3*n+8)*a(n) +3*(-63*n^3-297*n^2-349*n-60)*a(n-1) +3*(189*n^3+270*n^2-229*n-140)*a(n-2) +15*(-63*n^3+117*n^2+44*n-64)*a(n-3) +(689*n^3-5372*n^2+6946*n-1288)*a(n-4) +(n-4)*(201*n^2+2767*n-3011)*a(n-5) -(n-5)*(579*n+257)*(n-4)*a(n-6) +229*(n-5)*(n-6)*(n-4)*a(n-7)=0.” OEIS A379464, revision 20, unnumbered FORMULA line. The displayed proposition keeps integer polynomial arithmetic and natural sequence subtraction.

**Definition 1.1 (The Euler operator).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{E}\left(f\right) = \operatorname{PowerSeries}.\operatorname{X}\left(\right) \cdot \left(1 - \operatorname{PowerSeries}.\operatorname{X}\left(\right)\right) \cdot \operatorname{derivative}\left(f\right) - \operatorname{PowerSeries}.\operatorname{X}\left(\right) \cdot f$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.E` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.2 (The differential operator).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{L}\left(f\right) = \left(1 - \operatorname{PowerSeries}.\operatorname{X}\left(\right)\right)^{4} \cdot \left(\operatorname{PowerSeries}.\operatorname{C}\left(27\right) \cdot \operatorname{E}\left(\operatorname{E}\left(\operatorname{E}\left(f\right)\right)\right) + \operatorname{PowerSeries}.\operatorname{C}\left(216\right) \cdot \operatorname{E}\left(\operatorname{E}\left(f\right)\right) + \operatorname{PowerSeries}.\operatorname{C}\left(528\right) \cdot \operatorname{E}\left(f\right) + \operatorname{PowerSeries}.\operatorname{C}\left(384\right) \cdot f\right) - \operatorname{PowerSeries}.\operatorname{C}\left(256\right) \cdot \operatorname{PowerSeries}.\operatorname{X}\left(\right)^{4} \cdot \left(\operatorname{E}\left(\operatorname{E}\left(\operatorname{E}\left(f\right)\right)\right) + \operatorname{PowerSeries}.\operatorname{C}\left(14\right) \cdot \operatorname{E}\left(\operatorname{E}\left(f\right)\right) + \operatorname{PowerSeries}.\operatorname{C}\left(63\right) \cdot \operatorname{E}\left(f\right) + \operatorname{PowerSeries}.\operatorname{C}\left(90\right) \cdot f\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.3 (The rational coefficient recurrence).**

$$\forall v \in \mathbb{N} \to \mathbb{Q},\; \forall n \in \mathbb{N},\; \operatorname{recurrence}\left(v, n\right) = 3 \cdot \left((n:\mathbb{Q}) + 4\right) \cdot \left(3 \cdot (n:\mathbb{Q}) + 4\right) \cdot \left(3 \cdot (n:\mathbb{Q}) + 8\right) \cdot \operatorname{v}\left(n\right) + 3 \cdot \left(-63 \cdot (n:\mathbb{Q})^{3} - 297 \cdot (n:\mathbb{Q})^{2} - 349 \cdot (n:\mathbb{Q}) - 60\right) \cdot \operatorname{v}\left(n - 1\right) + 3 \cdot \left(189 \cdot (n:\mathbb{Q})^{3} + 270 \cdot (n:\mathbb{Q})^{2} - 229 \cdot (n:\mathbb{Q}) - 140\right) \cdot \operatorname{v}\left(n - 2\right) + 15 \cdot \left(-63 \cdot (n:\mathbb{Q})^{3} + 117 \cdot (n:\mathbb{Q})^{2} + 44 \cdot (n:\mathbb{Q}) - 64\right) \cdot \operatorname{v}\left(n - 3\right) + \left(689 \cdot (n:\mathbb{Q})^{3} - 5372 \cdot (n:\mathbb{Q})^{2} + 6946 \cdot (n:\mathbb{Q}) - 1288\right) \cdot \operatorname{v}\left(n - 4\right) + \left((n:\mathbb{Q}) - 4\right) \cdot \left(201 \cdot (n:\mathbb{Q})^{2} + 2767 \cdot (n:\mathbb{Q}) - 3011\right) \cdot \operatorname{v}\left(n - 5\right) - \left((n:\mathbb{Q}) - 5\right) \cdot \left(579 \cdot (n:\mathbb{Q}) + 257\right) \cdot \left((n:\mathbb{Q}) - 4\right) \cdot \operatorname{v}\left(n - 6\right) + 229 \cdot \left((n:\mathbb{Q}) - 5\right) \cdot \left((n:\mathbb{Q}) - 6\right) \cdot \left((n:\mathbb{Q}) - 4\right) \cdot \operatorname{v}\left(n - 7\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.recurrence` (`✓ std3`).

*Citation.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.4 (The geometric series).**

$$\operatorname{geom}\left(\right) = \operatorname{PowerSeries}.\operatorname{mk}\left((1:\mathbb{N} \to \mathbb{Q})\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.geom` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.5 (The substitution parameter).**

$$\operatorname{param}\left(\right) = \left(\operatorname{PowerSeries}.\operatorname{X}\left(\right) \cdot \operatorname{geom}\left(\right)\right)^{4}$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.param` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.6 (The binomial transform).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \operatorname{transform}\left(f\right) = \operatorname{geom}\left(\right) \cdot \operatorname{PowerSeries}.\operatorname{subst}\left(\operatorname{param}\left(\right), f\right)$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.transform` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.7 (The factorial sequence).**

$$\forall k \in \mathbb{N},\; \operatorname{b}\left(k\right) = \frac{3 \cdot (\operatorname{Nat}.\operatorname{factorial}\left(4 \cdot k + 2\right):\mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right):\mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot k + 3\right):\mathbb{Q})}$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.b` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Theorem 1.8 (Coefficient extraction).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall n \in \mathbb{N},\; (7 \le n) \Rightarrow (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, \operatorname{L}\left(f\right)\right) = \operatorname{recurrence}\left((i: \mathbb{N} \mapsto \operatorname{PowerSeries}.\operatorname{coeff}\left(i, f\right)), n\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA379464/Result.coeff_L` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Theorem 1.9 (Vanishing of the forcing term).**

$$\forall n \in \mathbb{N},\; (7 \le n) \Rightarrow (\operatorname{PowerSeries}.\operatorname{coeff}\left(n, \operatorname{PowerSeries}.\operatorname{C}\left(384\right) \cdot \left(1 - \operatorname{PowerSeries}.\operatorname{X}\left(\right)\right)^{3}\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA379464/Result.forcing_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Theorem 1.10 (The transform coefficients).**

$$\forall f \in \operatorname{PowerSeries}\left(\mathbb{Q}\right),\; \forall n \in \mathbb{N},\; \operatorname{PowerSeries}.\operatorname{coeff}\left(n, \operatorname{transform}\left(f\right)\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\operatorname{Nat}.\operatorname{choose}\left(n, 4 \cdot k\right):\mathbb{Q}) \cdot \operatorname{PowerSeries}.\operatorname{coeff}\left(k, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA379464/Result.transform_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Theorem 1.11 (The explicit series certificate).**

$$\operatorname{L}\left(\operatorname{transform}\left(\operatorname{PowerSeries}.\operatorname{mk}\left(\operatorname{b}\left(\right)\right)\right)\right) = \operatorname{PowerSeries}.\operatorname{C}\left(384\right) \cdot \left(1 - \operatorname{PowerSeries}.\operatorname{X}\left(\right)\right)^{3}$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA379464/Result.explicit_series_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The formal-series expression uses rational coefficients and the displayed differential operators.

**Definition 1.12 (The source recurrence claim).**

$$\forall n \in \mathbb{N},\; (7 \le n) \Rightarrow (3 \cdot \left((n:\mathbb{Z}) + 4\right) \cdot \left(3 \cdot (n:\mathbb{Z}) + 4\right) \cdot \left(3 \cdot (n:\mathbb{Z}) + 8\right) \cdot \operatorname{a}\left(n\right) + 3 \cdot \left(-63 \cdot (n:\mathbb{Z})^{3} - 297 \cdot (n:\mathbb{Z})^{2} - 349 \cdot (n:\mathbb{Z}) - 60\right) \cdot \operatorname{a}\left(n - 1\right) + 3 \cdot \left(189 \cdot (n:\mathbb{Z})^{3} + 270 \cdot (n:\mathbb{Z})^{2} - 229 \cdot (n:\mathbb{Z}) - 140\right) \cdot \operatorname{a}\left(n - 2\right) + 15 \cdot \left(-63 \cdot (n:\mathbb{Z})^{3} + 117 \cdot (n:\mathbb{Z})^{2} + 44 \cdot (n:\mathbb{Z}) - 64\right) \cdot \operatorname{a}\left(n - 3\right) + \left(689 \cdot (n:\mathbb{Z})^{3} - 5372 \cdot (n:\mathbb{Z})^{2} + 6946 \cdot (n:\mathbb{Z}) - 1288\right) \cdot \operatorname{a}\left(n - 4\right) + \left((n:\mathbb{Z}) - 4\right) \cdot \left(201 \cdot (n:\mathbb{Z})^{2} + 2767 \cdot (n:\mathbb{Z}) - 3011\right) \cdot \operatorname{a}\left(n - 5\right) - \left((n:\mathbb{Z}) - 5\right) \cdot \left(579 \cdot (n:\mathbb{Z}) + 257\right) \cdot \left((n:\mathbb{Z}) - 4\right) \cdot \operatorname{a}\left(n - 6\right) + 229 \cdot \left((n:\mathbb{Z}) - 5\right) \cdot \left((n:\mathbb{Z}) - 6\right) \cdot \left((n:\mathbb{Z}) - 4\right) \cdot \operatorname{a}\left(n - 7\right) = 0)$$

*Formalization.* `D5/S1/Recurrence/MatharA379464/Result.claim` (`✓ std3`).

*Citation.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

For every natural n at least 7, the eight displayed coefficient terms sum to zero.

**Theorem 1.13 (The recurrence is proved).**

$$\forall n \in \mathbb{N},\; (7 \le n) \Rightarrow (3 \cdot \left((n:\mathbb{Z}) + 4\right) \cdot \left(3 \cdot (n:\mathbb{Z}) + 4\right) \cdot \left(3 \cdot (n:\mathbb{Z}) + 8\right) \cdot \operatorname{a}\left(n\right) + 3 \cdot \left(-63 \cdot (n:\mathbb{Z})^{3} - 297 \cdot (n:\mathbb{Z})^{2} - 349 \cdot (n:\mathbb{Z}) - 60\right) \cdot \operatorname{a}\left(n - 1\right) + 3 \cdot \left(189 \cdot (n:\mathbb{Z})^{3} + 270 \cdot (n:\mathbb{Z})^{2} - 229 \cdot (n:\mathbb{Z}) - 140\right) \cdot \operatorname{a}\left(n - 2\right) + 15 \cdot \left(-63 \cdot (n:\mathbb{Z})^{3} + 117 \cdot (n:\mathbb{Z})^{2} + 44 \cdot (n:\mathbb{Z}) - 64\right) \cdot \operatorname{a}\left(n - 3\right) + \left(689 \cdot (n:\mathbb{Z})^{3} - 5372 \cdot (n:\mathbb{Z})^{2} + 6946 \cdot (n:\mathbb{Z}) - 1288\right) \cdot \operatorname{a}\left(n - 4\right) + \left((n:\mathbb{Z}) - 4\right) \cdot \left(201 \cdot (n:\mathbb{Z})^{2} + 2767 \cdot (n:\mathbb{Z}) - 3011\right) \cdot \operatorname{a}\left(n - 5\right) - \left((n:\mathbb{Z}) - 5\right) \cdot \left(579 \cdot (n:\mathbb{Z}) + 257\right) \cdot \left((n:\mathbb{Z}) - 4\right) \cdot \operatorname{a}\left(n - 6\right) + 229 \cdot \left((n:\mathbb{Z}) - 5\right) \cdot \left((n:\mathbb{Z}) - 6\right) \cdot \left((n:\mathbb{Z}) - 4\right) \cdot \operatorname{a}\left(n - 7\right) = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MatharA379464/Result.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The path count is converted to a binomial transform of the factorial series. The formal differential certificate has zero coefficients in degrees at least 7, so coefficient extraction gives the displayed recurrence for every such n.

## References

- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.E`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.L`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.b`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.claim`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.coeff_L`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.explicit_series_certificate`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.forcing_zero`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.geom`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.param`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.recurrence`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.result`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.transform`
- Truth anchor: `D5/S1/Recurrence/MatharA379464/Result.transform_coefficients`
- Dependency: [D5/S1/Recurrence/A308815DFiniteRecurrence](../A308815DFiniteRecurrence.md)
- Dependency: [D5/S1/Recurrence/Invariants/HannaDiagonalDerivativeParity](../Invariants/HannaDiagonalDerivativeParity.md)
- Dependency: [D5/S1/Words/LatticePaths/MatharA379464Counting](../../Words/LatticePaths/MatharA379464Counting.md)
