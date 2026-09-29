# Weighted Labelled Paths

## Abstract

The five-state labelled path ledger is counted by a finite Laurent polynomial, with a scalar recurrence and exact charge-zero coefficient bridges.

**Definition 1.1 (The explicit positive transfer).**

Lean statement: `D5/S3/Combinatorics/Zigzag/WeightedPaths.advance`

*Formalization.* `D5/S3/Combinatorics/Zigzag/WeightedPaths.advance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In state order A,D,E,H,I, the positive transfer rows are [z,z^2,1,0,z^(-1)], [1,z,z^(-1),1,0], [z^(-1),1,0,0,0], [0,z^(-1),0,0,0], and [1,0,0,0,0]. Each nonzero entry comes from its separately indexed labelled transition in PathData, including equal weights at distinct exits. The monomial records integer imbalance at +1, not a geometric path length.

**Theorem 1.2 (The second-order Laurent recurrence).**

$$\forall m \in \mathrm{Nat},\; \operatorname{pathPolynomial}\left(m + 2\right) = 2 \cdot \operatorname{z}\left(1\right) \cdot \operatorname{pathPolynomial}\left(m + 1\right) + 3 \cdot \operatorname{z}\left(-1\right) \cdot \operatorname{pathPolynomial}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/WeightedPaths.pathPolynomial_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With terminal vector (1,z^(-1),0,0,0) and start row (1,z,0,0,0), pathPolynomial has initial values 2 and 4z and satisfies f_(m+2)=2z f_(m+1)+3z^(-1) f_m. The stronger vector recurrence follows by checking the explicit five-state transfer twice and inducting, not by fitting initial counts.

**Theorem 1.3 (Transfer counts actual even paths).**

Lean statement: `D5/S3/Combinatorics/Zigzag/WeightedPaths.actualEvenPathPolynomial_eq_pathPolynomial`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/WeightedPaths.actualEvenPathPolynomial_eq_pathPolynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum of z to the accumulated charge over the finite positive-sector EvenPath type equals the transfer polynomial. The proof decomposes each labelled path into its start, indexed transitions, and terminal; equal transition weights still contribute as separate paths.

**Theorem 1.4 (Odd paths have the singleton shift).**

Lean statement: `D5/S3/Combinatorics/Zigzag/WeightedPaths.actualOddPathPolynomial_eq_shift`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/WeightedPaths.actualOddPathPolynomial_eq_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The odd terminal changes the positive-sector generating polynomial by one monomial shift. It is established by a separate induction over actual OddTail inhabitants and the singleton table, rather than by reusing the antipodal vector unchanged.

**Theorem 1.5 (Odd zero-charge paths are one coefficient).**

Lean statement: `D5/S3/Combinatorics/Zigzag/WeightedPaths.oddPath_zero_charge_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Zigzag/WeightedPaths.oddPath_zero_charge_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extracting the zero-charge coefficient of the sum over actual odd paths yields the required shifted Laurent coefficient. The companion evenPath_zero_charge_card extracts coefficient zero directly. Sector reflection later doubles these positive-sector counts.

## References

- Truth anchor: `D5/S3/Combinatorics/Zigzag/WeightedPaths.actualEvenPathPolynomial_eq_pathPolynomial`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/WeightedPaths.actualOddPathPolynomial_eq_shift`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/WeightedPaths.advance`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/WeightedPaths.oddPath_zero_charge_card`
- Truth anchor: `D5/S3/Combinatorics/Zigzag/WeightedPaths.pathPolynomial_recurrence`
- Dependency: [D5/S3/Combinatorics/Zigzag/PathData](PathData.md)
