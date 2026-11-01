# Quantitative uncrossing of admissible word fibers

## Abstract

Finite Boolean rows can be uncrossed by actual meet-join exchanges. Each exchange keeps the row count and every coordinate margin, raises the rank-square energy, and a bounded forward route reaches comparable support. Alternating complement carries the exchange to the no-adjacent-one admissible-word carrier.

**Theorem 1.1 (A meet-join step preserves every coordinate margin).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_margin`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual multiset is explicit, so repeated rows and empty rows are included. Replacing incomparable A and B by A intersect B and A union B preserves each coordinate's number of occupied rows.

**Theorem 1.2 (A coordinate has full margin exactly when every row contains it).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.margin_eq_card_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.margin_eq_card_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characterization is valid for empty rows, repeated rows, and the empty multiset; it is the coordinate-level description of the minimum row.

**Theorem 1.3 (Comparable row multisets are uniquely determined by mass and margins).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.comparable_margin_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.comparable_margin_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction removes a minimum row, identified by the full-margin coordinates, and reconstructs the multiset from its residual.

**Theorem 1.4 (An incomparable exchange raises rank-square energy).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_strict`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_strict` (`✓ std3`). ∎

*Citation.* Takayuki Hibi (1987). *Distributive Lattices, Affine Semigroup Rings and Algebras with Straightening Laws*. DOI: [10.2969/aspm/01110093](https://doi.org/10.2969/aspm/01110093). URL: <https://doi.org/10.2969/aspm/01110093>.

*Commentary.*

If a and b are the two nonempty exclusive parts of the selected rows, the energy increment is 2ab, hence at least two. This is the monotone potential used for the forward route bound.

**Theorem 1.5 (An incomparable exchange raises energy by at least two).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_gap`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both exclusive parts are nonempty, so the exact rank-square increment is at least two. This is the quantitative induction step.

**Theorem 1.6 (Every finite row multiset has a bounded forward route).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.exists_forward_route_to_comparable`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.exists_forward_route_to_comparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The route is built by strong induction on the remaining rank-square energy. It has at most floor(m times |V| squared divided by two) forward steps and ends at pairwise comparable support.

**Theorem 1.7 (Alternating complement sends admissible words to fence rows).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_support_fence`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_support_fence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-based alternating complement leaves even coordinates and complements odd coordinates. The no-adjacent-one condition becomes the alternating fence inequalities, and intersections and unions remain legal.

**Theorem 1.8 (Alternating complement is an involution).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_involutive`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the parity-dependent complement twice restores every Boolean word, so the transformed support carrier has no information loss.

**Theorem 1.9 (Phi supports faithfully distinguish words).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.support_phi_injective`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.support_phi_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support of the alternating complement determines the transformed word, and involutivity then recovers the original admissible-word input.

**Theorem 1.10 (The admissible carrier inherits the bounded route).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_route_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_route_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual multiset of admissible words, the transformed supports remain in the finite fence family throughout the constructed route. The same explicit bound and comparable endpoint therefore hold on the native carrier.

**Theorem 1.11 (The comparable endpoint is canonical inside the actual Phi fiber).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_canonical_endpoint_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_canonical_endpoint_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two comparable endpoints reached by forward routes from the same admissible-word multiset have the same mass and coordinate margins, so the generic uniqueness theorem identifies them.

**Theorem 1.12 (The native admissible-word consumer realizes a four-corner exchange).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_forward_consumer`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_forward_consumer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two actual admissible words with incomparable transformed supports instantiate the generic residual exchange. In dimension three this includes the 100 plus 001 exchange with its 000 and 101 meet-join endpoints.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_canonical_endpoint_unique`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_forward_consumer`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_route_bound`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.comparable_margin_unique`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.exists_forward_route_to_comparable`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_gap`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_strict`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_margin`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.margin_eq_card_iff`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_involutive`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_support_fence`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.support_phi_injective`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
