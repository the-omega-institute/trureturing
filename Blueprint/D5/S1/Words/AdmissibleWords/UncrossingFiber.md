# Quantitative uncrossing and native admissible occupancy fibers

## Abstract

Actual finite Boolean row multisets admit bounded meet-join sorting to a unique explicit threshold multiset. Reversing and concatenating normalization routes connects each margin fiber. Alternating complement and its inverse transport complete paths to the native admissible-word occupancy fibers. The qualitative straightening and its potential are classical. Straightening is attributed to Hibi (1987); the fence poset context is attributed to Stanley, Two Poset Polytopes (1986).

**Theorem 1.1 (Each residual exchange preserves coordinate counts).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_margin`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The input consists of two positive occurrences A and B and an explicit residual multiset. Replacing them by their intersection and union preserves every coordinate count, including multiplicities.

**Theorem 1.2 (Full margin identifies coordinates present in every row).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.margin_eq_card_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.margin_eq_card_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This characterization includes zero mass, repeated rows and empty rows and identifies the minimum row of a comparable multiset.

**Theorem 1.3 (Mass and margins uniquely determine comparable multisets).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.comparable_margin_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.comparable_margin_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction removes a minimum row, identified by the full-margin coordinates, and reconstructs the residual multiset. No inhabitedness assumption is imposed on the vertex type.

**Theorem 1.4 (The exact rank-square energy increment).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy` (`✓ std3`). ∎

*Citation.* Takayuki Hibi (1987). *Distributive Lattices, Affine Semigroup Rings and Algebras with Straightening Laws*. DOI: [10.2969/aspm/01110093](https://doi.org/10.2969/aspm/01110093). URL: <https://doi.org/10.2969/aspm/01110093>.

*Commentary.*

Writing the two exclusive parts as A minus B and B minus A, the energy increment is twice the product of their cardinalities. This is a classical distributive-lattice straightening potential, with no novelty claim.

**Theorem 1.5 (Every incomparable exchange gains at least two units of energy).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_gap`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both exclusive parts are nonempty. The exact identity therefore supplies the quantitative decrease of the remaining energy budget.

**Theorem 1.6 (Construct an actual forward route with the initial energy charged).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.exists_forward_route_to_comparable`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.exists_forward_route_to_comparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strong induction on energy slack constructs k residual exchanges to comparable support and proves 2k plus the input energy is at most m times the square of the number of vertices. The floor bound k at most floor(m times the square of the number of vertices divided by two) follows.

**Theorem 1.7 (The sorting endpoint is the explicit threshold multiset).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.sort_to_threshold`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.sort_to_threshold` (`✓ std3`). ∎

*Citation.* Takayuki Hibi (1987). *Distributive Lattices, Affine Semigroup Rings and Algebras with Straightening Laws*. DOI: [10.2969/aspm/01110093](https://doi.org/10.2969/aspm/01110093). URL: <https://doi.org/10.2969/aspm/01110093>.

*Commentary.*

For an actual input M of mass m and counts c(v), row j indexed by Fin m contains v exactly when m minus c(v) is at most j.val. The multiset retains all m rows, including repeated and empty rows. Its mass and counts agree with M, its support is comparable, and uniqueness identifies it with the constructed sorting endpoint. The bound retains the initial energy; no novelty claim is made for this classical normal form or quantitative estimate.

**Theorem 1.8 (An actual sorting route proves threshold-row feasibility).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.thresholdRows_family`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.thresholdRows_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Binary closure under intersection and union suffices. The route places each threshold row in the original family; arbitrary independently specified margins are not assumed feasible. Empty families, empty vertex types and zero mass remain in scope.

**Theorem 1.9 (Equal-margin configurations normalize to one comparable endpoint).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.same_margin_common_comparable`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.same_margin_common_comparable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two bounded forward routes are constructed separately and their endpoints are identified by comparable-margin uniqueness.

**Theorem 1.10 (Reverse and concatenate the actual residual-exchange paths).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.same_margin_connected`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.same_margin_connected` (`✓ std3`). ∎

*Citation.* Takayuki Hibi (1987). *Distributive Lattices, Affine Semigroup Rings and Algebras with Straightening Laws*. DOI: [10.2969/aspm/01110093](https://doi.org/10.2969/aspm/01110093). URL: <https://doi.org/10.2969/aspm/01110093>.

*Commentary.*

ExchangePath uses Mathlib ReflTransGen on residual exchanges with legal family endpoints. The proof converts each constructed normalization route to such a path, reverses the second, and concatenates. The monotone budget applies to forward sorting routes only; it is not asserted for arbitrary undirected paths.

**Theorem 1.11 (All reachable intermediate row states stay in the same fiber).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.exchangePath_invariants`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.exchangePath_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every path prefix preserves family membership, mass and each coordinate count. Forward and reverse steps both retain the same explicit residual exchange semantics.

**Theorem 1.12 (Native admissibility is equivalent to the fence inequalities).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_support_fence_iff`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_support_fence_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-based alternating complement leaves even coordinates unchanged and complements odd coordinates. AdmissibleCount.adm_iff_no_adjacent_true supplies the shared adjacency characterization of the native recursive Adm n predicate. This is equivalent to the alternating fence upper-set inequalities on transformed supports, for every n including zero.

**Definition 1.13 (Every fence row has a legal inverse native word).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.admFenceEquiv`

*Formalization.* `D5/S1/Words/AdmissibleWords/UncrossingFiber.admFenceEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse unphi takes a row characteristic function and applies alternating complement. Both inverse equations hold on the full Boolean carriers. Restricting gives a bijection between actual Adm n words and fence rows, so arbitrary intermediate fence rows also decode legally. Original admissible supports are not asserted union-closed.

**Theorem 1.14 (Transformed counts follow from original occupancies).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phiRows_margin`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.phiRows_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The occupancyCount is the multiset sum of original Boolean occupied coordinates. Phi counts equal c(i) on even coordinates and m minus c(i) on odd coordinates, with repetitions counted. Thus equality of original mass and occupancies implies equality of transformed margins.

**Theorem 1.15 (Pull every residual lattice move back to native word configurations).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_forward_consumer`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_forward_consumer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A fence-family forward step decodes to NativeForwardStep: two actual word occurrences a and b are replaced by unphi of the intersection and union of their transformed supports, with exactly the same residual word multiset. The resulting words satisfy native Adm n.

**Theorem 1.16 (Native paths preserve legality and original occupancy counts).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.nativePath_invariants`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.nativePath_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativePath is Mathlib ReflTransGen of the symmetric closure of actual native residual exchanges. Every reachable state is admissible and has the original mass and each original occupancy count; this holds for every prefix and both step directions.

**Theorem 1.17 (Construct the complete canonical native sorting endpoint).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_route_bound`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_route_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward route reaches the threshold multiset after Phi and satisfies the initial-energy and floor bounds. Its complete pullback is a NativePath to nativeCanonical M. Every threshold row decodes to Adm n, re-encoding the endpoint recovers exactly the threshold multiset, and any comparable forward endpoint equals it. Canonical comparability is asserted after Phi.

**Theorem 1.18 (Equal original occupancy fibers are connected on the all-n native carrier).**

Lean statement: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_fiber_common_endpoint`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_fiber_common_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary multisets of native Adm n words with equal original mass and occupancyCount at every coordinate, the theorem constructs a genuine undirected NativePath, proves equality of their canonical endpoints after Phi, exposes a bounded forward normalization and its native pullback, and proves legality and original-fiber invariants at every reachable intermediate state. The n equals three exchange 100 plus 001 with 000 plus 101 is a concrete instance of the native move; it does not restrict the theorem scope.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.admFenceEquiv`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_fiber_common_endpoint`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_forward_consumer`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.adm_phi_route_bound`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.comparable_margin_unique`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.exchangePath_invariants`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.exists_forward_route_to_comparable`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_energy_gap`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.forwardStep_margin`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.margin_eq_card_iff`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.nativePath_invariants`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phiRows_margin`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.phi_support_fence_iff`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.same_margin_common_comparable`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.same_margin_connected`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.sort_to_threshold`
- Truth anchor: `D5/S1/Words/AdmissibleWords/UncrossingFiber.thresholdRows_family`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
