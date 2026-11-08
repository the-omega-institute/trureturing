# HsfThreeLevelTraceBridge

## Abstract

Complex PSD3 cubic geometry and exact scalar coefficients.

**Definition 1.1 (tauClosed).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.tauClosed`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.tauClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal first closed moment 3sqrt(pq)(p+q)/(2H).

**Definition 1.2 (kappaClosed).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.kappaClosed`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.kappaClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal antisymmetric closed current moment sqrt(pq)(q-p)(p^2+3pq+q^2)/(2H^2).

**Definition 1.3 (psiClosed).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.psiClosed`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.psiClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal closed moment p^2q^2sqrt(pq)(p+q)/H^3.

**Definition 1.4 (betaNumerator).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.betaNumerator`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.betaNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit rational-kernel numerator G, before division by the positive H factors.

**Definition 1.5 (betaClosed).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.betaClosed`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.betaClosed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The literal closed moment sqrt(pq)r^3G/(2H(p,q)H(q,r)^2H(r,p)^2).

**Definition 1.6 (orderedCoefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.orderedCoefficient`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.orderedCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The scalar coefficient 4tau beta-4tau tau psi-(2/27)tau tau tau+3tau kappa kappa. The last plus sign comes from K*=-K.

**Definition 1.7 (rawNumerator).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.rawNumerator`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.rawNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The explicit polynomial 8Q^3 times the actual ordered scalar coefficient, cleared before symmetrization.

**Definition 1.8 (momentMatrix).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.momentMatrix`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.momentMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Entrywise multiplication of the actual source by the indicated real two-level moment kernel.

**Definition 1.9 (jMatrix).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.jMatrix`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.jMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second source-dependent moment with entry sum over k of beta(p_i,p_j;p_k)S_ik S_kj.

**Definition 1.10 (closedMomentTrace).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closedMomentTrace`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closedMomentTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four closed ordered traces 4Tr(XJv)-4Tr(XXPsi)-(2/27)Tr(XXX)-3Tr(XK* K), using the literal closed moment functions.

**Definition 1.11 (orderedCubic).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.orderedCubic`

*Formalization.* `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.orderedCubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full sum over all 27 ordered triples, with the real part of the original three source factors.

**Theorem 1.12 (trace to ordered).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.trace_to_ordered`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.trace_to_ordered` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real level vector and Hermitian complex three by three source, the four finite trace expressions expand into the actual 27 ordered scalar terms. Matrix factors are kept in their original order until scalar coordinates are expanded.

**Theorem 1.13 (ordered to coordinates).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.ordered_to_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.ordered_to_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a Hermitian source, assume all three pure coefficients vanish, each of the two repeated-index sums for edges 01,12,20 equals a,b,c respectively, and each oriented-cycle sum equals k/2. Then the 27-term ordered cubic equals the three weighted pair terms plus k Re(S01 S12 S20).

**Theorem 1.14 (closed trace normal form).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closed_trace_normal_form`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closed_trace_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At all positive levels and for every Hermitian complex three by three source, the four finite closed-moment traces equal the actual rho/Xi coordinate cubic, with both cycle orientations and all repeated-index terms.

**Theorem 1.15 (closed trace nonneg).**

Lean statement: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closed_trace_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closed_trace_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four finite closed-moment traces are nonnegative for every complex PSD three by three source and all positive levels. Equality with the original integrals and the original HSF derivative is a separate unfinished bridge.

The statements concern the explicitly defined closed algebraic kernels. The commutant equality classification, identification with the original integrals, dominated differentiation and original HSF derivative/source bridge remain outside these results. No assertion about arbitrary matrix dimension or literature novelty follows.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.betaClosed`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.betaNumerator`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closedMomentTrace`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closed_trace_nonneg`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.closed_trace_normal_form`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.jMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.kappaClosed`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.momentMatrix`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.orderedCoefficient`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.orderedCubic`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.ordered_to_coordinates`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.psiClosed`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.rawNumerator`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.tauClosed`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfThreeLevelTraceBridge.trace_to_ordered`
- Dependency: [D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding](HsfThreeLevelScalarBinding.md)
