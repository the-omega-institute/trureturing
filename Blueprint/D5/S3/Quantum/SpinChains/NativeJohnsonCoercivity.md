# Counting-average coercivity on native rank spaces

## Abstract

The coefficient-one lowering map on every complex fixed-cardinality space has counting-average coercivity with constant N.

For natural N and r, Rank(N,r) consists of the r-element subsets of Fin(N), and PreviousRank(N,r) consists of subsets T satisfying card(T)+1=r. Layer and PreviousLayer are the corresponding complex Euclidean function spaces, with counting inner products. The predecessor carrier is empty when r=0. No parity assumption, enlargement of N, normalization of counting measure, or restriction to real vectors is imposed.

**Definition 1.1 (The fixed-rank carrier).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\operatorname{Rank}\left(N, r\right) = \{A: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right) \mid \operatorname{card}\left(A\right) = r\}))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.Rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Definition 1.2 (The predecessor carrier).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\operatorname{PreviousRank}\left(N, r\right) = \{A: \operatorname{Finset}\left(\operatorname{Fin}\left(N\right)\right) \mid \operatorname{card}\left(A\right) + 1 = r\}))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.PreviousRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Definition 1.3 (The counting Hilbert space).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\operatorname{Layer}\left(N, r\right) = \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{Rank}\left(N, r\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.Layer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Definition 1.4 (The predecessor counting Hilbert space).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\operatorname{PreviousLayer}\left(N, r\right) = \operatorname{EuclideanSpace}\left(\mathbb{C}, \operatorname{PreviousRank}\left(N, r\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.PreviousLayer` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Definition 1.5 (Coefficient-one lowering).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (f: \operatorname{Layer}\left(N, r\right)), (\forall (T: \operatorname{PreviousRank}\left(N, r\right)), (\operatorname{lower}\left(N, r, f\right)\left(T\right) = \sum_{i \in \operatorname{Fin}\left(N\right)} \operatorname{ite}\left(i \in T, 0, f\left(\operatorname{insert}\left(i, T\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Definition 1.6 (The actual counting average).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\forall (f: \operatorname{Layer}\left(N, r\right)), (\forall (A: \operatorname{Rank}\left(N, r\right)), (\operatorname{average}\left(N, r, f\right)\left(A\right) = \frac{1}{\operatorname{ofNatC}\left(\operatorname{card}\left(\operatorname{Rank}\left(N, r\right)\right)\right)} \cdot \sum_{B \in \operatorname{Rank}\left(N, r\right)} f\left(B\right)))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.average` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Definition 1.7 (The native lowering defect).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), (\operatorname{defect}\left(N, r\right) = \operatorname{ofNatC}\left(r\right) \cdot \left(\operatorname{ofNatC}\left(N\right) - \operatorname{ofNatC}\left(r\right) + 1\right) \cdot \operatorname{id}\left(\operatorname{Layer}\left(N, r\right)\right) - \operatorname{comp}\left(\operatorname{adjoint}\left(\operatorname{lower}\left(N, r\right)\right), \operatorname{lower}\left(N, r\right)\right)))$$

*Formalization.* `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtype proof fields are suppressed in the displayed notation.

**Theorem 1.8 (Coercivity relative to the counting average).**

$$\forall (N: \mathbb{N}), (\forall (r: \mathbb{N}), ((r \le N) \Rightarrow (\forall (f: \operatorname{Layer}\left(N, r\right)), (\operatorname{ofNatR}\left(N\right) \cdot \operatorname{norm}\left(f - \operatorname{average}\left(N, r, f\right)\right)^{2} \le \operatorname{re}\left(\operatorname{innerC}\left(f, \operatorname{defect}\left(N, r, f\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r≤N, card(Rank(N,r))=choose(N,r)>0. The sum of f−average(N,r,f) is zero. Thus average is the orthogonal projection onto the line of constant functions. The defect is r(N−r+1)I−W*W, where W=lower(N,r) and W* is the actual adjoint for the counting inner products. In this scalar coefficient subtraction is in the complex field after casting N and r. The quadratic form equals r(N−r+1)‖f‖²−‖Wf‖².

The BooleanCollectiveLadders rankConfigurationEquiv identifies these subsets with the original N-bit configurations of occupancy r. Extending a function by zero gives E_r; the same construction on occupancy(x)+1=r gives Eminus_r. Reindexing the counting sums proves both maps preserve inner products and norms. The original site_entry formula gives L(N)E_r=Eminus_r W with every coefficient equal to one. The original adjoint_U identity transports the Boolean quadratic form to the native defect.

Repeated rank_split, starting from primitive_zero_eq, constructs f=∑_{t=0}^r U(N)^(r−t)v_t with v_t primitive of rank t. primitive_orthogonal and inner_power_orthogonal make different t components orthogonal. primitive_degree and primitive_endpoint kill components with t>N−r. The original primitive_recurrence gives defect eigenvalue t(N+1−t); for the surviving positive t, its difference from N is (t−1)(N−t)≥0.

Let the vacuum be the all-one bit configuration, the unique configuration of occupancy zero. On a function constant with value c at rank r and zero elsewhere, U has constant value (r+1)c at rank r+1. Induction therefore gives U(N)^r v=r! v(vacuum) on rank r for every primitive rank-zero v. This identifies the zero string with a constant function. Its orthogonality to all remaining strings forces the residual counting sum to vanish, so the zero string is exactly E_r average(N,r,f). Combining this identification with the orthogonal defect estimate proves the displayed inequality.

The conclusion includes odd and even N, both endpoints r=0 and r=N, and the empty-site extension N=0. At r=0 the lowering target is empty and the rank space is one dimensional. At r=N only the constant string survives. No claim about a graph Hamiltonian, tensor spectators, confinement, or physical realization follows without its separate correspondence.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.Layer`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.PreviousLayer`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.PreviousRank`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.Rank`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.average`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.defect`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.lower`
- Truth anchor: `D5/S3/Quantum/SpinChains/NativeJohnsonCoercivity.result`
- Dependency: [D5/S3/Quantum/SpinChains/BooleanCollectiveLadders](BooleanCollectiveLadders.md)
