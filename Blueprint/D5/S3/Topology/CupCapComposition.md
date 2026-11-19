# Generator paths and internal components

## Abstract

Generator paths and internal components

For j+1<n, the generator ports are the literal elements (false,Fin.mk j _) and (false,Fin.mk (j+1) hj) of Boundary n. The generator pairs these ports and reconnects their former partners.

**Definition 1.1 (reconnected).**

$$\forall (n: \operatorname{Nat}), (\forall (j: \operatorname{Nat}), (\forall (hj: (j) + (1) < n), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (x: \operatorname{Boundary}\left(n\right)), (\operatorname{reconnected}\left(j, hj, d, x\right) = \operatorname{ite}\left(x = \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right), \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right), \operatorname{ite}\left(x = \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right), \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right), \operatorname{ite}\left(\operatorname{Matching}.\operatorname{mate}\left(d, x\right) = \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right), \operatorname{Matching}.\operatorname{mate}\left(d, \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right)\right), \operatorname{ite}\left(\operatorname{Matching}.\operatorname{mate}\left(d, x\right) = \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right), \operatorname{Matching}.\operatorname{mate}\left(d, \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right)\right), \operatorname{Matching}.\operatorname{mate}\left(d, x\right)\right)\right)\right)\right))))))$$

*Formalization.* `D5/S3/Topology/CupCapComposition.reconnected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four tests are the literal defining conditional, with both boundary ports expanded.

**Theorem 1.2 (composite_cupcap_mate).**

$$\forall (n: \operatorname{Nat}), (\forall (j: \operatorname{Nat}), (\forall (hj: (j) + (1) < n), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), (\forall (x: \operatorname{Boundary}\left(n\right)), (\operatorname{Matching}.\operatorname{mate}\left(\operatorname{composite}\left(\operatorname{cupcapMatching}\left(j, hj\right), d\right), x\right) = \operatorname{reconnected}\left(j, hj, d, x\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.composite_cupcap_mate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reconnected mate is the endpoint reached by the sewn path.

**Theorem 1.3 (internalLoopCount_cupcap_zero).**

$$\forall (n: \operatorname{Nat}), (\forall (j: \operatorname{Nat}), (\forall (hj: (j) + (1) < n), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), ((\operatorname{Matching}.\operatorname{mate}\left(d, \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right)\right) \ne \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right)) \to (\operatorname{internalLoopCount}\left(\operatorname{cupcapMatching}\left(j, hj\right), d\right) = 0)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the inputs are not paired, every component reaches an exposed endpoint.

**Theorem 1.4 (internalLoopCount_cupcap_pos).**

$$\forall (n: \operatorname{Nat}), (\forall (j: \operatorname{Nat}), (\forall (hj: (j) + (1) < n), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), ((\operatorname{Matching}.\operatorname{mate}\left(d, \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right)\right) = \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right)) \to (0 < \operatorname{internalLoopCount}\left(\operatorname{cupcapMatching}\left(j, hj\right), d\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Paired inputs close an internal component.

**Theorem 1.5 (internalLoopCount_cupcap_eq_zero_iff).**

$$\forall (n: \operatorname{Nat}), (\forall (j: \operatorname{Nat}), (\forall (hj: (j) + (1) < n), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)), ((\operatorname{internalLoopCount}\left(\operatorname{cupcapMatching}\left(j, hj\right), d\right) = 0) \Leftrightarrow (\operatorname{Matching}.\operatorname{mate}\left(d, \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left(j, \operatorname{by} \operatorname{omega}\right)\right)\right) \ne \operatorname{Prod}.\operatorname{mk}\left(\operatorname{false}, \operatorname{Fin}.\operatorname{mk}\left((j) + (1), hj\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the exact zero-loop criterion for a generator product.

## References

- Truth anchor: `D5/S3/Topology/CupCapComposition.composite_cupcap_mate`
- Truth anchor: `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_eq_zero_iff`
- Truth anchor: `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_pos`
- Truth anchor: `D5/S3/Topology/CupCapComposition.internalLoopCount_cupcap_zero`
- Truth anchor: `D5/S3/Topology/CupCapComposition.reconnected`
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
