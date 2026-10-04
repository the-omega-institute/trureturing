# Necessary persistent controller capacities

## Abstract

Uniformly bounded cumulative communication forces sharp finite embeddings into every actual persistent readout fiber.

**Theorem 1.1 (Fiber, local and joint lower embeddings without finite competitors).**

$$\forall d:\mathbb {N},((2\le d)\implies (\forall A:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall B:\operatorname {Submodule}(\operatorname {ZMod}(2),\operatorname {Source}(d)),(\forall h:\operatorname {IsCompl}(A,B),(((0<\operatorname {finrank}(\operatorname {ZMod}(2),A))\land(0<\operatorname {finrank}(\operatorname {ZMod}(2),B)))\implies (\forall MA:Type_{u},(\forall MB:Type_{v},(\forall Root:Type_{w},(\forall C:\operatorname {Controller}(h,MA,MB,Root),(\forall K:\mathbb {N},((\operatorname {UniformCumulativeBudget}(C,K))\implies ((\forall a:A,(\operatorname {Nonempty}(\operatorname {Embedding}(\operatorname {Fin}(1+2^{\operatorname {finrank}(\operatorname {ZMod}(2),\operatorname {range}(\operatorname {ell}(B)))}),\{m:MA\mid \operatorname {readA}(C,m)=a\}))))\land(\forall b:B,(\operatorname {Nonempty}(\operatorname {Embedding}(\operatorname {Fin}(1+2^{\operatorname {finrank}(\operatorname {ZMod}(2),\operatorname {range}(\operatorname {ell}(A)))}),\{m:MB\mid \operatorname {readB}(C,m)=b\}))))\land(\operatorname {Nonempty}(\operatorname {Embedding}(\operatorname {Fin}((1+2^{\operatorname {finrank}(\operatorname {ZMod}(2),\operatorname {range}(\operatorname {ell}(B)))})\times 2^{\operatorname {finrank}(\operatorname {ZMod}(2),A)}),MA)))\land(\operatorname {Nonempty}(\operatorname {Embedding}(\operatorname {Fin}((1+2^{\operatorname {finrank}(\operatorname {ZMod}(2),\operatorname {range}(\operatorname {ell}(A)))})\times 2^{\operatorname {finrank}(\operatorname {ZMod}(2),B)}),MB)))\land(\operatorname {Nonempty}(\operatorname {Embedding}(\operatorname {Fin}(2^{d+2}),\operatorname {State}(C))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Algorithms/InitializedControllerCapacity.initialized_controller_capacity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix d at least two and a complementary pair A,B of positive dimensions in Source(d). Their control restrictions are ellA,ellB; rank means the dimension of the corresponding linear-map range. All universe levels u,v,w are arbitrary. The compliant controller has arbitrary local and root types. One natural K bounds all initialized finite-word cumulative costs.

The theorem produces an injection of a finite set of size 1+2^rank(ellB) into every left readout fiber and the symmetric injection into every right fiber. It also produces finite injections of the summed fiber capacities into both local carriers and of 2^(d+2) points into the operational joint carrier. No natural cardinality is taken of an infinite competitor.

The already proved maximal-cost supplier gives one actual silent successor region covering every source. A paid rewrite has an internal root at every initialization and a leaf throughout that region, so each silent local state differs from every initial local state. Root agreement gives the same separation on both sides.

When the opposite control restriction is nonzero, a nonzero projected data column exists because the data subspace projects onto the nonzero local summand. Two selected actual silent states with equal local state use the same local leaf update and empty bit string for that rewrite. Their required outputs therefore force their current controls to agree. The proof never splices endpoints from different actual states.

Index the silent representatives in a fixed fiber by the range of the opposite control map and add one separate initial point. Readouts distinguish different fibers. Initial representatives and source-covering silent representatives give two disjoint joint copies of Source(d). Pinned finite vector-space cardinality and finite-set equivalence APIs convert these constructions into the displayed finite domains.

## References

- Truth anchor: `D5/S3/ObserverMemory/Algorithms/InitializedControllerCapacity.initialized_controller_capacity`
- Dependency: [D5/S3/ObserverMemory/Algorithms/SaturatedControlRegion](SaturatedControlRegion.md)
