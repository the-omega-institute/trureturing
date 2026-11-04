# Native protocol composition and original-record projection

## Abstract

Stop-aware composition of the original sixteen-bit native protocols.

**Theorem 1.1 (Every original path retains its matrix, archive and resource semantics).**

$$(\forall T: \operatorname{Tree}\left(\operatorname{Cut}\left(\right)\right), (\forall C: \operatorname{Continuations}\left(T\right), (\forall pi: \operatorname{Nat}\left(\right), (\forall e: \operatorname{RecordEvent}\left(T\right), ((((\operatorname{projectedMass}\left(T, C, pi, e\right) = \sum_{p \in \operatorname{Path}\left(T\right)} \sum_{q \in \operatorname{Path}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right)\right)} \sum_{z \in \operatorname{Basis}\left(\right)} \operatorname{if} \operatorname{Apply}\left(e, \operatorname{Record}\left(pi, p, \operatorname{readTag}\left(\operatorname{label}\left(T, p\right), \operatorname{Apply}\left(C, p\right), q\right), \operatorname{label}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right), q\right)\right), z\right) \operatorname{then} \operatorname{normSq}\left(\operatorname{Apply}\left(\operatorname{mulVec}\left(\operatorname{MatMul}\left(\operatorname{Op}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right), q\right), \operatorname{Op}\left(T, p\right)\right), \operatorname{omegaZero}\left(\right)\right), z\right)\right) \operatorname{else} 0) \land (\operatorname{L}\left(\operatorname{graft}\left(T, \operatorname{extension}\left(T, C\right)\right)\right) = \operatorname{sup}_{p \in \operatorname{Path}\left(T\right)} (\operatorname{c}\left(T, p\right) + \operatorname{L}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right)\right)))) \land (\forall p: \operatorname{Path}\left(T\right), \operatorname{CutLaw}\left(\operatorname{label}\left(T, p\right), \operatorname{Apply}\left(C, p\right)\right))) \land (\forall p: \operatorname{Path}\left(T\right), (\forall q: \operatorname{Path}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right)\right), ((((\operatorname{Op}\left(\operatorname{graft}\left(T, \operatorname{extension}\left(T, C\right)\right), \operatorname{attach}\left(T, \operatorname{extension}\left(T, C\right), p, q\right)\right) = \operatorname{MatMul}\left(\operatorname{Op}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right), q\right), \operatorname{Op}\left(T, p\right)\right)) \land (\operatorname{Ar}\left(\operatorname{graft}\left(T, \operatorname{extension}\left(T, C\right)\right), \operatorname{attach}\left(T, \operatorname{extension}\left(T, C\right), p, q\right)\right) = \operatorname{Append}\left(\operatorname{Ar}\left(T, p\right), \operatorname{Ar}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right), q\right)\right))) \land (\operatorname{c}\left(\operatorname{graft}\left(T, \operatorname{extension}\left(T, C\right)\right), \operatorname{attach}\left(T, \operatorname{extension}\left(T, C\right), p, q\right)\right) = (\operatorname{c}\left(T, p\right) + \operatorname{c}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right), q\right)))) \land (\operatorname{label}\left(\operatorname{graft}\left(T, \operatorname{extension}\left(T, C\right)\right), \operatorname{attach}\left(T, \operatorname{extension}\left(T, C\right), p, q\right)\right) = \operatorname{label}\left(\operatorname{Apply}\left(\operatorname{extension}\left(T, C\right), p\right), q\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_native_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giulio Chiribella; Giacomo M. D'Ariano; Paolo Perinotti (2009). *Theoretical framework for quantum networks*. DOI: [10.1103/PhysRevA.80.022339](https://doi.org/10.1103/PhysRevA.80.022339). URL: <https://arxiv.org/abs/0904.4483v2>.

*Commentary.*

The carrier Basis is the set of all functions from Fin 16 to Bool, with shifted sites 0 through 15 representing the original sites -1 through 14. All operators are full matrices on these 65536 basis words. The root Omega is the computational word with ones at shifted positions 0, 4 and 8. No factorization of the 2584-dimensional legal subspace is used.

The menu is that of V88 definitions 23.1, 23.2 and 28.1. It uses the actual fourteen golden matrices K at addresses 0 through 13: Q is t times the zero-number projection plus t squared times the number projection plus beta cubed times bit flip; P is the product of neighboring number projections plus the product of their complements times Q; K is zeta times identity plus zeta times (zeta minus one) times P. Here phi=(1+sqrt(5))/2, t=phi inverse, beta=sqrt(t), and zeta=exp(3 pi i/5). An inverse call is interpreted as nine forward calls and costs nine. A forward call costs one.

A finite native tree has gate nodes, finite complete diagonal measurement nodes and labeled leaves. A measurement is specified by a function from Basis to Fin n: outcome o has the diagonal projector whose entries are one exactly on the fiber of o. Surjectivity is unnecessary, so zero projectors and their full successor trees remain. Feedback can depend on the whole acquired path. Leaf labels distinguish active cuts from absorbed stops; each stop has its failure, refusal, early or normal kind and its own identifying code.

For prefix T, Continuations(T) means the full function type Path(T) to Fin 2 to Tree(Stop). RecordEvent(T) means all Boolean predicates on the tuple of a natural program identifier, an original Path(T), an optional Fin 2 read and a Stop, together with a terminal Basis word. For such a continuation table C, E(p) denotes extension(T,C,p). At an active leaf E first reads original bit b1, at shifted index 2, and then executes C(p,j). At an absorbed leaf E is the single original stopped leaf: its operator is identity, its archive is empty, its added cost is zero and its read tag is none. CutLaw states these two cases, including each active read tag, diagonal projector, archive entry and terminal stop label.

G is graft(T,E). Each G path has a unique split into the original path p and an added path q of E(p), with inverse attach(T,E,p,q). The original-record projection keeps the original program pi, the full original path p, the optional original read j, the final stop and every terminal basis word z. Original path identities are retained even when two paths have equal labels or zero mass. Only the added path q is summed out. The event e is any Boolean predicate on this retained record and z.

Op denotes the chronological branch matrix; Ar is the complete gate-and-report archive; c is the expanded forward-call cost; L is its maximum over every syntactic terminal path. Mass uses normSq of Op applied to the same fixed Omega. The first equality is a raw finite Born-mass pushforward. It does not divide by success probability or erase records physically. The second equality includes every zero, failing and stopped path; it allows different continuation costs at different original leaves.

The path bijection and matrix factorization follow by induction through every original gate and measurement node. Reindexing the complete terminal sum by that bijection gives the event equality. The same induction concatenates archives and adds expanded costs. Taking the maximum over the finite, nonempty continuation fibers gives the exact whole-tree resource equality.

This composition theorem does not establish total Born-mass normalization, arithmetic integrality or nonphysical-conjugate estimates for the actual native gates. It does not construct a Petz compiler, compute the actual chi reference, or prove either numerical obstruction or resource lower bound. Those conclusions require their respective native arithmetic and reference-state bridges. No protection of the complement of b1, auxiliary preparation, reset, new controlled operation or postselection is assumed.

**Theorem 1.2 (Integral raw event masses exclude both reference-comparison values).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Events}\left(T\right), ((\operatorname{IsIntegral}\left(\operatorname{Int}\left(\right), \operatorname{eventMass}\left(T, e\right)\right) \land \operatorname{eventMass}\left(T, e\right) \ne \frac{13-5\sqrt{5}}{22}) \land \operatorname{eventMass}\left(T, e\right) \ne \frac{9\sqrt{5}-19}{22}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_arithmetic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

For every type L of terminal labels, every finite full-menu native tree T and every Boolean event e on its complete terminal path and terminal sixteen-bit word, the raw mass p=eventMass(T,e) is an algebraic integer over the ordinary integers. All fourteen actual gate addresses, deterministic feedback, complete diagonal zero-one measurements, zero outcomes, stops and expanded inverse calls are included. The input is the same fixed computational root Omega; no arbitrary input vector or external probability weights occur.

The scalars t, beta and zeta of the actual matrices are algebraic integers: rational-angle exponential and cosine integrality give zeta and t, and beta squared equals t. Every number projection and bit flip has integer entries. Finite matrix addition, multiplication and powers therefore preserve entrywise integrality. Induction through the actual tree gives integral branch-matrix entries. Applying the fixed root, multiplying each amplitude by its physical complex conjugate and summing the selected raw events preserve integrality. The real event mass is reflected from its injective complex embedding. No success normalization is performed.

Set q=(13-5 sqrt(5))/22 and w=(9 sqrt(5)-19)/22. In the existing quadratic golden field with generator phi, these are the images of coordinate pairs (9/11,-5/11) and (-14/11,9/11). Their field norms are respectively 1/11 and -1/11. Integrality would force an integer field norm; both rational values fail that condition. Consequently p differs from both q and w. This argument only needs absolute algebraic integrality of p and does not assert that p lies in the quadratic field.

These exclusions apply directly to any original-record event formed by the stop-aware graft above. They do not establish that the actual chi preparation and its faithful-support Petz pullback have ideal masses q and w. That realization bridge, the quadratic-field membership of general native events, the whole-tree nonphysical-conjugate estimate and the factor-eleven resource and total-variation bounds require further results. Total Born-mass normalization and the equality of the ninth gate power with its inverse are not used or proved here.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_arithmetic`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_native_projection`
- Dependency: [D5/S3/Arith/Lattices/GoldenIntegerRing](../../Arith/Lattices/GoldenIntegerRing.md)
