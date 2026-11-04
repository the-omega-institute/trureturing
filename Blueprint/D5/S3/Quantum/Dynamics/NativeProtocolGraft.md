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

These exclusions apply directly to any original-record event formed by the stop-aware graft above. They do not establish that the actual chi preparation and its faithful-support Petz pullback have ideal masses q and w. Quadratic integer coordinates, the whole-tree nonphysical-conjugate estimate and the arithmetic factor-eleven bounds are supplied below. The actual reference-state realization, original-record comparison and total-variation consumers remain separate obligations. Total Born-mass normalization and the equality of the ninth gate power with its inverse are not used or proved here.

**Theorem 1.3 (Computed integer coordinates and the whole-tree signed conjugate bound).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Events}\left(T\right), (((\operatorname{eventMass}\left(T, e\right) = \operatorname{realPhysical}\left(\operatorname{coordinates}\left(T, e\right)\right)) \land (\operatorname{realConjugate}\left(\operatorname{coordinates}\left(T, e\right)\right) = \sum_{p \in \operatorname{Path}\left(T\right)} \sum_{z \in \operatorname{Basis}\left(\right)} \operatorname{if} \operatorname{Apply}\left(e, p, z\right) \operatorname{then} {{-1}}^{\operatorname{exponent}\left(z\right)}*\operatorname{normSq}\left(\operatorname{conjugateAmplitude}\left(\operatorname{branch}\left(T, p, \operatorname{initial}\left(\right)\right), z\right)\right) \operatorname{else} 0)) \land \operatorname{abs}\left(\operatorname{realConjugate}\left(\operatorname{coordinates}\left(T, e\right)\right)\right) \le {\operatorname{kappa}\left(\right)}^{2*\operatorname{maxCalls}\left(T\right)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_coordinates_and_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

For every terminal-label type L, original native tree T and Boolean terminal event e, coordinates(T,e) is an explicitly computed integer pair A,B in the inverse-golden basis. The physical evaluation is A+B t, with t=phi inverse; its other real evaluation is A-B phi. The displayed theorem identifies the first value with the actually computed raw eventMass, identifies the second value with a signed sum over the same terminal paths and basis words, and bounds its absolute value using L(T)=Tree.maxCalls(T) and kappa=1+2 phi cubed.

The coefficient ring O consists of integer pairs with generator tau satisfying tau squared equals one minus tau. S consists of two O coordinates with generator eta satisfying eta squared equals minus one minus tau eta. These are Mathlib quadratic algebras; their multiplication and both evaluation homomorphisms are proved from the displayed equations. At each full basis word z the coefficient vector h represents the actual amplitude as beta to exponent(z) times physical(h(z)). The exponent is zero or one according to the Hamming parity relative to the actual root at shifted positions 0,4,8. A center-bit flip changes that parity.

The forward update is diagStep(j,z) h(z) plus offStep(j,z) tau to (one minus exponent(z)) h(flip(j,z)). Here diagStep is eta times one plus (eta minus one) times the actual diagonal of P; offStep is tau eta (eta minus one) on the 00 neighboring-control block and zero elsewhere. The proof expands the original number projections and bit flip on all sixteen-bit words and all fourteen addresses. Branch transport follows the original chronological operator product, with nine updates for inverse syntax. A report multiplies each coefficient by its original selector indicator, and all report outcomes remain in the tree.

For H=a+b eta, its quadratic norm in S is a squared minus tau a b plus b squared. The event coordinates sum tau to exponent(z) times this norm only on the selected original terminal coordinates. Under the physical evaluation this is exactly the original squared amplitude. Under tau mapped to minus phi, eta mapped to exp(pi i/5), and beta mapped to i sqrt(phi), it equals minus one to exponent(z) times the embedded squared amplitude. This sign is essential: the second evaluation is not a positive Born mass. No field-membership certificate or assumed event law is present.

The embedded active block has squared operator bound phi to the sixth, obtained by two-coordinate Cauchy-Schwarz and reindexing by the same center-bit involution. The remaining control blocks are zero or identity. The gate norm is therefore at most kappa. Induction on the complete tree sums all measurement energies before comparing the child maxima with the original maximum; selector completeness gives exact energy conservation even for non-surjective selectors. This proves a whole-tree bound with no leaf, report or branch-count factor. Zero-mass deep branches and nine-cost calls retain their syntactic resource cost.

This event theorem does not identify an original cut reduction or prove its determinant or spectral lower bounds. It does not construct the actual chi state, Petz comparison, full record-law bridge or Born normalization, and it does not prove that the ninth gate power is the semantic inverse.

**Theorem 1.4 (Positive-event and factor-eleven arithmetic resource bounds).**

$$(\forall L: \operatorname{Type}\left(\right), (\forall T: \operatorname{Tree}\left(L\right), (\forall e: \operatorname{Events}\left(T\right), ((0 < \operatorname{eventMass}\left(T, e\right) \Rightarrow {{\operatorname{kappa}\left(\right)}^{2*\operatorname{maxCalls}\left(T\right)}}^{-1} \le \operatorname{eventMass}\left(T, e\right) \land \frac{1}{11*{{\operatorname{kappa}\left(\right)}^{2*\operatorname{maxCalls}\left(T\right)}+\frac{13+5\sqrt{5}}{22}}} \le \operatorname{abs}\left(\operatorname{eventMass}\left(T, e\right)-\operatorname{emptyTarget}\left(\right)\right)) \land \frac{1}{11*{{\operatorname{kappa}\left(\right)}^{2*\operatorname{maxCalls}\left(T\right)}+\frac{19+9\sqrt{5}}{22}}} \le \operatorname{abs}\left(\operatorname{eventMass}\left(T, e\right)-\operatorname{referenceTarget}\left(\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_resource_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ian Stewart and David Tall (2025). *Algebraic Number Theory and Fermat's Last Theorem*. DOI: [10.1201/9781003462002](https://doi.org/10.1201/9781003462002).

*Commentary.*

The bounds apply to every actually computed eventMass of the same original tree T. K denotes kappa to twice Tree.maxCalls(T). Every positive raw event mass is at least one divided by K. For q=emptyTarget=(13-5 sqrt(5))/22 and w=referenceTarget=(9 sqrt(5)-19)/22, the two displayed discrepancy bounds use exactly the source constants and the same K. These are arithmetic bounds for raw masses, without conditioning or a probability-normalization premise.

For x=A+B tau the integer norm is A squared minus A B minus B squared, and the product of its two real evaluations equals that norm. Its nonvanishing is reused from the existing golden-integer norm theorem through the coordinate correspondence (A-B,B). For u=11q=(4,-5) and u=11w=(-5,9), the norms are 11 and minus 11. Direct expansion proves that the norm of 11x-u is divisible by 11. The existing original_event_arithmetic theorem supplies non-equality with q and w. Thus the nonzero norm has absolute value at least 11. The whole-tree conjugate bound and the triangle inequality give the stated denominators.

The arithmetic inequalities do not identify q or w as the ideal probabilities of the actual chi/Petz experiments. Their empty-prefix and five-call source-history realization, preservation of original records and failure zeros, graft resource identities and total-variation comparison still require the specified original-object consumers. The cut determinant and spectral clauses of V88 theorem 24.1 remain outside this event result.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_arithmetic`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_coordinates_and_bound`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_resource_bounds`
- Truth anchor: `D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_native_projection`
- Dependency: [D5/S3/Arith/Lattices/GoldenIntegerRing](../../Arith/Lattices/GoldenIntegerRing.md)
