# Signed loaded-record coefficients

## Abstract

The prescribed signed recursion gives unique complex coefficient certificates for actual loaded Hann router records at every height.

**Definition 1.1 (Specified Fourier coordinates).**

Lean statement: `D5/S3/Quantum/Routing/HannSignedCertificate.localRecord`

*Formalization.* `D5/S3/Quantum/Routing/HannSignedCertificate.localRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set omega=exp(2 pi i/3) and labelIndex(wait)=0, labelIndex(zero)=1, labelIndex(one)=2. localRecord(q,s) has coordinates sqrt((1+2q)/3), sqrt((1-q)/3) omega^labelIndex(s), sqrt((1-q)/3) omega^(-labelIndex(s)). All square roots are the nonnegative real roots. The rate interval is the entire closed interval from minus one half to one. The entries need not be real.

**Definition 1.2 (Literal actual loading and common restrictions).**

Lean statement: `D5/S3/Quantum/Routing/HannSignedCertificate.record`

*Formalization.* `D5/S3/Quantum/Routing/HannSignedCertificate.record` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Router n is the existing internal-router index. Environment n is Router n to Fin 3, and Address n retains the existing head-first binary order. record n q bus a e is the product of localRecord(q(v),loadedLabel n a bus v,e(v)) over all routers. loadedLabel is the literal router after the existing actual load. The existing loaded_label and vacuum_label supply the programming bridge. Every external qutrit bus is allowed. restrict n q b sends v to q(some(b,v)); thus every recursive input is a restriction of the same arbitrary heterogeneous assignment. No distinct rates are identified. The environment order is root, left child, right child.

**Definition 1.3 (Nonzero vacuum tensor).**

Lean statement: `D5/S3/Quantum/Routing/HannSignedCertificate.vacuumRecord`

*Formalization.* `D5/S3/Quantum/Routing/HannSignedCertificate.vacuumRecord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

vacuumRecord n q is the product of the wait local records. It is nonzero throughout the rate interval: at a lower-endpoint coordinate use Fourier coordinate one, and elsewhere use coordinate zero. This supplies the nonzero factors used in the common-scalar tensor argument. At depth zero both record and vacuumRecord are one.

**Definition 1.4 (Complex coefficient synthesis).**

Lean statement: `D5/S3/Quantum/Routing/HannSignedCertificate.synthesis`

*Formalization.* `D5/S3/Quantum/Routing/HannSignedCertificate.synthesis` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coeff n is Address n to Complex. synthesis n q bus maps x to the environment function whose value is the sum of x(a) record(n,q,bus,a,e). embed n b is literal zero extension along the first address bit b. The coefficient theorem concerns this map, not an operator-space or Schur-superoperator kernel.

**Definition 1.5 (The prescribed ordered recursion).**

Lean statement: `D5/S3/Quantum/Routing/HannSignedCertificate.outputs`

*Formalization.* `D5/S3/Quantum/Routing/HannSignedCertificate.outputs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Output n contains dimension d, an ordered kernel list K, and an optional representative U. Its Boolean flag t is U.isSome. At depth zero, d=1, K is empty, and U is the constant-one coefficient. At a successor start K with J0(K0) followed by J1(K1), preserving both orders. For root rate less than one, d=d0+d1. At rate one, subtract one exactly when both child flags are true, and append exactly J0(u0)-J1(u1) only in that case. At minus one half, t=t0 and t1 and, when true, U=Some(-J0(u0)-J1(u1)). In the open interval t is false and U=None. At one, t=t0 or t1 and U prefers Some(J0(u0)) whenever the left flag is true; only when it is false and the right flag true use Some(J1(u1)). Otherwise U=None. No basis selection, elimination, rescaling, deduplication or optimization changes this list.

**Definition 1.6 (The two Gram orientations).**

Lean statement: `D5/S3/Quantum/Routing/HannSignedCertificate.standardGram`

*Formalization.* `D5/S3/Quantum/Routing/HannSignedCertificate.standardGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

recordMatrix has environment rows and address columns and entry record n q bus a e. standardGram is its conjugate transpose times itself. densityGram(a,b) instead sums record(a,e) conjugate(record(b,e)). Local conjugate-first overlap is one for equal labels and q(v) otherwise. The product over actual loaded labels is real, so the two Gram orientations coincide. This uses real overlaps, without assuming that the Fourier entries themselves are real.

**Theorem 1.7 (Complete signed coefficient and Gram certificate).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \left(\forall v \in \operatorname{Router}\left(n\right),\; \operatorname{neg}\left(\frac{1}{2}\right) \le q\left(v\right) \land q\left(v\right) \le 1\right) \Rightarrow \left(\forall bus \in Qutrit,\; \left(\left(\left(\left(\left(\left(\left(\operatorname{finrank}\left(Complex, \operatorname{range}\left(\operatorname{synthesis}\left(n, q, bus\right)\right)\right) = \operatorname{dimension}\left(\operatorname{outputs}\left(n, q\right)\right) \land \operatorname{length}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right)\right) = 2^{n} - \operatorname{dimension}\left(\operatorname{outputs}\left(n, q\right)\right)\right) \land \left(\operatorname{mem}\left(\operatorname{vacuumRecord}\left(n, q\right), \operatorname{range}\left(\operatorname{synthesis}\left(n, q, bus\right)\right)\right) \Leftrightarrow \operatorname{flag}\left(\operatorname{outputs}\left(n, q\right)\right) = true\right)\right) \land \left(\forall u \in \operatorname{Address}\left(n\right) \to Complex,\; \operatorname{representative}\left(\operatorname{outputs}\left(n, q\right)\right) = \operatorname{some}\left(u\right) \Rightarrow \operatorname{synthesis}\left(n, q, bus\right)\left(u\right) = \operatorname{vacuumRecord}\left(n, q\right)\right)\right) \land \left(\forall x \in \operatorname{Address}\left(n\right) \to Complex,\; \operatorname{synthesis}\left(n, q, bus\right)\left(x\right) = 0 \Leftrightarrow \left(\exists alpha \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right)\right)\right) \to Complex,\; x = \sum_{i\in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right)\right)\right)}{\operatorname{smul}\left(alpha\left(i\right), \operatorname{get}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right), i\right)\right)} \land \left(\forall beta \in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right)\right)\right) \to Complex,\; x = \sum_{i\in \operatorname{Fin}\left(\operatorname{length}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right)\right)\right)}{\operatorname{smul}\left(beta\left(i\right), \operatorname{get}\left(\operatorname{kernel}\left(\operatorname{outputs}\left(n, q\right)\right), i\right)\right)} \Rightarrow beta = alpha\right)\right)\right)\right) \land \left(\forall a \in \operatorname{Address}\left(n\right),\; \forall b \in \operatorname{Address}\left(n\right),\; \operatorname{standardGram}\left(n, q, bus\right)\left(a, b\right) = \operatorname{ofReal}\left(\prod_{v\in \operatorname{Router}\left(n\right)}{\operatorname{ite}\left(\operatorname{loadedLabel}\left(n, a, bus, v\right) = \operatorname{loadedLabel}\left(n, b, bus, v\right), 1, q\left(v\right)\right)}\right)\right)\right) \land \operatorname{densityGram}\left(n, q, bus\right) = \operatorname{standardGram}\left(n, q, bus\right)\right) \land \operatorname{ker}\left(\operatorname{mulVecLin}\left(\operatorname{densityGram}\left(n, q, bus\right)\right)\right) = \operatorname{ker}\left(\operatorname{synthesis}\left(n, q, bus\right)\right)\right) \land \operatorname{rank}\left(\operatorname{densityGram}\left(n, q, bus\right)\right) = \operatorname{dimension}\left(\operatorname{outputs}\left(n, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannSignedCertificate.signed_event` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement quantifies over every natural height, every rate assignment in the closed signed interval, every external bus, and every complex coefficient vector. Apply it to restrict at any prefix to obtain all subtree clauses for the original common assignment. The lower endpoint uses the negative sum representative. Below the upper endpoint the local equation forces both child scalars to be the negative vacuum scalar, and in the interior that scalar vanishes. At the upper endpoint the nonzero child vacua force one common scalar. Subtracting the prescribed collision removes it and leaves the two child kernels. Applying child synthesis separates that collision from inherited kernel vectors. This proves completeness and independence of the literal ordered list together with vacuum membership and the prescribed representative equations. Pinned Mathlib finite-dimensional rank-nullity and independent-family span results then give the count and unique coefficients. Its Gram rank and kernel interfaces consume the proved real product bridge. The result is repository-derived; generic tensor intersection or generic basis existence is not claimed as new content. It makes no noisy-continuation, Choi-rank, computability or bit-complexity claim.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.localRecord`
- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.outputs`
- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.record`
- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.signed_event`
- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.standardGram`
- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.synthesis`
- Truth anchor: `D5/S3/Quantum/Routing/HannSignedCertificate.vacuumRecord`
- Dependency: [D5/S3/Quantum/Routing/HannRouterProfiles](HannRouterProfiles.md)
