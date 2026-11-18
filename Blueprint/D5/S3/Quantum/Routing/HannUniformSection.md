# Uniform original-leaf endpoints

## Abstract

The real probability section of the original signed Hann records has uniform laws at both endpoints and a nonempty zero-sum subset whenever zero is feasible.

**Definition 1.1 (The original real probability section).**

Lean statement: `D5/S3/Quantum/Routing/HannUniformSection.Section`

*Formalization.* `D5/S3/Quantum/Routing/HannUniformSection.Section` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix a natural height n, one heterogeneous assignment q on Router n in [-1/2,1], and one qutrit bus. Section n q bus consists of the real z for which there is p:Address n to Real with p(a)>=0, sum p=1, and synthesis(p)=z vacuumRecord. Address 0 is Unit and Address(n+1)=Bool times Address n, so there are exactly 2^n original leaves. The synthesis is the sum of p(a) record(n,q,bus,a) using the actual HannSignedCertificate record and vacuumRecord, with real scalars cast to Complex. In the formulas, ofRealCoefficients denotes this pointwise cast. Probability is assigned only to these original leaves.

**Definition 1.2 (The real local clauses).**

Lean statement: `D5/S3/Quantum/Routing/HannUniformSection.RealLocal`

*Formalization.* `D5/S3/Quantum/Routing/HannUniformSection.RealLocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At q=1 the root scalar is the sum of the two child scalars. At q=-1/2 both child scalars are minus the root scalar. At every other q all three vanish. These are exactly the real restrictions of HannExactForest.Local.

**Definition 1.3 (Exact real coordinates of the original matrix).**

Lean statement: `D5/S3/Quantum/Routing/HannUniformSection.RealEquations`

*Formalization.* `D5/S3/Quantum/Routing/HannUniformSection.RealEquations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At height zero equate the distinct node and original-leaf coordinates. At each successor impose RealLocal and recurse with the same q restricted by restrict n q b. Casting every real coordinate to Complex gives exactly HannExactForest.Equations. Its existing kernel_iff_equations identifies these clauses with the literal matrix kernel. The existing relation_iff_matrix_kernel then gives both directions of the original loaded-record relation. Taking real parts of a complex lift produces a real lift because every matrix coefficient is real. No rows, columns, addresses, root equations or mass variables are added.

**Theorem 1.4 (Binary leaves and signed unit nodes).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \forall x \in \operatorname{Address}\left(n\right) \to Real,\; \forall c \in \operatorname{Node}\left(n\right) \to Real,\; \left(\left(\left(\forall a \in \operatorname{Address}\left(n\right),\; 0 \le x\left(a\right)\right) \land x \ne 0\right) \land \operatorname{mulVec}\left(\operatorname{matrix}\left(n, q\right), \operatorname{SumElim}\left(x, c\right)\right) = 0\right) \Rightarrow \left(\exists u \in \operatorname{Address}\left(n\right) \to Real,\; \exists d \in \operatorname{Node}\left(n\right) \to Real,\; \left(\left(\left(\left(\left(\operatorname{mulVec}\left(\operatorname{matrix}\left(n, q\right), \operatorname{SumElim}\left(u, d\right)\right) = 0 \land u \ne 0\right) \land \left(\forall a \in \operatorname{Address}\left(n\right),\; u\left(a\right) = 0 \lor u\left(a\right) = 1\right)\right) \land \left(\forall a \in \operatorname{Address}\left(n\right),\; u\left(a\right) \ne 0 \Rightarrow 0 < x\left(a\right)\right)\right) \land \left(\forall v \in \operatorname{Node}\left(n\right),\; d\left(v\right) = 0 \lor \left(d\left(v\right) = \operatorname{neg}\left(1\right) \lor d\left(v\right) = 1\right)\right)\right) \land \left(\forall v \in \operatorname{Node}\left(n\right),\; d\left(v\right) \ne 0 \Rightarrow \operatorname{sign}\left(d\left(v\right)\right) = \operatorname{sign}\left(c\left(v\right)\right)\right)\right) \land \operatorname{sign}\left(d\left(\operatorname{root}\left(n\right)\right)\right) = \operatorname{sign}\left(c\left(\operatorname{root}\left(n\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannUniformSection.binary_conformal_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any real q, a kernel vector with nonnegative nonzero original leaves contains a nonzero binary-leaf kernel certificate. A selected leaf had strictly positive original mass. Its node entries are zero or signed units with the original signs; the root has exactly the original root sign. The recursive construction rounds the root to its sign. At an upper router with nonzero root, one child with the required sign suffices. With zero root, the rounded child signs cancel. At a lower router, both child signs equal the negative root sign. At an interior router all local roots vanish. Combining the literal child coordinates preserves all original clauses. If all leaves vanished, induction would force every node to vanish; hence a selected nonzero root also ensures nonempty leaves.

**Definition 1.5 (Nonempty original-leaf sums).**

Lean statement: `D5/S3/Quantum/Routing/HannUniformSection.UniformCertificate`

*Formalization.* `D5/S3/Quantum/Routing/HannUniformSection.UniformCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

UniformCertificate n q bus S e means that S is a nonempty finite subset of Address n, e is -1, 0 or 1, and the sum of the original records over S is e vacuumRecord. Dividing by card S gives a probability law uniform on S and the feasible scalar e/card S.

**Definition 1.6 (Uniform endpoint values).**

Lean statement: `D5/S3/Quantum/Routing/HannUniformSection.UniformEndpoint`

*Formalization.* `D5/S3/Quantum/Routing/HannUniformSection.UniformEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

UniformEndpoint n q bus z provides such an S and e with z=e/card S and 1<=card S<=2^n. Different endpoints may use different subsets and signs.

**Theorem 1.7 (Zero-sum subset in the given positive support).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \forall bus \in Qutrit,\; \left(\forall v \in \operatorname{Router}\left(n\right),\; \operatorname{neg}\left(\frac{1}{2}\right) \le q\left(v\right) \land q\left(v\right) \le 1\right) \Rightarrow \left(\forall p \in \operatorname{Address}\left(n\right) \to Real,\; \left(\left(\left(\forall a \in \operatorname{Address}\left(n\right),\; 0 \le p\left(a\right)\right) \land \sum_{a\in \operatorname{Address}\left(n\right)}{p\left(a\right)} = 1\right) \land \operatorname{synthesis}\left(n, q, bus\right)\left(\operatorname{ofRealCoefficients}\left(p\right)\right) = 0\right) \Rightarrow \left(\exists S \in \operatorname{Finset}\left(\operatorname{Address}\left(n\right)\right),\; \left(\operatorname{Nonempty}\left(S\right) \land \left(\forall a \in S,\; 0 < p\left(a\right)\right)\right) \land \sum_{a\in S}{\operatorname{record}\left(n, q, bus, a\right)} = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannUniformSection.zero_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Lift the given nonnegative normalized p through the original matrix theorem. The real root is zero, so the binary certificate also has zero root. Its leaves equal one on a nonempty subset S and zero elsewhere. The exact matrix bridge therefore gives sum over S of record(a)=0. Every selected leaf belongs to the positive support of the given p. The argument does not require zero to be an endpoint of the section.

**Theorem 1.8 (The complete closed interval and both uniform endpoints).**

$$\forall n \in Nat,\; \forall q \in \operatorname{Router}\left(n\right) \to Real,\; \forall bus \in Qutrit,\; \left(\forall v \in \operatorname{Router}\left(n\right),\; \operatorname{neg}\left(\frac{1}{2}\right) \le q\left(v\right) \land q\left(v\right) \le 1\right) \Rightarrow \left(\left(\operatorname{Section}\left(n, q, bus\right) = emptyset \lor \left(\exists l \in Real,\; \exists r \in Real,\; \left(\left(l \le r \land \operatorname{Section}\left(n, q, bus\right) = \operatorname{Icc}\left(l, r\right)\right) \land \operatorname{UniformEndpoint}\left(n, q, bus, l\right)\right) \land \operatorname{UniformEndpoint}\left(n, q, bus, r\right)\right)\right) \land \left(\operatorname{mem}\left(0, \operatorname{Section}\left(n, q, bus\right)\right) \Rightarrow \left(\exists S \in \operatorname{Finset}\left(\operatorname{Address}\left(n\right)\right),\; \operatorname{Nonempty}\left(S\right) \land \sum_{a\in S}{\operatorname{record}\left(n, q, bus, a\right)} = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Routing/HannUniformSection.uniform_section` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing signConformalGlobalKernelCircuitDecomposition to the same real original matrix, reindexing only its rows by Fin(card Row). Every summand is conformal to the given probability lift, so its leaves are nonnegative. A nonzero summand has a nonzero leaf. Apply binary rounding to that circuit. The rounded vector has support contained in the circuit. Subtract the original value at a selected leaf times the rounded vector. The difference remains in the kernel, stays inside the circuit support, and vanishes at that leaf. Support minimality forces the difference to be zero. Thus every circuit is a positive scalar times a binary certificate. After normalization, its contribution has weight t card S and value e/card S. The weights sum to one, and their weighted values sum to z. Consequently the section lies in the convex hull of its uniform values. Conversely every uniform value is feasible and the section is convex. There are finitely many subsets and three possible numerators. If any value is feasible, the least and greatest uniform values are feasible, bound the whole section, and convexity fills their closed interval. This treats both signs and both endpoints together, including a singleton.

The small-height boundaries distinguish emptiness, a singleton and two different endpoint values. At height zero the section is {1}. At height one, a strictly interior root rate gives the empty section, while rate -1/2 gives {-1/2}. At rate 1, the unequal leaf probabilities 2/3 and 1/3 are feasible. For a larger example, let q3 have height three, root rate 1, all left-subtree rates -1/2 and all right-subtree rates 1. Its nonnegative kernel coordinates satisfy mass/4 <= root <= mass, with the bounds attained by four equal left leaves and by one right leaf. Form q4 by placing rate -1/2 above two identical copies of q3, and q5 by placing rate -1/2 above two copies of q4. Their sections for the wait bus are exactly [-1/2,-1/8] and [1/16,1/4], respectively. Duplicating a normalized leaf law with half its mass in each copy sends its root value z to -z/2. Conversely the lower-router equations equate both child roots to minus the parent root; the two child mass bounds give the displayed parent bounds. Convexity fills the intervals between the attained endpoints.

The conformal-decomposition method is classical; the elementary-vector source is Mueller and Regensburger, Elementary vectors and conformal sums in polyhedral geometry and their relevance for metabolic pathway analysis, Section 3.1, Lemma 2 and Theorem 3. The binary rounding and its application here concern the stated signed Hann model. No claim about physical signed channels, hardware, complexity, ontology or originality follows. A feasible probability law need not itself be uniform.

## References

- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.RealEquations`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.RealLocal`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.Section`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.UniformCertificate`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.UniformEndpoint`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.binary_conformal_kernel`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.uniform_section`
- Truth anchor: `D5/S3/Quantum/Routing/HannUniformSection.zero_certificate`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/NonnegativeKernelCircuit](../Entanglement/AbsolutePPT/NonnegativeKernelCircuit.md)
- Dependency: [D5/S3/Quantum/Routing/HannExactForest](HannExactForest.md)
