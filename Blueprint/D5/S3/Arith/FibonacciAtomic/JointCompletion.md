# Joint Source Completion

## Abstract

Finite legal Fibonacci sources complete to the product of legal infinite addresses and two profinite integer coordinates.

Omega is the space of infinite Boolean addresses without adjacent ones. The profinite integers are the existing compatible residue families over all positive moduli, and K is Omega times two copies of that space. D consists of the eventually zero legal addresses. X(L) is the existing space of legal words of length L. The index m denotes the positive modulus m+1, so every positive modulus and the empty prefix are included.

**Definition 1.1 (Finite joint observations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/JointCompletion.jointObservation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/JointCompletion.jointObservation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q(k)(L,m) consists of the low prefix P(L,omega) and both residue coordinates of z modulo m+1, for k=(omega,z) in K.

**Definition 1.2 (Actual finite-source graph).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/JointCompletion.sourceGraph`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/JointCompletion.sourceGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gamma(b) pairs the actual address b with the two profinite residue families of its existing Fibonacci sourceComposition. Its range is the graph Gamma; the two coordinates come from the same finite source.

**Definition 1.3 (Bonding conditions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/JointCompletion.compatibleObservations`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/JointCompletion.compatibleObservations` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A joint reading family q is compatible when increasing the prefix length and replacing a modulus by a multiple preserves every lower bit and reduces each residue to the corresponding lower-modulus reading. These are precisely the prefix-truncation and modular-reduction bonding maps.

**Definition 1.4 (Finite-observation uniform structure).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/JointCompletion.sourceUniformity`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/JointCompletion.sourceUniformity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source uniform structure is the infimum of the pullbacks of the finite joint observation spaces. Thus agreement means simultaneous equality of a finite low prefix and the two modular Fibonacci-composition coordinates.

**Theorem 1.5 (Joint compact completion).**

$$(\forall i \in N^{2}, \operatorname{Surjective}\left(\operatorname{Qgamma}\left(i\right)\right)) \land ((\operatorname{UniformEmbedding}\left(Q\right)) \land (\forall q, \operatorname{Compatible}\left(q\right) \iff \exists! k \in K, \operatorname{Q}\left(k\right) = q)) \land ((\operatorname{DenseRange}\left(gamma\right)) \land (\forall k \in K, \exists s: N \to D, (\forall n, \operatorname{Q}\left(\operatorname{gamma}\left(\operatorname{s}\left(n\right)\right), \operatorname{i}\left(n\right)\right) = \operatorname{Q}\left(k, \operatorname{i}\left(n\right)\right)) \land (\operatorname{gamma}\left(\operatorname{s}\left(n\right)\right) \to k))) \land ((\operatorname{Compact}\left(K\right)) \land (\operatorname{UniformEmbedding}\left(gamma\right)) \land (\operatorname{AbstractCompletionOn}\left(K, D, UD, gamma\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/JointCompletion.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Q_gamma(i) sends a source b to Q(gamma(b))(i). The pair i(n) is (n,(n+1)!-1), whose second index represents the modulus (n+1)!. The convergence arrow is convergence as n tends to infinity. All uniform embeddings use the product and subspace uniform structures, with each finite residue space discrete and the source structure U_D given by sourceUniformity. The observation embedding uses the underlying bit-function encoding of each legal finite word in its ambient Boolean word space; the actual image clause has codomain X(L) times the residue pair. AbstractCompletionOn denotes the existence of a mathlib AbstractCompletion of (D,U_D) with underlying space K, the stated product uniform structure, and inclusion gamma.

The joint observation map is a uniform embedding into the product of finite reading spaces. Its image is exactly the compatible reading families: the j-th bit is recovered from a prefix of length j+1, and each residue is recovered from the empty-prefix reading. Compatibility makes these recovered bits legal and makes both residue families profinite integers. This identifies K with the inverse limit in the product subspace topology.

For every k, remote vector compensation supplies one finite source at each stage with its first n bits and both residues modulo (n+1)!. Every fixed positive modulus divides all sufficiently large stage moduli, so each fixed residue coordinate is eventually correct. Each fixed bit is also eventually correct. The resulting sources converge to k and prove that the actual graph is dense. Legality and modular compatibility are closed conditions in products of finite discrete spaces. Hence K is compact Hausdorff and complete, and the dense uniform embedding gives its abstract completion structure.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/JointCompletion.compatibleObservations`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/JointCompletion.jointObservation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/JointCompletion.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/JointCompletion.sourceGraph`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/JointCompletion.sourceUniformity`
- Dependency: [D5/S1/Dynamics/ProfiniteIntegers](../../../S1/Dynamics/ProfiniteIntegers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/RemoteVectorCompensation](RemoteVectorCompensation.md)
