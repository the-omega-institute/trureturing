# Controlled-rotation assemblages do not obey the proposed LOSR angle ordering

## Abstract

The controlled-rotation channel assemblage at pi/3 converts by local operations and shared randomness to the assemblage at pi/2, contradicting the proposed angle ordering.

Matrices have complex entries and use the computational product bases. MatrixMap(A,B,C) consists of complex linear maps from matrices on A to matrices on B. The tensor product of matrices is the Kronecker product, and a dagger denotes conjugate transpose. Anonymous bracketed assumptions supply finite enumerations and decidable equality. All source line numbers refer to channel-quantum.tex in arXiv:2209.10177v3.

**Definition 1.1 (Completely positive trace-preserving maps).**

$$\forall \left(A: \operatorname{Type}\right), \left(\forall \left(B: \operatorname{Type}\right), \left([\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] [\operatorname{Fintype}\left(B\right)] \forall \left(\phi: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(A, B, \mathbb{C}\right)\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(\phi\right)\right) \Leftrightarrow \left(\left(\operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive}\left(\phi\right)\right) \land \left(\forall \left(X: \operatorname{Matrix}\left(A, A, \mathbb{C}\right)\right), \left(\operatorname{Matrix.trace}\left(\phi\left(X\right)\right) = \operatorname{Matrix.trace}\left(X\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.IsCPTP` (`✓ std3`).

*Citation.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

A map is completely positive at every finite amplification and preserves the trace of every matrix. Trace preservation is not restricted to normalized states. This is the CPTP notion used for the channels at source lines 175-179 and 217-220.

**Definition 1.2 (Binary families of qubit matrix maps).**

$$\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.Assemblage}: \operatorname{Type}\right) = \left(\operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(2\right) \to \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.Assemblage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

An Assemblage is a family of qubit matrix maps indexed first by the binary outcome a and then by the binary measurement choice x. This type supplies the carrier for the binary scenario at source line 316. The type alone imposes no positivity, trace, or no-signalling condition.

**Definition 1.3 (The half-angle y rotation).**

$$\forall \left(\theta: \mathbb{R}\right), \left(\left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.rotationY}\left(\theta\right): \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right) = \operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.cos}\left(\frac{\theta}{2}\right)\right), \operatorname{Complex.ofReal}\left(\operatorname{Real.sin}\left(\frac{\theta}{2}\right)\right)\right)\right)\right) \land \left(\operatorname{val}\left(\operatorname{Matrix.planeConformalMatrix}\left(\operatorname{Complex.ofReal}\left(\operatorname{Real.cos}\left(\frac{\theta}{2}\right)\right), \operatorname{Complex.ofReal}\left(\operatorname{Real.sin}\left(\frac{\theta}{2}\right)\right)\right)\right) = \begin{pmatrix}\operatorname{Complex.ofReal}\left(\operatorname{Real.cos}\left(\frac{\theta}{2}\right)\right)&-\operatorname{Complex.ofReal}\left(\operatorname{Real.sin}\left(\frac{\theta}{2}\right)\right)\\\operatorname{Complex.ofReal}\left(\operatorname{Real.sin}\left(\frac{\theta}{2}\right)\right)&\operatorname{Complex.ofReal}\left(\operatorname{Real.cos}\left(\frac{\theta}{2}\right)\right)\end{pmatrix}\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.rotationY` (`✓ std3`).

*Citation.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

The rotation has real cosine and sine entries included explicitly into the complex scalars. It is the lower block of the controlled rotation in Eq. CR, source lines 318-325. The identity cos squared plus sin squared equals one supplies the nonzero condition in the plane-conformal matrix construction. The definition is made for every real angle.

**Definition 1.4 (The Bell-state controlled-rotation family).**

$$\forall \left(\theta: \mathbb{R}\right), \left(\forall \left(a: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.assemblage}\left(\theta, a, x\right)\left(\rho\right) = \operatorname{let} gate := \operatorname{Matrix.kronecker}\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \operatorname{D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled}\left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.rotationY}\left(\theta\right)\right)\right); \left(\operatorname{let} joint := \operatorname{Matrix.reindex}\left(\operatorname{Equiv.prodAssoc}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Equiv.prodAssoc}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right)\right), \operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.QuantumBounds.CHSHWitness.bellDensity}, \rho\right)\right); \left(\operatorname{let} evolved := \left(\left(gate\right) \cdot \left(joint\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(gate\right)\right); \left(\operatorname{let} reduced := \operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{Matrix.submatrix}\left(evolved, \lambda \left(p: \left(\left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right) \times \operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(p.1.1, \left(p.2, p.1.2\right)\right)\right), \lambda \left(p: \left(\left(\operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)\right) \times \operatorname{Fin}\left(2\right)\right)\right) \mapsto \left(\left(p.1.1, \left(p.2, p.1.2\right)\right)\right)\right)\right); \left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(\left(\operatorname{Matrix.kronecker}\left(\operatorname{D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.chshAlice}\left(x, a\right), \left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right)\right)\right) \cdot \left(reduced\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.assemblage` (`✓ std3`).

*Citation.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

Equation CRfam, source lines 316-333, begins with the Bell density matrix on A and B and an arbitrary input matrix on the third qubit. The associativity equivalence orders the indices as A times (B times the input qubit). The gate acts on the last two qubits with B as control. The displayed permutation then places B last so that the right partial trace removes it. Alice's Pauli-z or Pauli-x measurement effect acts on A, and the left partial trace removes A. The equality specifies the linear map on every matrix, with no density-matrix restriction.

**Definition 1.5 (Local operations with shared randomness and memory).**

$$\forall \left(I: \operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.Assemblage}\right), \left(\forall \left(I': \operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.Assemblage}\right), \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.LOSRConvertible}\left(I, I'\right)\right) \Leftrightarrow \left(\exists \left(\Lambda: \operatorname{Type}\right), \left(\exists \left(S: \operatorname{Type}\right), \left(\exists \left(f\Lambda: \operatorname{Fintype}\left(\Lambda\right)\right), \left(\exists \left(fS: \operatorname{Fintype}\left(S\right)\right), \left(\exists \left(dS: \operatorname{DecidableEq}\left(S\right)\right), \left(\operatorname{letI} := f\Lambda; \left(\operatorname{letI} := fS; \left(\operatorname{letI} := dS; \left(\exists \left(p: \Lambda \to \mathbb{R}\right), \left(\exists \left(q: \Lambda \to \left(\operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(2\right) \to \left(\operatorname{Fin}\left(2\right) \to \mathbb{R}\right)\right)\right)\right)\right), \left(\exists \left(pre: \Lambda \to \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\operatorname{Fin}\left(2\right), \left(\operatorname{Fin}\left(2\right) \times S\right), \mathbb{C}\right)\right), \left(\exists \left(post: \Lambda \to \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(\left(\operatorname{Fin}\left(2\right) \times S\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\left(\forall \left(l: \Lambda\right), \left(\left(0: \mathbb{R}\right) \le p\left(l\right)\right)\right) \land \left(\left(\sum_{\left(l: \Lambda\right)} \left(p\left(l\right)\right) = \left(1: \mathbb{R}\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\forall \left(a': \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(a: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x': \operatorname{Fin}\left(2\right)\right), \left(\left(0: \mathbb{R}\right) \le q\left(l, a', x, a, x'\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\forall \left(a: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x': \operatorname{Fin}\left(2\right)\right), \left(\sum_{\left(a': \operatorname{Fin}\left(2\right)\right)} \left(\sum_{\left(x: \operatorname{Fin}\left(2\right)\right)} \left(q\left(l, a', x, a, x'\right)\right)\right) = \left(1: \mathbb{R}\right)\right)\right)\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x': \operatorname{Fin}\left(2\right)\right), \left(\forall \left(a_{1}: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(a_{2}: \operatorname{Fin}\left(2\right)\right), \left(\sum_{\left(a': \operatorname{Fin}\left(2\right)\right)} \left(q\left(l, a', x, a_{1}, x'\right)\right) = \sum_{\left(a': \operatorname{Fin}\left(2\right)\right)} \left(q\left(l, a', x, a_{2}, x'\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(pre\left(l\right)\right)\right)\right) \land \left(\left(\forall \left(l: \Lambda\right), \left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.IsCPTP}\left(post\left(l\right)\right)\right)\right) \land \left(\forall \left(a': \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x': \operatorname{Fin}\left(2\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(I'\left(a', x'\right)\left(\rho\right) = \sum_{\left(l: \Lambda\right)} \left(\sum_{\left(a: \operatorname{Fin}\left(2\right)\right)} \left(\sum_{\left(x: \operatorname{Fin}\left(2\right)\right)} \left(\left(\left(\left(p\left(l\right)\right) \cdot \left(q\left(l, a', x, a, x'\right)\right): \mathbb{R}\right)\right) \cdot \left(post\left(l\right)\left(\operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.kron}\left(I\left(a, x\right), \left(\operatorname{LinearMap.id}: \operatorname{D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap}\left(S, S, \mathbb{C}\right)\right)\right)\left(pre\left(l\right)\left(\rho\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.LOSRConvertible` (`✓ std3`).

*Citation.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

Equation LOSRtrans-channel, source lines 246-265, combines finite shared randomness Lambda, a finite quantum memory S, Alice's conditional probabilities q, and Bob's CPTP pre- and post-processing maps. The distribution p is nonnegative and sums to one. For each l, a and x', the distribution q over a' and x is nonnegative and normalized. Its marginal over a' is independent of a, which is precisely the no-retrocausation condition at source line 260. Bob sends the input into a qubit and S, applies the chosen source branch tensored with the identity on S, and maps the output qubit and S to the final qubit. The final equality holds on all complex matrices; its scalar action is by the real probability p(l)q(l,a',x,a,x').

**Definition 1.6 (The proposed angle criterion).**

$$\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.claim}\right) \Leftrightarrow \left(\forall \left(\theta_{1}: \mathbb{R}\right), \left(\forall \left(\theta_{2}: \mathbb{R}\right), \left(\left(\theta_{1} \in \operatorname{Set.Ioc}\left(\left(0: \mathbb{R}\right), \frac{\operatorname{Real.pi}}{2}\right)\right) \Rightarrow \left(\left(\theta_{2} \in \operatorname{Set.Ioc}\left(\left(0: \mathbb{R}\right), \frac{\operatorname{Real.pi}}{2}\right)\right) \Rightarrow \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.LOSRConvertible}\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.assemblage}\left(\theta_{1}\right), \operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.assemblage}\left(\theta_{2}\right)\right)\right) \Leftrightarrow \left(\theta_{1} \ge \theta_{2}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

Conjecture 3, source lines 353-355, proposes that conversion within the family is possible exactly when the source angle is at least the target angle. The displayed proposition uses the literal controlled-rotation family and the finite-memory LOSR formula above. Both real angles lie in the interval with zero excluded and pi/2 included.

**Theorem 1.7 (A conversion from the smaller angle to the larger angle).**

$$\neg \left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/zjawin-schmid-hoban-sainz-2023-channel-assemblage-losr-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zjawin-schmid-hoban-sainz-2023-channel-assemblage-losr-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Beata Zjawin; David Schmid; Matty J. Hoban; Ana Belén Sainz (2023). *The resource theory of nonclassicality of channel assemblages*. DOI: [10.22331/q-2023-10-10-1134](https://doi.org/10.22331/q-2023-10-10-1134). URL: <https://arxiv.org/abs/2209.10177v3>.

*Commentary.*

First expand the three-qubit construction in the computational basis. Tracing B removes the off-diagonal terms of its control index. The Pauli-z measurement selects one of the two remaining branches, whereas the Pauli-x measurement weights them equally. For every real theta and every input matrix rho this gives:

$$
\forall \left(\theta: \mathbb{R}\right), \left(\forall \left(a: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(x: \operatorname{Fin}\left(2\right)\right), \left(\forall \left(\rho: \operatorname{Matrix}\left(\operatorname{Fin}\left(2\right), \operatorname{Fin}\left(2\right), \mathbb{C}\right)\right), \left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.assemblage}\left(\theta, a, x\right)\left(\rho\right) = \operatorname{if} \left(x = \left(0: \operatorname{Fin}\left(2\right)\right)\right) \operatorname{then} \left(\operatorname{if} \left(a = \left(0: \operatorname{Fin}\left(2\right)\right)\right) \operatorname{then} \left(\left(\left(\frac{1}{2}: \mathbb{C}\right)\right) \cdot \left(\rho\right)\right) \operatorname{else} \left(\left(\left(\frac{1}{2}: \mathbb{C}\right)\right) \cdot \left(\left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.rotationY}\left(\theta\right)\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.rotationY}\left(\theta\right)\right)\right)\right)\right)\right) \operatorname{else} \left(\left(\left(\frac{1}{4}: \mathbb{C}\right)\right) \cdot \left(\rho + \left(\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.rotationY}\left(\theta\right)\right) \cdot \left(\rho\right)\right) \cdot \left(\operatorname{Matrix.conjTranspose}\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.rotationY}\left(\theta\right)\right)\right)\right)\right)\right)\right)\right)\right)
$$

Take a qubit memory. The pre-processing map E inserts a zero state in the source input and stores rho in memory: E(rho) = |0><0| tensor rho. Its single Kraus operator K has entry K(i,j) equal to the identity entry with row i.2 and column j when i.1 is zero, and zero otherwise. Put V(b) equal to the identity for b = 0 and to rotationY(pi/2) for b = 1. The post-processing map F(b) has Kraus operators indexed by k in Fin 2; their (i,j) entries are V(b)(i,j.2) when j.1 = k and zero otherwise. Thus F(b) traces out the source output and conjugates the memory by V(b).

Choose a shared pair l = (b,r) of independent uniform bits. Alice always queries x = 0, ignores a, and outputs a' = b when x' = 0 and a' = r when x' = 1. Her conditional probability is one exactly for this choice of x and a', and zero otherwise. Each pair has probability 1/4.

The pre-processing Kraus operator satisfies K dagger K = 1, so its Kraus map is completely positive and trace preserving. For the post-processing, the identity cos squared plus sin squared equals one gives V(b) dagger V(b) = 1 in both cases of b. Summing the products of each post-processing Kraus operator with its adjoint in the order L dagger L gives the identity on the source output and memory. The finite Kraus channel construction therefore proves that both post-processing maps are also completely positive and trace preserving.

For any complex linear qubit matrix map Phi, direct expansion of these Kraus operators shows that F(b)((Phi tensor id)(E(rho))) is the trace of Phi(|0><0|) times V(b) rho V(b) dagger. The expanded family and the trigonometric identity give trace(assemblage(theta,a,0)(|0><0|)) = 1/2 for both outcomes a. Consequently each source branch queried by Alice contributes one half of V(b) rho V(b) dagger.

At source angle pi/3, summing the two source outcomes and the four shared pairs now gives exactly the expanded family at target angle pi/2: when x' = 0, fixing a' selects b and gives the corresponding conjugation with weight 1/2; when x' = 1, fixing a' selects r and leaves the two conjugations with weight 1/4 each. Checking the binary values of a' and x' establishes this equality on every matrix.

Use these data in the definition of LOSRConvertible. The four probabilities 1/4 are nonnegative and sum to one. Alice's probabilities are zero or one and sum to one over a' and x for every l, a and x'. They do not depend on a, so their marginal over a' satisfies no retrocausation. The two CPTP conditions and the matrix equality just proved supply the remaining conditions for the conversion.

$$
\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.LOSRConvertible}\left(\operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.assemblage}\left(\frac{\operatorname{Real.pi}}{3}\right), \operatorname{D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation.assemblage}\left(\frac{\operatorname{Real.pi}}{2}\right)\right)
$$

Finally pi is positive, so pi/3 and pi/2 both belong to the required interval, and pi/3 is strictly below pi/2. If claim held, its forward implication applied to this conversion would give pi/3 at least pi/2, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.Assemblage`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.IsCPTP`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.LOSRConvertible`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.assemblage`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.rotationY`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalHockeyStickOrthogonalReduction](../Divergence/ConditionalHockeyStickOrthogonalReduction.md)
- Dependency: [D5/S3/Quantum/Dynamics/PositivePauliClockOrder](../Dynamics/PositivePauliClockOrder.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/QuantumBounds/CHSHWitness](../../QuantumBounds/CHSHWitness.md)
- Dependency: [D5/S3/QuantumBounds/StatisticalStrengthMagicSquare](../../QuantumBounds/StatisticalStrengthMagicSquare.md)
