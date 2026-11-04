# Subsystem size does not order coherent information

## Abstract

A uniformly dephased graph state on five plus four qubits has greater coherent information on its smaller subsystem.

**Definition 1.1 (An independently dephased qubit).**

$$\forall (P: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.noisyQubit}\left(P\right): \operatorname{Matrix}\left(\operatorname{Bool}, \operatorname{Bool}, \mathbb{C}\right)) = \mathrm{let} (plus: (\operatorname{Bool}) \to (\mathbb{C})):= (\lambda (b: \operatorname{Bool}) \mapsto (\operatorname{D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.plusState}\left((1: \mathbb{N}), \operatorname{Function.const}\left(\operatorname{Fin}\left(1\right), b\right)\right))); (\mathrm{let} (minus: (\operatorname{Bool}) \to (\mathbb{C})):= (\lambda (b: \operatorname{Bool}) \mapsto ((\operatorname{ite}\left(b = \operatorname{Bool.true}, -(1: \mathbb{C}), (1: \mathbb{C})\right)) \cdot (plus\left(b\right)))); ((\operatorname{smul}\left((\operatorname{Complex.ofReal}\left(P\right): \mathbb{C}), \operatorname{Matrix.vecMulVec}\left(plus, \operatorname{star}\left(plus\right)\right)\right)) + (\operatorname{smul}\left((\operatorname{Complex.ofReal}\left(((1: \mathbb{R})) - (P)\right): \mathbb{C}), \operatorname{Matrix.vecMulVec}\left(minus, \operatorname{star}\left(minus\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.noisyQubit` (`✓ std3`).

*Citation.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

The vectors plus and minus are the one-qubit states with computational-basis amplitudes (1,1)/√2 and (1,−1)/√2. Their outer products are mixed with real weights P and 1−P, each explicitly included in the complex scalars. For P in [0,1] this is the dephasing model of Section 2.2, arXiv v2 main.tex, lines 186–194. The displayed matrix-valued function is defined for every real P.

**Definition 1.2 (The phase from controlled-Z gates).**

$$\forall (nA: \mathbb{N}), (\forall (nB: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\forall (x: (\operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)) \to (\operatorname{Bool})), ((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.czPhase}\left(G, x\right): \mathbb{C}) = \prod_{e \in \operatorname{SimpleGraph.edgeFinset}\left(G\right)} (\operatorname{D5.S3.Quantum.Entanglement.RandomizedGraphNegativityRefutation.czPhase}\left(\operatorname{Sym2.map}\left(\operatorname{Equiv.toFun}\left(\operatorname{finSumFinEquiv}\right), e\right), \operatorname{Function.comp}\left(x, \operatorname{Equiv.toFun}\left(\operatorname{Equiv.symm}\left(\operatorname{finSumFinEquiv}\right)\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.czPhase` (`✓ std3`).

*Citation.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

For a Boolean assignment x on the disjoint union of the two vertex sets, multiply the diagonal controlled-Z entry over every edge. The equivalence finSumFinEquiv relabels the disjoint union as Fin (nA+nB); its inverse transports the assignment. Each edge contributes minus one precisely when both endpoint bits are true. This is the commuting controlled-Z construction of Section 2.1, arXiv v2 main.tex, lines 163–177.

**Definition 1.3 (The noisy graph-state matrix).**

$$\forall (nA: \mathbb{N}), (\forall (nB: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\forall (P: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.graphState}\left(G, P\right): \operatorname{Matrix}\left(\operatorname{Prod}\left((\operatorname{Fin}\left(nA\right)) \to (\operatorname{Bool}), (\operatorname{Fin}\left(nB\right)) \to (\operatorname{Bool})\right), \operatorname{Prod}\left((\operatorname{Fin}\left(nA\right)) \to (\operatorname{Bool}), (\operatorname{Fin}\left(nB\right)) \to (\operatorname{Bool})\right), \mathbb{C}\right)) = \lambda (x: \operatorname{Prod}\left((\operatorname{Fin}\left(nA\right)) \to (\operatorname{Bool}), (\operatorname{Fin}\left(nB\right)) \to (\operatorname{Bool})\right)) \mapsto (\lambda (y: \operatorname{Prod}\left((\operatorname{Fin}\left(nA\right)) \to (\operatorname{Bool}), (\operatorname{Fin}\left(nB\right)) \to (\operatorname{Bool})\right)) \mapsto (((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.czPhase}\left(G, \operatorname{Sum.elim}\left(\operatorname{Prod.fst}\left(x\right), \operatorname{Prod.snd}\left(x\right)\right)\right)) \cdot (\prod_{v: \operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)} (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.noisyQubit}\left(P, \operatorname{Sum.elim}\left(\operatorname{Prod.fst}\left(x\right), \operatorname{Prod.snd}\left(x\right)\right)\left(v\right), \operatorname{Sum.elim}\left(\operatorname{Prod.fst}\left(y\right), \operatorname{Prod.snd}\left(y\right)\right)\left(v\right)\right)))) \cdot (\operatorname{star}\left(\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.czPhase}\left(G, \operatorname{Sum.elim}\left(\operatorname{Prod.fst}\left(y\right), \operatorname{Prod.snd}\left(y\right)\right)\right)\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.graphState` (`✓ std3`).

*Citation.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

The computational basis is indexed by a pair of Boolean assignments, one on each subsystem. Multiply the independent one-qubit matrix entries and conjugate by the diagonal controlled-Z phases. Thus x supplies the row assignment and y the column assignment. For P in [0,1] this is the uniformly dephased graph state of Sections 2.1–2.2, arXiv v2 main.tex, lines 175–194. The matrix expression itself permits every real P and either subsystem to be empty.

**Definition 1.4 (Entropy in bits).**

$$\forall (\iota: \operatorname{Type}*), ([\operatorname{Fintype}\left(\iota\right)], ([\operatorname{DecidableEq}\left(\iota\right)], (\forall (rho: \operatorname{Matrix}\left(\iota, \iota, \mathbb{C}\right)), ((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.entropy2}\left(rho\right): \mathbb{R}) = \frac{-\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left((\operatorname{CStarMatrix.ofMatrix}\left(rho\right)) \cdot (\operatorname{CFC.log}\left(\operatorname{CStarMatrix.ofMatrix}\left(rho\right)\right))\right)\right)}{\operatorname{Real.log}\left((2: \mathbb{R})\right)}))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.entropy2` (`✓ std3`).

*Citation.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

For a finite square complex matrix rho, take the negative real part of the trace of rho times its continuous-functional-calculus logarithm, then divide by the natural logarithm of two. CStarMatrix.ofMatrix supplies the matrix C-star algebra. On density matrices this is the base-two von Neumann entropy in Section 2.3, arXiv v2 main.tex, lines 206–209. The displayed function has no positivity or trace-one hypothesis; its values elsewhere are the extension specified by this expression.

**Definition 1.5 (Coherent information on the first subsystem).**

$$\forall (nA: \mathbb{N}), (\forall (nB: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\forall (P: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.coherentInfoA}\left(G, P\right): \mathbb{R}) = (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.entropy2}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight}\left(\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.graphState}\left(G, P\right)\right)\right)) - (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.entropy2}\left(\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.graphState}\left(G, P\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.coherentInfoA` (`✓ std3`).

*Citation.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

Trace out the second subsystem, take the entropy of the first marginal, and subtract the entropy of the joint state. This is the reverse coherent information of Section 2.3, arXiv v2 main.tex, lines 210–216, with the source's choice of subsystem names.

**Definition 1.6 (Coherent information on the second subsystem).**

$$\forall (nA: \mathbb{N}), (\forall (nB: \mathbb{N}), (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\forall (P: \mathbb{R}), ((\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.coherentInfoB}\left(G, P\right): \mathbb{R}) = (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.entropy2}\left(\operatorname{D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceLeft}\left(\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.graphState}\left(G, P\right)\right)\right)) - (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.entropy2}\left(\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.graphState}\left(G, P\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.coherentInfoB` (`✓ std3`).

*Citation.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

Trace out the first subsystem, take the entropy of the second marginal, and subtract the entropy of the joint state. This is the coherent information of Section 2.3, arXiv v2 main.tex, lines 201–209.

**Definition 1.7 (The proposed subsystem-size ordering).**

$$(\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.claim}: \operatorname{Prop}) = (\forall (nA: \mathbb{N}), (\forall (nB: \mathbb{N}), ((nB < nA) \Rightarrow (\forall (G: \operatorname{SimpleGraph}\left(\operatorname{Sum}\left(\operatorname{Fin}\left(nA\right), \operatorname{Fin}\left(nB\right)\right)\right)), ([\operatorname{DecidableRel}\left(\operatorname{SimpleGraph.Adj}\left(G\right)\right)], (\forall (P: \mathbb{R}), ((P \in \operatorname{Set.Icc}\left((0: \mathbb{R}), (1: \mathbb{R})\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.coherentInfoB}\left(G, P\right) \le \operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.coherentInfoA}\left(G, P\right)))))))))$$

*Formalization.* `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

For every pair of natural subsystem sizes with nB<nA, every simple graph on their disjoint union, and every common dephasing parameter P in [0,1], the proposed inequality places the second subsystem's coherent information below the first's. This is a non-strict mathematical reading of the conjecture in Section 5.4, arXiv v2 main.tex, lines 948–951. It allows edges inside either subsystem as well as between them.

**Theorem 1.8 (A nine-qubit counterexample).**

$$\neg (\operatorname{D5.S3.Quantum.Information.NoisyGraphStateCoherentInformationRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sajjad-kaur-goodenough-towsley-guha-2026-coherent-information-ordering-refutation` (refuted) by `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sajjad-kaur-goodenough-towsley-guha-2026-coherent-information-ordering-refutation","declaration_gid":"D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aqil Sajjad; Eneet Kaur; Kenneth Goodenough; Don Towsley; Saikat Guha (2026). *Lower bounds on bipartite entanglement in noisy graph states*. DOI: [10.22331/q-2026-05-21-2111](https://doi.org/10.22331/q-2026-05-21-2111). URL: <https://arxiv.org/abs/2404.09014v2>.

*Commentary.*

First, a noisy-qubit matrix entry is one half when its two bits agree and (2P−1)/2 otherwise. A character product has the form ∏ⱼ(−1) raised to k(j)b(j), with natural exponents k(j) and Boolean bits b(j). Its sum over all assignments b is 2 to the number of bits when every k(j) is even, and zero otherwise. For a bipartite graph with Boolean biadjacency matrix N, its controlled-Z phase at assignments (a,b) is the product of (−1) raised to N(i,j)a(i)b(j). Put t=2P−1. On any finite set of bits, the product of noisy-qubit entries is 2 to the negative number of bits times t to the Hamming distance. Pairing two controlled-Z phases combines the assignments by exclusive-or. The character sums therefore give the first marginal entry as 2 to the power −nA times t to the Hamming distance between a and a′, provided N transpose sends their exclusive-or to zero over the two-element field, and is zero otherwise. The second marginal has the analogous expression with nB and the kernel of N.

Take nA=5, nB=4 and no edges within either subsystem. The five biadjacency rows are (1,1,0,0), (1,1,0,0), (1,1,0,0), (1,0,1,0), and (1,0,0,1). Choose P=255/256, so t=127/128, and put s=t². The kernel of the transpose consists of 00000, 11000, 10100 and 01100; every nonzero element has weight two. The kernel of the biadjacency matrix consists of 0000 and 1111.

Let Q_A have entry 1/4 when the exclusive-or of its two five-bit indices belongs to the transpose kernel, and zero otherwise. Let Q_B be half the sum of the identity and the permutation matrix that complements all four bits. For Q_A, two row supports are equal four-element cosets or are disjoint, so Q_A²=Q_A. The complement permutation is an involution, giving Q_B²=Q_B. Both matrices have real symmetric entries and hence are Hermitian. Each has trace eight: the diagonal entries are respectively 1/4 on 32 indices and 1/2 on 16 indices. The first reduced matrix equals αQ_A+β(I−Q_A), where α=(1+3s)/32 and β=(1−s)/32. The second equals γQ_B+δ(I−Q_B), where γ=(1+s²)/16 and δ=(1−s²)/16. The first equality follows from the weight-two property; the second follows because distinct allowed four-bit indices are complements and have Hamming distance four.

For any Hermitian projection Q and real r and z, apply FullwoodParzygnatSubadditivityRefutation.projection_cfc to zI+(r−z)Q. Its logarithm is (log r)Q+(log z)(I−Q). Transporting the functional calculus to CStarMatrix and multiplying eliminates the cross terms, since Q(I−Q)=(I−Q)Q=0. Taking the trace gives the entropy numerator −trace(Q)r log r−(dimension−trace(Q))z log z. Thus the two marginal entropies are (−8α log α−24β log β)/log 2 and (−8γ log γ−8δ log δ)/log 2.

Rewrite log α as log((1+3s)/4)−3 log 2, log β as log(1−s)−5 log 2, log γ as log((1+s²)/2)−3 log 2, and log δ as log(1−s)+log(1+s)−4 log 2. For positive x, the inequalities 1−1/x≤log x and log x≤x−1 give a lower bound on log((1+3s)/4) and an upper bound on log((1+s²)/2), respectively. Also 0<1−s≤1/64 and 0<1+s≤2 give log(1−s)≤−6 log 2 and log(1+s)≤log 2. At s=(127/128)² these bounds, together with log 2<9/10, yield −8α log α−24β log β<−8γ log γ−8δ log δ. Since log 2 is positive, the first marginal entropy is strictly smaller than the second.

Finally apply the proposed ordering at sizes five and four, this graph, and P=255/256, which lies in [0,1]. Subtracting the same joint entropy from both marginal entropies preserves their strict order. The proposed inequality would therefore require the larger second marginal entropy to be at most the smaller first marginal entropy, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.coherentInfoA`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.coherentInfoB`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.czPhase`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.entropy2`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.graphState`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.noisyQubit`
- Truth anchor: `D5/S3/Quantum/Information/NoisyGraphStateCoherentInformationRefutation.result`
- Dependency: [D5/S3/Quantum/Entanglement/RandomizedGraphNegativityRefutation](../Entanglement/RandomizedGraphNegativityRefutation.md)
- Dependency: [D5/S3/Quantum/Information/FullwoodParzygnatSubadditivityRefutation](FullwoodParzygnatSubadditivityRefutation.md)
