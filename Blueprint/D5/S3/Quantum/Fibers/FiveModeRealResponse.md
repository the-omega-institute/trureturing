# Five-Mode Real Response Fibers

## Abstract

Actual five-mode protocol responses retain exactly the entrywise real part.

**Theorem 1.1 (The exact response fiber and fifteen-dimensional effect span).**

$$\forall X,Y:\operatorname{ComplexMatrix}(5),\operatorname{Hermitian}(X)\land \operatorname{Hermitian}(Y)\Rightarrow (\operatorname{AllResponses}(X)=\operatorname{AllResponses}(Y)\Leftrightarrow \operatorname{Re}(X)=\operatorname{Re}(Y))\land \operatorname{dimR}(waitSpan)=15\land \\\operatorname{RealSpan}(AllHistoryEffects)=symmetricEffectSpace\land \\(\exists F:\operatorname{FiniteMatrixSet}(5),\operatorname{Finite}(F)\land F\subseteq AllHistoryEffects\land \operatorname{RealSpan}(F)=symmetricEffectSpace)\land \\(\forall Seed:Type,[\operatorname{MeasurableSpace}(Seed)],\forall mu:\operatorname{Measure}(Seed),\forall strategy:\operatorname{ProtocolFamily}(Seed,5),\forall event:\operatorname{FiniteEventFamily}(strategy),\operatorname{Re}(X)=\operatorname{Re}(Y)\Rightarrow \operatorname{randomEventProbability}(mu,strategy,event,X)=\operatorname{randomEventProbability}(mu,strategy,event,Y))\land \\(\forall Z:\operatorname{ComplexMatrix}(5),\operatorname{PSD}(Z)\Rightarrow \operatorname{AllResponses}(\operatorname{symmetrize}(Z))=\operatorname{AllResponses}(Z))\land \neg \operatorname{CP}(symmetrize)\land \operatorname{finiteOrthogonalReadout}(AllResponses)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeRealResponse.five_mode_real_response_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The wait is the entrywise complex embedding of exp(t A), for arbitrary nonnegative real t. These waits satisfy the semigroup and unitary identities. Every finite feedback tree, including Stop, is evaluated by the actual complex Lueders recursion.

For any two Hermitian matrices, equality on every retained protocol history is equivalent to entrywise real-part equality. Each operational history probability is paired with its explicit Heisenberg effect. The full-protocol to first-read span correspondence and the nonnegative-time symmetric spanning theorem prove that the real span of all actual history effects is exactly the entrywise complex embedding of the real symmetric matrices. A finite subset of actual history effects is proved to span this same space, by finite generation and finite support inside the actual family. Adjoining the actual Stop effect and reindexing produces a nonempty finite vector of actual effects, each positive and bounded by the identity. The finiteOrthogonalReadout clause identifies the entire menu fiber with this finite trace readout, its centered invisible residual, and its visible orthogonal projection, by applying ReadoutOrthogonalEquivalence to the actual supplier. The residual and projection equivalences are asserted on positive trace-one states; the entrywise-real equivalence holds on all Hermitian inputs. Upper-triangular coordinates give effect dimension fifteen. Transpose symmetrization preserves every actual menu response on positive inputs, while its Choi obstruction excludes complete positivity. The response equality also persists after integrating any seed-dependent finite recorded event against any input-independent seed measure, with randomEventProbability defined as the Bochner integral of the finite-history event weight. It represents a probability for a probability seed measure and a measurable event-probability function; the integral equality itself also holds for arbitrary seed measures.

**Theorem 1.2 (Ten blind directions form a physical neighborhood at full rank).**

$$\forall \rho:\operatorname{ComplexMatrix}(5),\operatorname{PosDef}(\rho)\land \operatorname{Tr}(\rho)=1\Rightarrow \operatorname{dimR}(blindDirections)=10\land \operatorname{dimR}(normalizedVisibleDirections)=14\land \operatorname{dimR}(\operatorname{traceZeroHermitian}(5))=24\land \\\exists r\in \mathbb{R},r>0\land \forall D\in blindDirections,\operatorname{CStarNorm}(D)<r\Rightarrow \operatorname{PSD}(\rho+D)\land \operatorname{Tr}(\rho+D)=1\land \operatorname{AllResponses}(\rho)=\operatorname{AllResponses}(\rho+D)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeRealResponse.full_rank_blind_fiber_neighborhood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the real Hermitian input space the real-coordinate map is onto the symmetric effects, so its kernel has dimension ten. The trace-one response directions have dimension fourteen, while the ambient trace-zero Hermitian directions have dimension twenty-four. The ambient dimension is the Hermitian dimension formula of BipartiteSectorDecomposition.

For a positive-definite trace-one input, a strictly positive spectral lower bound gives a positive radius. Every blind perturbation smaller than this radius remains positive, retains trace one, and has exactly the same finite protocol responses. This establishes a relative neighborhood in all ten linear blind directions. Positive definiteness is essential to this local physical statement; the theorem makes no such neighborhood claim at rank-deficient states.

**Theorem 1.3 (Orthogonal pure states with identical actual menu responses).**

$$\operatorname{Density}(\operatorname{pairState}(1))\land \operatorname{Density}(\operatorname{pairState}(-1))\land \operatorname{pairState}(1)\operatorname{pairState}(-1)=0\land \operatorname{pairState}(1)\neq \operatorname{pairState}(-1)\land \operatorname{AllResponses}(\operatorname{pairState}(1))=\operatorname{AllResponses}(\operatorname{pairState}(-1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/FiveModeRealResponse.orthogonal_pair_same_actual_responses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two normalized rank-one states lie on the rays e_N plus i e_2 and e_N minus i e_2. Their matrices are one half of the corresponding unnormalized outer products. The proof checks positivity, trace one, zero product, and distinctness, then consumes the full real-response fiber theorem to obtain equality for every actual finite protocol.

Measurement-relative compression is prior work of Bluhm, Rauber and Wolf, arXiv:1708.04898v4. Koashi and Imoto, quant-ph/0101144, provide broader no-disturbance structure. A response quotient and invisible state directions do not supply a completely positive compression channel. No novelty or optimality claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeRealResponse.five_mode_real_response_fiber`
- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeRealResponse.full_rank_blind_fiber_neighborhood`
- Truth anchor: `D5/S3/Quantum/Fibers/FiveModeRealResponse.orthogonal_pair_same_actual_responses`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Fibers/FiveModeRealWaitSpan](FiveModeRealWaitSpan.md)
- Dependency: [D5/S3/Quantum/Fibers/RankOneFeedbackProtocol](RankOneFeedbackProtocol.md)
- Dependency: [D5/S3/Quantum/Fibers/ReadoutOrthogonalEquivalence](ReadoutOrthogonalEquivalence.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/RealPartPositiveObstruction](../QuantumChannels/RealPartPositiveObstruction.md)
