# Ordinary queries and the prescribed fractional branch

## Abstract

Ordinary unitary queries preserve global-phase blindness, whereas prescribed fractional branches can separate their full output channels.

**Definition 1.1 (Ordinary signed oracle queries).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.query`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.query` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A true sign selects the adjoint of the oracle matrix; a false sign selects the oracle itself.

**Definition 1.2 (The controlled query for comparison).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.controlledQuery`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.controlledQuery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On control zero this matrix applies the signed query; on control one it is identity. It is the source model's controlled query and does not occur in the ordinary circuit run.

**Definition 1.3 (Fixed finite circuits).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.Circuit`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.Circuit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For dimension d, workspace dimension m+1, and natural query count N, a circuit contains N+1 unitary inter-query gates and N Boolean signs. These data are fixed before the oracle and its logarithm are quantified. N may be zero.

**Definition 1.4 (The ordered ordinary-query product).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.run`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.run` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Start at W zero and fold the ordered list of N slots by left multiplication with W at the next index and identity tensor the signed oracle. The product is W N Q N through W one Q one W zero. The identity tensor factor acts on the entire workspace.

**Definition 1.5 (The fixed basis-zero embedding).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.initialization`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.initialization` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initialization matrix J maps input psi to workspace basis zero tensor psi. Its entry is one exactly when the workspace coordinate is zero and the target coordinate equals the input index; all other entries vanish.

**Definition 1.6 (Uniform full-output success).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.Successful`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.Successful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pair U,H with U=exp(iH), H Hermitian, and real spectrum contained in [delta,2 pi), compare the conjugation channels of run(A,U) J and J exp(itH). Their difference must have the original Harrow diamondNorm at most ENNReal.ofReal epsilon. This norm is the unhalved supremum of trace norms over all positive semidefinite trace-one inputs with an input-sized untouched reference. The entire workspace and target output is retained.

**Definition 1.7 (A universal ordinary-query upper bound).**

Lean statement: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim`

*Formalization.* `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There exists a real universal constant C>0. For every real t and delta strictly between zero and one, epsilon strictly between zero and one half, and positive natural dimension d, there exist natural m,N and a fixed Circuit d m N with N at most C times inverse delta times the natural logarithm of inverse epsilon, and Successful A t delta epsilon. The circuit existential precedes every U,H in Successful.

**Theorem 1.8 (The uniform upper bound fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result` (`✓ std3`). ∎

*Resolves.* `Problems/liu-wesolowski-2026-ordinary-fractional-evolution` (refuted) by `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"liu-wesolowski-2026-ordinary-fractional-evolution","declaration_gid":"D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

Use t=delta=1/2, epsilon=1/4, and d=2. The logarithms are diagonal with entries pi/2 and 3 pi/2 in opposite orders. Their oracle exponentials are U=diag(i,-i) and -U, and both logarithms satisfy the half-open spectral promise. Every ordinary query changes sign when U is replaced by -U, including adjoint queries. Induction over the actual ordered fold gives run(A,-U)=(-1)^N run(A,U), so the initialized implementation channels agree for every finite workspace and every natural N.

The input is the equal-superposition density on the target tensored with reference basis zero. At t=1/2 the two ideal stabilized full outputs are orthogonal pure states with relative phases i and -i, initialized at workspace basis zero. Their unhalved trace-norm separation is two. Each successful implementation would lie within trace norm one quarter of its corresponding target on this admissible stabilized input. The triangle inequality would then bound two by one half, a contradiction. No query-count estimate is needed to reach this contradiction.

The source is Liu, Wesolowski, Thompson, Gu and Pira, Optimal query complexity for fractional quantum evolution, arXiv:2610.01940v1: Definitions 1-3, Appendix B, and the unnumbered uncontrolled-access question in Section V. The ordinary-query substitution leaves the controlled upper bound and the ordinary-query lower bound outside the assertion considered here. The global-phase obstruction is known prior work.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.Circuit`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.Successful`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.controlledQuery`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.initialization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.query`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/FractionalEvolutionPhaseObstruction.run`
- Dependency: [D5/S3/Quantum/QuantumChannels/HarrowParallelChernoffExponentRefutation](HarrowParallelChernoffExponentRefutation.md)
