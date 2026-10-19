# One ancillary qubit cannot give constant-round universal channel simulation

## Abstract

A family of sign-frame channels has exact postselection success at most 4 times 4 to the R divided by n for every adaptive protocol with one ancillary qubit and at most R measurement rounds. Finite classical randomization preserves this bound, excluding universal constant depth and constant positive success.

**Definition 1.1 (The system and its ancillary qubit).**

$$\forall I \in Type,\; (\operatorname{Workspace}\left(I\right) = \operatorname{CStarMatrix}\left(((I) \times (\operatorname{Fin}\left(2\right))), ((I) \times (\operatorname{Fin}\left(2\right))), \mathbb{C}\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.Workspace` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

For a system with coordinate type I, the joint workspace has coordinates I times Fin(2). Workspace is the complex square-matrix algebra with its operator norm. In the formulas, ofMatrix denotes CStarMatrix.ofMatrix, and symm(ofMatrix) is its inverse, taking a workspace operator to its ordinary matrix; adjoint denotes conjugate transpose. The finite-type and decidable-equality structures on I are assumed to exist.

**Definition 1.2 (A complete projective measurement).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow (\forall k \in \mathbb{N},\; (\operatorname{Measurement}\left(I, k\right) = \Sigma_{P : \operatorname{Fin}\left(k\right) \to \operatorname{Workspace}\left(I\right)} ((\forall o \in \operatorname{Fin}\left(k\right),\; (\operatorname{adjoint}\left(\operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right)\right) = \operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right))) \land ((\forall o \in \operatorname{Fin}\left(k\right),\; (\operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right) \cdot \operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right) = \operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right))) \land ((\forall o \in \operatorname{Fin}\left(k\right), z \in \operatorname{Fin}\left(k\right),\; ((o \ne z) \Rightarrow (\operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right) \cdot \operatorname{symm}\left(ofMatrix\right)\left(P\left(z\right)\right) = 0))) \land (\sum_{o : \operatorname{Fin}\left(k\right)} (\operatorname{symm}\left(ofMatrix\right)\left(P\left(o\right)\right)) = 1)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.Measurement` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

A measurement consists of a family P of k workspace operators and a proof that their underlying matrices form a complete family of pairwise orthogonal self-adjoint projections. Zero projections are allowed. There is no bound on k. This is the projective-measurement operation allowed in Question 6.1 of Kotowski and Kotowski. The displayed dependent sum spells out the projector and record fields.

**Definition 1.3 (Adaptive protocol trees).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow ((\forall R \in \mathbb{N}, b \in Bool,\; (\left(leaf_{R}\right)\left(b\right) : \operatorname{Protocol}\left(I, R\right))) \land (\forall R \in \mathbb{N}, k \in \mathbb{N}, U \in \operatorname{unitary}\left(\operatorname{Workspace}\left(I\right)\right), P \in \operatorname{Measurement}\left(I, k\right), c \in \operatorname{Fin}\left(k\right) \to \operatorname{Protocol}\left(I, R\right),\; (\operatorname{node}\left(k, U, P, c\right) : \operatorname{Protocol}\left(I, R + 1\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.Protocol` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

These are the constructors of an inductively generated family of finite trees, with no other constructors. A leaf records a Boolean success flag and is allowed at every depth bound R. A node applies U, measures P, and chooses the child indexed by the observed outcome. Its children have depth bound R and the node has depth bound R+1. The subscript on leaf records its implicit depth bound. This describes the unitary, measurement and adaptive operations of Question 6.1 with the ancilla initially in the fixed state zero.

**Definition 1.4 (Complete measurement histories).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow ((\forall R \in \mathbb{N}, b \in Bool,\; (\operatorname{History}\left(\left(leaf_{R}\right)\left(b\right)\right) = Unit)) \land (\forall R \in \mathbb{N}, k \in \mathbb{N}, U \in \operatorname{unitary}\left(\operatorname{Workspace}\left(I\right)\right), P \in \operatorname{Measurement}\left(I, k\right), c \in \operatorname{Fin}\left(k\right) \to \operatorname{Protocol}\left(I, R\right),\; (\operatorname{History}\left(\operatorname{node}\left(k, U, P, c\right)\right) = \Sigma_{o : \operatorname{Fin}\left(k\right)} (\operatorname{History}\left(c\left(o\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.History` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

A leaf has the single history of Unit. At a node, a history is an outcome o followed by a history of the child c(o). The dependent sum retains which continuation belongs to each observed outcome.

**Definition 1.5 (The finite set of histories).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow (\forall R \in \mathbb{N}, t \in \operatorname{Protocol}\left(I, R\right),\; (\operatorname{historyFintype}\left(t\right) : \operatorname{Fintype}\left(\operatorname{History}\left(t\right)\right))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.historyFintype` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

Every tree has a finite history type: Unit is finite, and a finite dependent sum of finite child-history types is finite. The displayed term supplies that finite-type structure.

**Definition 1.6 (Which histories succeed).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow ((\forall R \in \mathbb{N}, b \in Bool,\; (\forall u \in Unit,\; (\operatorname{succeeds}\left(\left(leaf_{R}\right)\left(b\right), u\right) = b))) \land (\forall R \in \mathbb{N}, k \in \mathbb{N}, U \in \operatorname{unitary}\left(\operatorname{Workspace}\left(I\right)\right), P \in \operatorname{Measurement}\left(I, k\right), c \in \operatorname{Fin}\left(k\right) \to \operatorname{Protocol}\left(I, R\right),\; (\forall o \in \operatorname{Fin}\left(k\right), h \in \operatorname{History}\left(c\left(o\right)\right),\; (\operatorname{succeeds}\left(\operatorname{node}\left(k, U, P, c\right), (o, h)\right) = \operatorname{succeeds}\left(c\left(o\right), h\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.succeeds` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

The success flag of a complete history is the flag on its terminal leaf. Both true and false leaves are permitted, independently at different histories.

**Definition 1.7 (Ordered branch products).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow ((\forall R \in \mathbb{N}, b \in Bool,\; (\forall u \in Unit,\; (\operatorname{branch}\left(\left(leaf_{R}\right)\left(b\right), u\right) = 1))) \land (\forall R \in \mathbb{N}, k \in \mathbb{N}, U \in \operatorname{unitary}\left(\operatorname{Workspace}\left(I\right)\right), P \in \operatorname{Measurement}\left(I, k\right), c \in \operatorname{Fin}\left(k\right) \to \operatorname{Protocol}\left(I, R\right),\; (\forall o \in \operatorname{Fin}\left(k\right), h \in \operatorname{History}\left(c\left(o\right)\right),\; (\operatorname{branch}\left(\operatorname{node}\left(k, U, P, c\right), (o, h)\right) = \operatorname{branch}\left(c\left(o\right), h\right) \cdot \operatorname{projector}\left(P, o\right) \cdot U)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.branch` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

The empty branch has operator one. At a node, the current unitary acts first, followed by the outcome projector and then the remaining branch product. Thus earlier operations occur on the right of the product.

**Definition 1.8 (Compression to the system).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow (\forall R \in \mathbb{N}, t \in \operatorname{Protocol}\left(I, R\right),\; (\forall B \in \operatorname{Workspace}\left(I\right), h \in \operatorname{History}\left(t\right), a \in \operatorname{Fin}\left(2\right), i \in I, j \in I,\; (((\operatorname{succeeds}\left(t, h\right) = true) \Rightarrow (\operatorname{krausFrom}\left(t, B, h, a\right)\left(i, j\right) = \operatorname{symm}\left(ofMatrix\right)\left(\operatorname{branch}\left(t, h\right) \cdot B\right)\left((i, a), (j, 0)\right))) \land ((\operatorname{succeeds}\left(t, h\right) = false) \Rightarrow (\operatorname{krausFrom}\left(t, B, h, a\right)\left(i, j\right) = 0))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.krausFrom` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

The prefix B is any workspace operator. On a successful history, compress branch(t,h) B from the input ancilla coordinate zero to the output ancilla coordinate a. A failed history contributes the zero matrix. The formula is entrywise for every pair of system coordinates; it imposes no norm condition on B. In the successful map B is one, so the input ancilla is fixed and summing over a discards the final qubit.

**Definition 1.9 (The successful map of a tree).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow (\forall R \in \mathbb{N}, t \in \operatorname{Protocol}\left(I, R\right),\; (\forall X \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; (\operatorname{successfulMap}\left(t, X\right) = \sum_{h : \operatorname{History}\left(t\right)} (\sum_{a : \operatorname{Fin}\left(2\right)} (\operatorname{krausFrom}\left(t, 1, h, a\right) \cdot X \cdot \operatorname{adjoint}\left(\operatorname{krausFrom}\left(t, 1, h, a\right)\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.successfulMap` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

For a deterministic tree t, sum the Kraus conjugations over every complete history and both final ancillary basis coordinates. Failed histories contribute zero. This is the unnormalized successful map; equality to q times a trace-preserving target channel gives input-independent success probability q, as in the postselection convention of Definition 2.3.

**Definition 1.10 (Finite classical randomization).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow (\forall R \in \mathbb{N},\; (\operatorname{RandomizedProtocol}\left(I, R\right) = \Sigma_{N : \mathbb{N}} (((\operatorname{StdSimplex}\left(\mathbb{R}, \operatorname{Fin}\left(N\right)\right)) \times (\operatorname{Fin}\left(N\right) \to \operatorname{Protocol}\left(I, R\right)))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.RandomizedProtocol` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

The record has a natural number N of seeds, a real probability vector w in the standard simplex on Fin(N), and a tree c(s) of the same depth bound for each seed. The standard simplex requires nonnegative weights with sum one. The dependent sum selects N, and its body is the product of the probability and tree fields. This is the finite classical randomization allowed in the simulation model.

**Definition 1.11 (The successful map after randomization).**

$$\forall I \in Type,\; (((\operatorname{Nonempty}\left(\operatorname{Fintype}\left(I\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{DecidableEq}\left(I\right)\right))) \Rightarrow (\forall R \in \mathbb{N}, p \in \operatorname{RandomizedProtocol}\left(I, R\right), X \in \operatorname{Matrix}\left(I, I, \mathbb{C}\right),\; (\operatorname{mixtureMap}\left(p, X\right) = \sum_{s : \operatorname{Fin}\left(\operatorname{seeds}\left(p\right)\right)} (\operatorname{ofReal}\left(\operatorname{weights}\left(\operatorname{probability}\left(p\right), s\right)\right) \cdot \operatorname{successfulMap}\left(\operatorname{tree}\left(p, s\right), X\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.mixtureMap` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

For a randomized protocol p, average the successful maps of its trees with its real simplex weights, cast to complex scalars. Each input matrix uses the same distribution of trees.

**Definition 1.12 (Universal depth and success constants).**

$$claim \Leftrightarrow (\exists Rzero \in \mathbb{N}, qzero \in \mathbb{R},\; ((0 < qzero) \land (\forall d \in \mathbb{N}, Phi \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; (\exists p \in \operatorname{RandomizedProtocol}\left(\operatorname{Fin}\left(d\right), Rzero\right), q \in \mathbb{R},\; ((qzero \le q) \land (\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right),\; (\operatorname{mixtureMap}\left(p, X\right) = \operatorname{ofReal}\left(q\right) \cdot \operatorname{symm}\left(ofMatrix\right)\left(\operatorname{toCompletelyPositiveMap}\left(Phi\right)\left(\operatorname{ofMatrix}\left(X\right)\right)\right))))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.claim` (`✓ std3`).

*Citation.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

This is the affirmative reading of Question 6.1: there are a natural depth bound Rzero and a positive real qzero, both independent of dimension and target channel, such that every completely positive trace-preserving channel has an exact successful map q times that channel with q at least qzero. The displayed channel action first applies ofMatrix to X, then the channel's toCompletelyPositiveMap, and finally symm(ofMatrix). Equality is on every complex matrix, not only one input state. The source's Definition 2.3 supplies the postselection convention; Question 6.1 adds projective measurements and adaptive unitaries. The definition imposes qzero at most q and does not include a separate upper bound on q.

**Definition 1.13 (Basis coordinates and sign coordinates).**

$$\forall n \in \mathbb{N},\; (\operatorname{FrameIndex}\left(n\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(n \cdot n\right), \operatorname{Fin}\left(n \cdot n\right) \to Bool\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.FrameIndex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

For m=n squared, the coordinate type is the disjoint sum of m basis labels and all Boolean strings of length m. Its cardinality is d=m+2 to the m. No positivity assumption on n is part of this type definition.

**Definition 1.14 (The sign frame).**

$$\forall n \in \mathbb{N},\; ((\forall i \in \operatorname{Fin}\left(n \cdot n\right), j \in \operatorname{Fin}\left(n \cdot n\right),\; (\operatorname{frame}\left(n\right)\left(\operatorname{inl}\left(i\right), j\right) = \operatorname{ite}\left(i = j, 1, 0\right))) \land (\forall s \in \operatorname{Fin}\left(n \cdot n\right) \to Bool, j \in \operatorname{Fin}\left(n \cdot n\right),\; (\operatorname{frame}\left(n\right)\left(\operatorname{inr}\left(s\right), j\right) = \frac{\operatorname{ofReal}\left(\operatorname{ite}\left(s\left(j\right), 1, -1\right)\right)}{\operatorname{natCast}\left(\mathbb{C}, n\right)})))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.frame` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

The basis rows form the identity matrix. A Boolean sign row has entry +1/n where the Boolean is true and -1/n where it is false. The displayed real conditional equals boolSign applied to the Boolean complement; ofReal embeds it into the complex numbers. The notation natCast(C,n) denotes the natural-to-complex embedding of the denominator. The definition includes n=0, where there are no column indices. For positive n every row has squared Euclidean norm one.

**Definition 1.15 (Relabelling the frame by a finite ordinal).**

$$\forall n \in \mathbb{N}, i \in \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), j \in \operatorname{Fin}\left(n \cdot n\right),\; (\operatorname{frameNat}\left(n\right)\left(i, j\right) = \operatorname{frame}\left(n\right)\left(\operatorname{symm}\left(\operatorname{equivFin}\left(\operatorname{FrameIndex}\left(n\right)\right)\right)\left(i\right), j\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.frameNat` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

Relabel the rows of frame(n) by Fin(card(FrameIndex(n))) using the inverse of Fintype.equivFin; the column labels are unchanged. This puts the same frame on the coordinate type used by the universal channel claim.

**Theorem 1.16 (The universal constants do not exist).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/kotowski-kotowski-2026-one-qubit-simulation-refutation` (refuted) by `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kotowski-kotowski-2026-one-qubit-simulation-refutation","declaration_gid":"D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marcin Kotowski; Michał Kotowski (2026). *Randomized simulation of quantum channels using small ancilla*. URL: <https://arxiv.org/abs/2606.08784v1>.

*Commentary.*

The sign-frame family is a repository construction addressing the question of Kotowski and Kotowski. Fix an integer n at least 2, put m=n squared and d=m+2 to the m, and let A=frame(n). Relabel its rows by frameNat(n) when using Fin(d). With D_j the diagonal matrix formed from column j, define the channel Phi_n by the sum of D_j X D_j adjoint. The unit norm of every row makes this channel trace preserving and unital. In the displayed bound natCast(R,n) denotes the natural-to-real embedding.

$$
\forall n \in \mathbb{N},\; ((2 \le n) \Rightarrow (\exists Phi \in \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right)\right),\; ((\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \mathbb{C}\right),\; (\operatorname{symm}\left(ofMatrix\right)\left(\operatorname{toCompletelyPositiveMap}\left(Phi\right)\left(\operatorname{ofMatrix}\left(X\right)\right)\right) = \sum_{j : \operatorname{Fin}\left(n \cdot n\right)} (\operatorname{diagonal}\left(\lambda i : \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \operatorname{frameNat}\left(n\right)\left(i, j\right)\right) \cdot X \cdot \operatorname{adjoint}\left(\operatorname{diagonal}\left(\lambda i : \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \operatorname{frameNat}\left(n\right)\left(i, j\right)\right)\right)))) \land (\forall R \in \mathbb{N}, p \in \operatorname{RandomizedProtocol}\left(\operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), R\right), q \in \mathbb{R},\; ((\forall X \in \operatorname{Matrix}\left(\operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \operatorname{Fin}\left(\operatorname{card}\left(\operatorname{FrameIndex}\left(n\right)\right)\right), \mathbb{C}\right),\; (\operatorname{mixtureMap}\left(p, X\right) = \operatorname{ofReal}\left(q\right) \cdot \operatorname{symm}\left(ofMatrix\right)\left(\operatorname{toCompletelyPositiveMap}\left(Phi\right)\left(\operatorname{ofMatrix}\left(X\right)\right)\right))) \Rightarrow (q \cdot \operatorname{natCast}\left(\mathbb{R}, n\right) \le 4 \cdot 4^{R}))))))
$$

Suppose the successful map equals q Phi_n on every matrix. For every seed of positive probability, each successful compressed Kraus matrix is diagonal of the form diag(A v). Every nonzero such matrix has rank at least r=2 to the (m-1) plus 1. Since 5r>2d, a projective measurement on the joint 2d-dimensional workspace has at most four outcomes admitting a nonzero successful continuation. A deterministic tree of depth at most R therefore has at most 4 to the R useful histories and at most 2 times 4 to the R nonzero successful compressed Kraus matrices. This is a bound for each tree, irrespective of how many seeds occur in the finite randomization.

Each of these compressed Kraus matrices is a contraction. The basis rows give |v_j| at most 1. Choosing sign rows separately for the real and imaginary parts gives sum_j |Re(v_j)| at most n and sum_j |Im(v_j)| at most n. Consequently sum_j |v_j| squared is at most 2n. The total coefficient energy of one tree is at most 4n times 4 to the R. Averaging over the seeds preserves this bound, while comparison on the basis-coordinate diagonal inputs gives total weighted coefficient energy q m. Hence q n is at most 4 times 4 to the R, or equivalently q is at most 4 times 4 to the R divided by n.

Given any proposed Rzero and qzero>0, choose an integer n at least 2 and strictly greater than 4 times 4 to the Rzero divided by qzero. Applying the claim to Phi_n requires q at least qzero and contradicts the bound. The conclusion concerns exact simulation with one ancillary qubit, arbitrary finite projective measurements, finite classical randomization and adaptive trees with a dimension-independent round bound. It leaves protocols whose depth grows with dimension and protocols whose success decreases with dimension outside this obstruction.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.FrameIndex`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.History`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.Measurement`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.Protocol`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.RandomizedProtocol`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.Workspace`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.branch`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.frame`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.frameNat`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.historyFintype`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.krausFrom`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.mixtureMap`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.succeeds`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/OneQubitAdaptiveSimulationRefutation.successfulMap`
- Dependency: [D5/S3/Quantum/Information/SeparableStateLocalUnitaryStabilizerObstruction](../Information/SeparableStateLocalUnitaryStabilizerObstruction.md)
- Dependency: [D5/S3/Quantum/Matrix/RecordCapacity](../Matrix/RecordCapacity.md)
- Dependency: [D5/S3/QuantumBounds/MerminMeasurementDependence/Model](../../QuantumBounds/MerminMeasurementDependence/Model.md)
- Dependency: [D5/S3/Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate](../../Weil/BurnolGram/QuantitativeMultiOrbitWeilNegativeCertificate.md)
