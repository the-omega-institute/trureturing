# Cyclic Refractory Quantum Generator

## Abstract

A finite quantum instrument reproduces every word of a residue-labelled refractory process.

**Theorem 1.1 (A completely positive channel with the exact classical word law).**

$$\forall Z: \operatorname{Type}, \operatorname{Fintype}(Z), \operatorname{DecidableEq}(Z),\\{}a, b: Z \to \mathbb{R}, e: \operatorname{Perm}(Z),\\{}(\forall z: Z, a(z)^{2} + b(z)^{2} = 1) \implies\\{}\exists C: \operatorname{QuantumChannel}(\operatorname{Fin}(2) \times Z, \operatorname{Fin}(2) \times Z),\\{}(\forall \rho: \operatorname{Matrix}(\operatorname{Fin}(2) \times Z, \operatorname{Fin}(2) \times Z, \mathbb{C}), \operatorname{matrix}(C(\operatorname{ofMatrix}(\rho))) = \sum_{x \in \operatorname{Bool}} \operatorname{branchK}(a, b, e, x) \cdot \rho \cdot \operatorname{adjoint}(\operatorname{branchK}(a, b, e, x))) \land\\{}\forall s: \operatorname{Fin}(2) \times Z, w: \operatorname{List}(\operatorname{Bool}),\\{}\operatorname{Tr}(\operatorname{wordK}(a, b, e, w) \cdot \operatorname{vecMulVec}(\operatorname{stateVec}(a, b, s), \operatorname{star}(\operatorname{stateVec}(a, b, s))) \cdot \operatorname{adjoint}(\operatorname{wordK}(a, b, e, w))) = \operatorname{complex}(\operatorname{classicalWordProbability}((z \mapsto b(z)^{2}), e, s, w)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/CyclicRefractoryGenerator.cyclic_refractory_generator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residue set is finite and decidable. The real amplitudes at each residue have squared sum one. The residue update is an arbitrary permutation; it need not consist of a single cycle. The Hilbert basis is indexed by a two-valued block coordinate and a residue.

In each block the free vector is (1,0), and the tail vector has coordinates (a(z),b(z)). The zero operator has rows (a(z),b(z)) and (0,0). The one operator in block z is the outer product of the tail vector at e(z) and the row (b(z),-a(z)); its output is shifted to residue e(z). These explicit operators are Kzero and Kone. The Boolean branchK chooses Kone for true and Kzero for false.

The zero branch maps the free vector to a(z) times that vector and maps the tail vector to the free vector. The one branch maps the free vector to b(z) times the next residue's tail vector and annihilates the tail vector. The corresponding classical weights are 1-p(z), p(z), 1 and 0, with p(z)=b(z) squared.

The stateVec function selects the free vector for block coordinate zero and the tail vector for block coordinate one. The wordK recursion uses identity for the empty word and multiplies the remaining word operator on the left of its first branch. The independently defined classicalWordProbability recursion multiplies the first transition weight by the probability of the remaining word from the updated classical state.

The channel is completely positive at every matrix amplification and preserves trace. In the formula, matrix converts its CStarMatrix output back to an ordinary matrix, ofMatrix converts its input, and star on vectors is entrywise conjugation. The word equality includes the empty word, impossible words and zero transition weights.

The proof first computes each one-step vector update. Induction on the word then gives the product of transition amplitudes and the final state vector. A second induction identifies its squared amplitude with the classical recursive probability. Unit vector normalization converts this identity to a branch trace. The existing finite Kraus channel construction supplies complete positivity and trace preservation.

Quantum simulation of stochastic processes is an established subject. This theorem gives an explicit finite refractory family. It does not establish a minimum memory dimension, an entropy advantage, a stationary initial law or a physical implementation.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/CyclicRefractoryGenerator.cyclic_refractory_generator`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
