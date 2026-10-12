# Pure targets prevent general square-root savings

## Abstract

Pure-target quantum Cerny complexity grows linearly on constant binary words. The word consisting of m zeros has complexity m+1, so no uniform square-root bound holds.

**Definition 1.1 (Pure-output instances).**

$$\forall d \in \mathrm{Nat},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right),\; \operatorname{HasPureInstance}\left(d, w\right) \Leftrightarrow \left(\exists A \in \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \exists rho0 \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \exists P \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{UniqueShortestSync}\left(A, rho0, w\right) \land \left(\operatorname{IsPure}\left(P\right) \land \left(\forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{member}\left(rho, \operatorname{reachable}\left(A, rho0\right)\right) \Rightarrow \operatorname{applyWord}\left(A, w, rho\right) = P\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.HasPureInstance` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Two completely positive trace-preserving channels and a start density make w the unique shortest synchronizing word. Every reachable density has the same output P under w, and P equals the outer product of a vector with its adjoint. Since P has trace one, the vector has unit norm.

**Definition 1.2 (Pure-target complexity).**

$$\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right),\; \operatorname{qcPure}\left(w\right) = \operatorname{sInf}\left(\ \{d : \mathrm{Nat} \mid \operatorname{HasPureInstance}\left(d, w\right)\ \}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.qcPure` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Take the infimum of the natural dimensions admitting a pure-output instance. For constant words the set is nonempty, so this infimum is attained.

**Definition 1.3 (The proposed square-root saving).**

$$claim \Leftrightarrow \left(\exists C \in \mathrm{Real},\; \exists m0 \in \mathrm{Nat},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right),\; m0 \le \operatorname{length}\left(w\right) \Rightarrow \operatorname{castReal}\left(\operatorname{qcPure}\left(w\right)\right) \le C \cdot \operatorname{sqrt}\left(\operatorname{castReal}\left(\operatorname{length}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.claim` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

There would be a real constant C and a natural length threshold such that every binary word beyond that threshold has pure-target complexity at most C times the square root of its length.

**Theorem 1.4 (A realization for every constant word).**

$$\forall m \in \mathrm{Nat},\; \operatorname{HasPureInstance}\left(m + 1, \operatorname{replicate}\left(m, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.constant_word_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

In dimension m+1 start at the last basis projector. The zero channel has Kraus operators taking basis vector j to its predecessor, with zero fixed; the one channel is the identity. Their Kraus completeness gives trace preservation and complete positivity. A word with z zeros sends basis projector j to max(j-z,0). All basis projectors are reachable, and synchronization is equivalent to z being at least m. Only the all-zero word of length m synchronizes among words of length at most m, and its output is the first basis projector.

**Theorem 1.5 (The pure-output dimension obstruction).**

$$\forall d \in \mathrm{Nat},\; \forall m \in \mathrm{Nat},\; \forall A \in \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right),\; \forall rho0 \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \forall P \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \left(\operatorname{UniqueShortestSync}\left(A, rho0, \operatorname{replicate}\left(m, 0\right)\right) \land \left(\operatorname{IsPure}\left(P\right) \land \left(\forall rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{member}\left(rho, \operatorname{reachable}\left(A, rho0\right)\right) \Rightarrow \operatorname{applyWord}\left(A, \operatorname{replicate}\left(m, 0\right), rho\right) = P\right)\right)\right) \Rightarrow m + 1 \le d$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.pure_constant_word_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Let the all-zero word of length m be the unique shortest synchronizing word, with pure common output P. Invariance of reachable states under the zero channel implies that P is fixed. The positive functional measuring mass in the orthogonal complement of P vanishes precisely on nonnegative scalar multiples of P. The vanishing vectors of its iterates form subspaces. Decomposing a positive matrix into rank-one terms shows that equality of successive subspaces propagates to the next pair. For m greater than zero, some reachable state fails to reach P at m-1 steps, so every pair up to level m differs. These m strict increases start from a nonzero subspace and force d to be at least m+1, using only positivity and trace preservation of the zero channel. When m is zero, the existence of a density already forces d to be at least one.

**Theorem 1.6 (The exact constant-word complexity).**

$$\forall m \in \mathrm{Nat},\; \operatorname{qcPure}\left(\operatorname{replicate}\left(m, 0\right)\right) = m + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.constant_word_complexity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The construction gives dimension m+1. Positivity gives increasing subspaces of vectors whose rank-one matrices reach the pure output line after j zero steps. Equality of successive subspaces propagates to all later levels. For m greater than zero, failure to synchronize at m-1 forces m strict increases from a nonzero initial subspace, requiring dimension at least m+1. At m equal to zero, the existence of a density requires positive dimension.

**Theorem 1.7 (The general saving fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lee-kjoshanssen-2026-quantum-cerny-pure-target` (refuted) by `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lee-kjoshanssen-2026-quantum-cerny-pure-target","declaration_gid":"D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Given a constant C and a length threshold, choose a natural m larger than C squared, the threshold and one. The exact value m+1 exceeds C times the square root of m. Hence no such bound holds for all sufficiently long binary words.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.HasPureInstance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.constant_word_complexity`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.constant_word_realization`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.pure_constant_word_dimension`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.qcPure`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyPureTargetRefutation.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation](QuantumCernyThueMorseRefutation.md)
