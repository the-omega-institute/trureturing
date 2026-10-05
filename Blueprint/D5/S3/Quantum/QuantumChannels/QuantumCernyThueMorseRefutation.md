# The Thue-Morse prefix 01101001 needs more than one qubit

## Abstract

Lee, Lee and Kjos-Hanssen (arXiv:2609.40154) define the quantum Cerny complexity qc(w) of a binary word w as the least dimension d for which two quantum channels on d x d density matrices and a start state make w the unique shortest synchronizing word, and conjecture that the Thue-Morse prefix 01101001 has qc = 2. No qubit instance has this word as its unique shortest synchronizing word, so the conjecture fails. Combined with the authors' upper bound qc(w) <= 3, which is proved in the paper and not formalized here, the value is 3.

**Definition 1.1 (The channel of a word).**

$$\forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \forall rho : \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), (\operatorname{applyWord}\left(A, [], rho\right) = rho) \land (\forall a : \operatorname{Fin}\left(2\right), \forall u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \operatorname{applyWord}\left(A, a :: u, rho\right) = \operatorname{applyWord}\left(A, u, \operatorname{mapState}\left(A\left(a\right), rho\right)\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.applyWord` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The letters act left to right: the empty word leaves the state unchanged, and the word a :: u first applies the channel of the letter a, then the channel of u. The channels are the completely positive trace-preserving maps on d x d matrices and the states are the positive semidefinite trace-one matrices.

**Definition 1.2 (The reachable set).**

$$\forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \forall rho_0 : \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{reachable}\left(A, rho_0\right) = \ \{\operatorname{applyWord}\left(A, u, rho_0\right) \mid u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right)\ \}$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.reachable` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The reachable set is the set of images of the start state under the channels of all words.

**Definition 1.3 (Synchronizing words).**

$$\forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \forall rho_0 : \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \forall w : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), (\operatorname{Synchronizing}\left(A, rho_0, w\right)) \Leftrightarrow (\exists rho_1 : \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \forall rho \in \operatorname{reachable}\left(A, rho_0\right), \operatorname{applyWord}\left(A, w, rho\right) = rho_1)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.Synchronizing` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

A word synchronizes the instance when its channel is constant on the reachable set.

**Definition 1.4 (Unique shortest synchronizing word).**

$$\forall d : \mathbb{N}, \forall A : \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \forall rho_0 : \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \forall w : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), (\operatorname{UniqueShortestSync}\left(A, rho_0, w\right)) \Leftrightarrow ((\operatorname{Synchronizing}\left(A, rho_0, w\right)) \land (\forall u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), (|u| \le |w|) \Rightarrow ((u \ne w) \Rightarrow (\neg \operatorname{Synchronizing}\left(A, rho_0, u\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.UniqueShortestSync` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The word w synchronizes and no other word of length at most |w| does.

**Definition 1.5 (Instances of dimension d).**

$$\forall d : \mathbb{N}, \forall w : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), (\operatorname{HasInstance}\left(d, w\right)) \Leftrightarrow (\exists A : \operatorname{Fin}\left(2\right) \to \operatorname{QuantumChannel}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right)\right), \exists rho_0 : \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{UniqueShortestSync}\left(A, rho_0, w\right))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.HasInstance` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Some pair of channels on d x d matrices and some start state have w as their unique shortest synchronizing word.

**Definition 1.6 (The quantum Cerny complexity).**

$$\forall w : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \operatorname{qc}\left(w\right) = \operatorname{sInf}\left(\ \{d : \mathbb{N} \mid (1 \le d) \land (\operatorname{HasInstance}\left(d, w\right))\ \}\right)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.qc` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The least dimension d at least 1 with such an instance, as the infimum of a set of natural numbers.

**Definition 1.7 (The Thue-Morse prefix).**

$$thueMorsePrefix = [0, 1, 1, 0, 1, 0, 0, 1]$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.thueMorsePrefix` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

The first eight letters of the Thue-Morse word.

**Definition 1.8 (The conjecture).**

$$(claim) \Leftrightarrow (\operatorname{qc}\left(thueMorsePrefix\right) = 2)$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.claim` (`✓ std3`).

*Citation.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Open problem 1 of the paper: the Thue-Morse prefix has quantum Cerny complexity 2.

**Definition 1.9 (The linear map of a word).**

$$\forall K, V : \operatorname{Type}\left(\right), (((\operatorname{Field}\left(K\right)) \land (\operatorname{AddCommGroup}\left(V\right))) \land (\operatorname{Module}\left(K, V\right))) \Rightarrow (\forall f : \operatorname{Fin}\left(2\right) \to \operatorname{End}\left(K, V\right), (\operatorname{wordComp}\left(f, []\right) = \operatorname{id}) \land (\forall a : \operatorname{Fin}\left(2\right), \forall u : \operatorname{List}\left(\operatorname{Fin}\left(2\right)\right), \operatorname{wordComp}\left(f, a :: u\right) = \operatorname{wordComp}\left(f, u\right) \circ f\left(a\right)))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.wordComp` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

For two linear maps f(0), f(1) of a vector space V (an additive commutative group with a K-module structure) over a field K, the empty word gives the identity and the word a :: u gives the map of u after f(a).

**Theorem 1.10 (A dimension lemma for the Thue-Morse prefix).**

$$\forall K, V : \operatorname{Type}\left(\right), ((((\operatorname{Field}\left(K\right)) \land (\operatorname{AddCommGroup}\left(V\right))) \land (\operatorname{Module}\left(K, V\right))) \land (\operatorname{FiniteDimensional}\left(K, V\right))) \Rightarrow (\forall f : \operatorname{Fin}\left(2\right) \to \operatorname{End}\left(K, V\right), ((\operatorname{dim}\left(K, V\right) \le 3) \land (\operatorname{wordComp}\left(f, [0, 1, 1, 0, 1, 0, 0, 1]\right) = 0)) \Rightarrow (((\operatorname{wordComp}\left(f, [0, 1, 1, 0, 1]\right) = 0) \lor (\operatorname{wordComp}\left(f, [0, 1, 0, 0, 1]\right) = 0)) \lor ((\operatorname{wordComp}\left(f, [1, 1, 0, 1, 0, 0, 1]\right) = 0) \lor (\operatorname{wordComp}\left(f, [0, 1, 1, 0, 1, 0, 0]\right) = 0))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.mortal_thueMorse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

Let P, Q and T be the maps of 01101, 01 and 001, so that the map of 01101001 is T after P, and suppose that this map vanishes while the maps of 01101, 01001, 1101001 and 0110100 are all nonzero. The image of P lies in the image of Q. If the two images had equal dimension they would coincide; then for each x there is y with Q x = P y, so T Q x = T P y = 0 and the map of 01001, which is T after Q, would vanish. Hence the image of Q has larger dimension than the image of P, which is at least 1 because P is nonzero. The map f(0) is not surjective, since otherwise the map of 1101001 would vanish: the map of 01101001 is the map of 1101001 after f(0). So the image of Q, the image of the image of f(0) under f(1), has dimension at most 2, hence exactly 2. The image of Q lies in the image of f(1); if they coincided, then for each x there would be y with f(1) x = Q y, and the map of 1101001, which is the map of 101001 after f(1), would send x to the map of 01101001 applied to y, which is 0. So f(1) has rank 3, it is injective, and the map of 0110100 vanishes because f(1) after it is the map of 01101001.

**Theorem 1.11 (The conjecture fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lee-kjoshanssen-2026-quantum-cerny-thue-morse` (refuted) by `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lee-kjoshanssen-2026-quantum-cerny-thue-morse","declaration_gid":"D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pui Hang Lee, Pui Yee Lee and Bjørn Kjos-Hanssen (2026). *Quantum Černý complexity of binary words*. URL: <https://arxiv.org/abs/2609.40154>.

*Commentary.*

If the complexity were 2, the set defining it would contain 2, giving a qubit instance with 01101001 as unique shortest synchronizing word. Let V be the complex span of the differences of reachable states. A word synchronizes exactly when the linear map of its channel vanishes on V, and each channel maps V into itself. The differences of states have trace zero, so V lies in the span of three traceless 2 x 2 matrices and has dimension at most 3. Applying the dimension lemma to the two channels restricted to V shows that one of 01101, 01001, 1101001, 0110100 synchronizes, although each is shorter than 01101001.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.HasInstance`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.Synchronizing`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.UniqueShortestSync`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.applyWord`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.mortal_thueMorse`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.qc`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.reachable`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.result`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.thueMorsePrefix`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/QuantumCernyThueMorseRefutation.wordComp`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
