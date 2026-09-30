# The one-bit bound of the double CGLMP game

## Abstract

For every d >= 2, two parallel copies of the CGLMP_d game have one-bit classical bound 12 when one bit is sent from Alice to Bob, and also when it is sent from Bob to Alice; the truncations to the inputs {00, 01, 11} x {00, 01, 11} and {00, 01, 11} x {00, 11} have local bounds 7 and 4. These are the conjecture and the two conjectured local bounds of I. Márton, E. Bene, P. Diviánszky and T. Vértesi (arXiv:2308.10771), who verified them up to d = 10 and d = 20.

**Definition 1.1 (Inputs of the double game).**

$$Inp = \operatorname{Fin}\left(2\right) \times \operatorname{Fin}\left(2\right)$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.Inp` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

An input of the double game is the pair of input bits (x, x') of the two copies; outputs are pairs in Fin d x Fin d.

**Definition 1.2 (Winning one copy).**

$$\operatorname{copyWins}\left(x, y, a, b\right) \Leftrightarrow (((x = 0) \land \left((y = 0) \land (b \le a)\right)) \lor \left(((x = 0) \land \left((y = 1) \land (a \le b)\right)) \lor \left(((x = 1) \land \left((y = 0) \land (a < b)\right)) \lor ((x = 1) \land \left((y = 1) \land (b \le a)\right))\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.copyWins` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

Eq. (cglmpineq) of the paper: CGLMP_d = P(A_0 >= B_0) + P(A_0 <= B_1) + P(A_1 < B_0) + P(A_1 >= B_1), read as a game won on inputs (x, y) and outputs (a, b) in the four listed cases.

**Definition 1.3 (Winning the double game).**

$$\operatorname{wins}\left(X, Y, A, B\right) \Leftrightarrow ((\operatorname{copyWins}\left(X_{1}, Y_{1}, A_{1}, B_{1}\right)) \land (\operatorname{copyWins}\left(X_{2}, Y_{2}, A_{2}, B_{2}\right)))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.wins` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

Two copies are played in parallel; the double game is won when both copies are won.

**Definition 1.4 (The Bell expression).**

$$\operatorname{bell}\left(XS, YS, P\right) = \sum_{X \in XS} \sum_{Y \in YS} \sum_{A} \sum_{B} [\operatorname{wins}\left(X, Y, A, B\right)] \cdot P\left(X, Y, A, B\right)$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.bell` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

The Bell expression CGLMP_d tensor CGLMP_d restricted to the inputs XS x YS: the total probability of winning, where [wins] is 1 when the double game is won and 0 otherwise.

**Definition 1.5 (Response distributions).**

$$\operatorname{IsResponse}\left(r\right) \Leftrightarrow ((\forall A \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; \operatorname{Measurable}\left((t \mapsto r\left(t, A\right))\right)) \land \left((\forall t \in \mathbb{R},\; \forall A \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; 0 \le r\left(t, A\right)) \land (\forall t \in \mathbb{R},\; \sum_{A} r\left(t, A\right) = 1)\right))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsResponse` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

A conditional distribution of an output given the hidden value t: measurable in t, nonnegative and normalised.

**Definition 1.6 (Local behaviours).**

$$\operatorname{IsLocal}\left(d, P\right) \Leftrightarrow (\exists \mu : \operatorname{Measure}\left(\mathbb{R}\right), (\operatorname{IsProbabilityMeasure}\left(\mu\right)) \land (\exists p_{A}, p_{B} : Inp \to \mathbb{R} \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R}, (\forall X \in Inp,\; \operatorname{IsResponse}\left(\left(p_{A}\right)\left(X\right)\right)) \land \left((\forall Y \in Inp,\; \operatorname{IsResponse}\left(\left(p_{B}\right)\left(Y\right)\right)) \land (\forall X \in Inp,\; \forall Y \in Inp,\; \forall A \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; \forall B \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; P\left(X, Y, A, B\right) = \int \left(p_{A}\right)\left(X, t, A\right) \cdot \left(p_{B}\right)\left(Y, t, B\right) d\mu(t))\right)))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsLocal` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

Eq. (P_LHV): the hidden variable has an arbitrary probability distribution mu on the real line, and each party answers with a response distribution depending on its own input and t.

**Definition 1.7 (One bit from Alice to Bob).**

$$\operatorname{IsOneBitAB}\left(d, P\right) \Leftrightarrow (\exists \mu : \operatorname{Measure}\left(\mathbb{R}\right), (\operatorname{IsProbabilityMeasure}\left(\mu\right)) \land (\exists p_{A} : Inp \to \mathbb{R} \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R}, \exists l : Inp \to \mathbb{R} \to Bool, \exists p_{B} : Inp \to Bool \to \mathbb{R} \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R}, (\forall X \in Inp,\; \operatorname{IsResponse}\left(\left(p_{A}\right)\left(X\right)\right)) \land \left((\forall X \in Inp,\; \operatorname{Measurable}\left(l\left(X\right)\right)) \land \left((\forall Y \in Inp,\; \forall m \in Bool,\; \operatorname{IsResponse}\left(\left(p_{B}\right)\left(Y, m\right)\right)) \land (\forall X \in Inp,\; \forall Y \in Inp,\; \forall A \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; \forall B \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; P\left(X, Y, A, B\right) = \int \left(p_{A}\right)\left(X, t, A\right) \cdot \left(p_{B}\right)\left(Y, l\left(X, t\right), t, B\right) d\mu(t))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsOneBitAB` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

Eq. (P_LHV1bit): in addition Alice sends a bit l(X, t), measurable in t, and Bob's response depends on it.

**Definition 1.8 (One bit from Bob to Alice).**

$$\operatorname{IsOneBitBA}\left(d, P\right) \Leftrightarrow (\exists \mu : \operatorname{Measure}\left(\mathbb{R}\right), (\operatorname{IsProbabilityMeasure}\left(\mu\right)) \land (\exists p_{A} : Inp \to Bool \to \mathbb{R} \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R}, \exists l : Inp \to \mathbb{R} \to Bool, \exists p_{B} : Inp \to \mathbb{R} \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R}, (\forall X \in Inp,\; \forall m \in Bool,\; \operatorname{IsResponse}\left(\left(p_{A}\right)\left(X, m\right)\right)) \land \left((\forall Y \in Inp,\; \operatorname{Measurable}\left(l\left(Y\right)\right)) \land \left((\forall Y \in Inp,\; \operatorname{IsResponse}\left(\left(p_{B}\right)\left(Y\right)\right)) \land (\forall X \in Inp,\; \forall Y \in Inp,\; \forall A \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; \forall B \in \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right),\; P\left(X, Y, A, B\right) = \int \left(p_{A}\right)\left(X, l\left(Y, t\right), t, A\right) \cdot \left(p_{B}\right)\left(Y, t, B\right) d\mu(t))\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsOneBitBA` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

The same with the bit l(Y, t) sent from Bob to Alice; the paper lists this game as bidirectional.

**Definition 1.9 (The inputs of the truncations).**

$$symInputs = \{(0, 0), (0, 1), (1, 1)\}$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.symInputs` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

The inputs {00, 01, 11} kept by both truncations.

**Definition 1.10 (Bob's inputs of the asymmetric truncation).**

$$asymInputs = \{(0, 0), (1, 1)\}$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.asymInputs` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

Bob's inputs {00, 11} of the asymmetric truncation.

**Definition 1.11 (The conjecture and the two conjectured local bounds).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; (2 \le d) \Rightarrow \left((\operatorname{IsGreatest}\left(\{v \mid \exists P \in Inp \to Inp \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R},\; (\operatorname{IsOneBitAB}\left(d, P\right)) \land (\operatorname{bell}\left(univ, univ, P\right) = v)\}, 12\right)) \land \left((\operatorname{IsGreatest}\left(\{v \mid \exists P \in Inp \to Inp \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R},\; (\operatorname{IsOneBitBA}\left(d, P\right)) \land (\operatorname{bell}\left(univ, univ, P\right) = v)\}, 12\right)) \land \left((\operatorname{IsGreatest}\left(\{v \mid \exists P \in Inp \to Inp \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R},\; (\operatorname{IsLocal}\left(d, P\right)) \land (\operatorname{bell}\left(symInputs, symInputs, P\right) = v)\}, 7\right)) \land (\operatorname{IsGreatest}\left(\{v \mid \exists P \in Inp \to Inp \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right) \to \mathbb{R},\; (\operatorname{IsLocal}\left(d, P\right)) \land (\operatorname{bell}\left(symInputs, asymInputs, P\right) = v)\}, 4\right))\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.claim` (`✓ std3`).

*Citation.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

For every d >= 2: the one-bit bound of the double game is 12 in both directions, the local bound of the truncation to {00, 01, 11} x {00, 01, 11} is 7, and that of the truncation to {00, 01, 11} x {00, 11} is 4. Each bound is the greatest value of the Bell expression over the class.

**Theorem 1.12 (Proof of the three bounds).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.result` (`✓ std3`). ∎

*Resolves.* `Problems/marton-2023-double-cglmp-one-bit-bound` (proved) by `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"marton-2023-double-cglmp-one-bit-bound","declaration_gid":"D5/S3/Quantum/Information/DoubleCglmpOneBitBound.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* István Márton; Erika Bene; Péter Diviánszky; Tamás Vértesi (2023). *Beating one bit of communication with and without quantum pseudo-telepathy*. DOI: [10.48550/arXiv.2308.10771](https://doi.org/10.48550/arXiv.2308.10771). URL: <https://arxiv.org/abs/2308.10771v1>.

*Commentary.*

Take inputs U, V of Alice whose bits in one copy are 0 and 1, and inputs W, Z of Bob whose bits in that copy are 0 and 1. The four winning conditions of that copy would give a_U <= b_Z <= a_V < b_W <= a_U, so they cannot all hold: in every such rectangle {U, V} x {W, Z} on which Bob answers alike, some cell is lost. A kernel-checked count over the Boolean patterns of won cells shows that three inputs of one party that send the same message lose at least four of their twelve cells, and two such inputs lose at least two of their eight; splitting Alice's (or Bob's) inputs by the message they send, at most 12 of the 16 cells are won, and at most 7 and 4 in the truncations. For a fixed hidden value the Bell expression is linear in each response distribution, so replacing each by a best output does not decrease it; the value at each t is therefore at most the deterministic bound, and integrating over mu gives the bound for the class. Deterministic strategies with outputs 0 and 1 and a point mass attain 12, 12, 7 and 4, for every d >= 2.

## References

- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.Inp`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsLocal`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsOneBitAB`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsOneBitBA`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.IsResponse`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.asymInputs`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.bell`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.claim`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.copyWins`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.result`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.symInputs`
- Truth anchor: `D5/S3/Quantum/Information/DoubleCglmpOneBitBound.wins`
