# The classical value of the odd polygon game

## Abstract

For every odd P at least three, the polygon game's optimal classical winning probability is one minus F(P minus one) divided by two to the power P.

**Definition 1.1 (Disjoint edges of a cycle).**

$$\forall (P: \mathbb{N}), (\forall (M: \operatorname{Finset}\left(\operatorname{Fin}\left(P\right)\right)), ((\operatorname{IsMatching}\left(P, M\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(P\right)), ((i \in M) \Rightarrow (\neg (\operatorname{finRotate}\left(P, i\right) \in M))))))$$

*Formalization.* `D5/S3/QuantumBounds/PolygonGameClassicalValue.IsMatching` (`✓ std3`).

*Citation.* Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi (2023). *Playing nonlocal games with phases of quantum matter*. DOI: [10.1103/PhysRevB.107.045412](https://doi.org/10.1103/PhysRevB.107.045412). URL: <https://arxiv.org/abs/2206.11252v2>.

*Commentary.*

Edge i joins i to finRotate P i. A finite set M is a matching when it never contains both an edge and its cyclic successor. For P at least three this says precisely that no two selected edges share a vertex. Section 4.1, Rules of the polygon game (ArxivResub.tex, lines 636–658), indexes the polygon conditions by these matchings.

**Definition 1.2 (The input covered by a matching).**

$$\forall (P: \mathbb{N}), (\forall (M: \operatorname{Finset}\left(\operatorname{Fin}\left(P\right)\right)), (\operatorname{matchingInput}\left(P, M\right) = \lambda (i: \operatorname{Fin}\left(P\right)) \mapsto (\operatorname{decide}\left((i \in M) \lor (\operatorname{Equiv.symm}\left(\operatorname{finRotate}\left(P\right)\right)\left(i\right) \in M)\right))))$$

*Formalization.* `D5/S3/QuantumBounds/PolygonGameClassicalValue.matchingInput` (`✓ std3`).

*Citation.* Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi (2023). *Playing nonlocal games with phases of quantum matter*. DOI: [10.1103/PhysRevB.107.045412](https://doi.org/10.1103/PhysRevB.107.045412). URL: <https://arxiv.org/abs/2206.11252v2>.

*Commentary.*

The input bit at i is true exactly when the edge starting at i or the edge ending at i belongs to M. This is the endpoint input specified in Section 4.1 (ArxivResub.tex, lines 653–655). The function is defined for every finite edge set, whether or not it is a matching.

**Definition 1.3 (All winning conditions).**

$$\forall (P: \mathbb{N}), (\forall (s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))), (\forall (x: (\operatorname{Fin}\left(P\right)) \to (\operatorname{Bool})), ((\operatorname{wins}\left(P, s, x\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(P\right)), ((\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.fst}\left(s\left(i, x\left(i\right)\right)\right)\right)\right): \operatorname{ZMod}\left(2\right)) + (\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(s\left(i, x\left(i\right)\right)\right)\right)\right)\right): \operatorname{ZMod}\left(2\right)) + (\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(s\left(i, x\left(i\right)\right)\right)\right)\right)\right): \operatorname{ZMod}\left(2\right)) = (0: \operatorname{ZMod}\left(2\right)))) \land ((\sum_{i: \operatorname{Fin}\left(P\right)} ((\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(s\left(i, x\left(i\right)\right)\right)\right)\right)\right): \operatorname{ZMod}\left(2\right))) = (0: \operatorname{ZMod}\left(2\right))) \land (\forall (M: \operatorname{Finset}\left(\operatorname{Fin}\left(P\right)\right)), ((\operatorname{IsMatching}\left(P, M\right)) \Rightarrow ((\operatorname{matchingInput}\left(P, M\right) = x) \Rightarrow (\sum_{i \in M} ((\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.fst}\left(s\left(i, \operatorname{true}\right)\right)\right)\right): \operatorname{ZMod}\left(2\right)) + (\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(s\left(\operatorname{finRotate}\left(P, i\right), \operatorname{true}\right)\right)\right)\right)\right): \operatorname{ZMod}\left(2\right))) + \sum_{i \in \operatorname{Finset.filter}\left(\lambda (i: \operatorname{Fin}\left(P\right)) \mapsto (\operatorname{matchingInput}\left(P, M, i\right) = \operatorname{false}), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(P\right)\right))\right)} ((\operatorname{Nat.cast}\left(\operatorname{Bool.toNat}\left(\operatorname{Prod.fst}\left(s\left(i, \operatorname{false}\right)\right)\right)\right): \operatorname{ZMod}\left(2\right))) = (\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(M\right)\right): \operatorname{ZMod}\left(2\right)))))))))))$$

*Formalization.* `D5/S3/QuantumBounds/PolygonGameClassicalValue.wins` (`✓ std3`).

*Citation.* Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi (2023). *Playing nonlocal games with phases of quantum matter*. DOI: [10.1103/PhysRevB.107.045412](https://doi.org/10.1103/PhysRevB.107.045412). URL: <https://arxiv.org/abs/2206.11252v2>.

*Commentary.*

A deterministic strategy s assigns a Boolean triple to each player and each Boolean input. The triple is associated to the right, so its coordinates are obtained by Prod.fst, Prod.fst after Prod.snd, and Prod.snd after Prod.snd. Each triple has even parity and the middle coordinates have even total parity. For every matching producing x, sum the first output at each selected edge's initial vertex, the third output at its terminal vertex, and the first output on input false at every uncovered vertex. This sum equals the matching's cardinality in ZMod 2. The empty, one-edge and two-edge matchings give Conditions 3, 4 and 5; larger matchings give Condition 6 (ArxivResub.tex, lines 629–655). Inputs coming from no matching retain the two parity conditions. The middle output is allowed to depend on the input, so both local response tables are included. Bool.toNat converts each bit to a natural number; every subsequent Nat.cast, including the cardinality cast, is displayed with its target type.

**Definition 1.4 (Uniform inputs and shared randomness).**

$$\forall (P: \mathbb{N}), (\forall (\mu: ((\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))) \to (\mathbb{R})), (\operatorname{winProbability}\left(P, \mu\right) = \sum_{s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))} (\frac{\mu\left(s\right) \cdot (\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\operatorname{wins}\left(P, s\right), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(P\right)) \to (\operatorname{Bool})\right))\right)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}})))$$

*Formalization.* `D5/S3/QuantumBounds/PolygonGameClassicalValue.winProbability` (`✓ std3`).

*Citation.* Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi (2023). *Playing nonlocal games with phases of quantum matter*. DOI: [10.1103/PhysRevB.107.045412](https://doi.org/10.1103/PhysRevB.107.045412). URL: <https://arxiv.org/abs/2206.11252v2>.

*Commentary.*

For each deterministic response table, count its winning inputs and divide by the number of all Boolean inputs, two to the power P. Weight this fraction by μ and sum over all response tables. When μ is nonnegative and sums to one, this is the classical winning probability with shared randomness and uniform inputs. The definition itself accepts arbitrary real weights. This is the winning probability used in Section 4.1, Classical winning probabilities (ArxivResub.tex, lines 684–717).

**Definition 1.5 (The Fibonacci value).**

$$\operatorname{claim} = (\forall (P: \mathbb{N}), ((\operatorname{Odd}\left(P\right)) \Rightarrow ((3 \le P) \Rightarrow ((\forall (\mu: ((\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))) \to (\mathbb{R})), ((\forall (s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))), ((0: \mathbb{R}) \le \mu\left(s\right))) \Rightarrow ((\sum_{s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))} (\mu\left(s\right)) = (1: \mathbb{R})) \Rightarrow (\operatorname{winProbability}\left(P, \mu\right) \le (1: \mathbb{R}) - \frac{(\operatorname{Nat.cast}\left(\operatorname{Nat.fib}\left((P - 1)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}})))) \land (\exists (s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))), (\frac{(\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\operatorname{wins}\left(P, s\right), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(P\right)) \to (\operatorname{Bool})\right))\right)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}} = (1: \mathbb{R}) - \frac{(\operatorname{Nat.cast}\left(\operatorname{Nat.fib}\left((P - 1)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}}))))))$$

*Formalization.* `D5/S3/QuantumBounds/PolygonGameClassicalValue.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi (2023). *Playing nonlocal games with phases of quantum matter*. DOI: [10.1103/PhysRevB.107.045412](https://doi.org/10.1103/PhysRevB.107.045412). URL: <https://arxiv.org/abs/2206.11252v2>.

*Commentary.*

For every odd P at least three, every nonnegative normalized distribution on deterministic strategies has winning probability at most one minus F(P minus one) divided by two to the power P, and a deterministic strategy attains that value. Nat.fib has F(1) = F(2) = 1. The source gives the lower bound and conjectures its tightness (ArxivResub.tex, lines 703–717); the displayed proposition includes both the upper bound for shared randomness and an optimal deterministic strategy. The subtraction P minus one takes place in the natural numbers before applying Nat.fib, and the Fibonacci number is then cast to the reals.

**Theorem 1.6 (The sharp upper bound).**

$$\forall (P: \mathbb{N}), ((\operatorname{Odd}\left(P\right)) \Rightarrow ((3 \le P) \Rightarrow ((\forall (\mu: ((\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))) \to (\mathbb{R})), ((\forall (s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))), ((0: \mathbb{R}) \le \mu\left(s\right))) \Rightarrow ((\sum_{s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))} (\mu\left(s\right)) = (1: \mathbb{R})) \Rightarrow (\operatorname{winProbability}\left(P, \mu\right) \le (1: \mathbb{R}) - \frac{(\operatorname{Nat.cast}\left(\operatorname{Nat.fib}\left((P - 1)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}})))) \land (\exists (s: (\operatorname{Fin}\left(P\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool} \times (\operatorname{Bool} \times \operatorname{Bool}))))), (\frac{(\operatorname{Nat.cast}\left(\operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\operatorname{wins}\left(P, s\right), (\operatorname{Finset.univ}: \operatorname{Finset}\left((\operatorname{Fin}\left(P\right)) \to (\operatorname{Bool})\right))\right)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}} = (1: \mathbb{R}) - \frac{(\operatorname{Nat.cast}\left(\operatorname{Nat.fib}\left((P - 1)\right)\right): \mathbb{R})}{(2: \mathbb{R})^{P}})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/PolygonGameClassicalValue.result` (`✓ std3`). ∎

*Resolves.* `Problems/bulchandani-burnell-sondhi-2023-polygon-game-classical-value` (proved) by `D5/S3/QuantumBounds/PolygonGameClassicalValue.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bulchandani-burnell-sondhi-2023-polygon-game-classical-value","declaration_gid":"D5/S3/QuantumBounds/PolygonGameClassicalValue.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vir B. Bulchandani, Fiona J. Burnell, S. L. Sondhi (2023). *Playing nonlocal games with phases of quantum matter*. DOI: [10.1103/PhysRevB.107.045412](https://doi.org/10.1103/PhysRevB.107.045412). URL: <https://arxiv.org/abs/2206.11252v2>.

*Commentary.*

Fix an odd P at least three and a deterministic strategy. If a local triple has odd parity for one input bit at one player, all inputs having that bit lose, accounting for half of all inputs. If a middle output changes with the input, flipping that player's input is an involution that changes the total middle parity by one. It injects winning inputs into losing inputs, so at least half of all inputs lose. If every middle output is constant but their sum is odd, every input loses. The fact that F(P minus one) is smaller than half of the two to the power P inputs covers all these cases.

It remains to consider locally even triples with input-independent middle outputs bᵢ of even total parity. Write aᵢ and dᵢ for the first outputs on false and true, and cᵢ and eᵢ for the third outputs. Work in ZMod 2. Local parity gives cᵢ = aᵢ + bᵢ and eᵢ = dᵢ + bᵢ. Put A = Σᵢ aᵢ and tᵢ = aᵢ + dᵢ, and assign edge i the bit qᵢ = 1 + tᵢ + tᵢ₊₁ + bᵢ₊₁. Split the vertices into the initial and terminal vertices of M and its uncovered vertices. Substituting the local parity identities into the matching condition shows that it holds exactly when A + Σᵢ∈M qᵢ = 0. Thus this affine expression is the failure bit.

Summing the edge bits around the cycle cancels each tᵢ twice. The remaining sum is P + Σᵢ bᵢ = 1, because P is odd and the middle parity is even. Hence some edge j has qⱼ = 1.

Distinct matchings of an odd cycle have distinct endpoint inputs. Indeed, if M and N have the same covered vertices, let zᵢ be the integer difference of their edge indicators. At each vertex, equality of the covered-vertex indicators gives zᵢ + zᵢ₋₁ = 0, since a matching has at most one incident selected edge. The differences alternate in sign around the cycle; after the odd number P of steps, zᵢ equals its own negative. Every zᵢ is therefore zero, so M = N.

Consider matchings N containing none of the three edges j minus one, j and j plus one. These are exactly the matchings disjoint from both endpoints of j. The remaining P minus two vertices form a path, with P minus three possible edges. Number those edges consecutively, starting two positions after j. Choosing a matching is equivalent to a Boolean word of length P minus three with no adjacent true bits. The count of such words is F(P minus one).

For each such N, both N and N with j inserted are matchings. Their affine failure bits differ by qⱼ = 1, so at least one of their endpoint inputs loses. Choose N's input if it loses, and otherwise choose the input after insertion. This choice is injective: equal inputs on the same branch give equal matchings, and insertion can be reversed by removing j; inputs on opposite branches differ at vertex j. Thus at least F(P minus one) distinct inputs lose. Subtracting these losses from the two to the power P inputs and dividing by this positive denominator gives the deterministic upper bound.

To attain the bound, index players from zero to P minus one. Every player except the last outputs (true, true, false) on both inputs; the last outputs (false, false, false) on false and (true, false, true) on true. This is the source's strategy (ArxivResub.tex, lines 703–706). All local triples are even, the middle outputs are fixed and have even total parity, and A = 0. Exactly the edge from the last player to the first has edge bit one. Consequently a losing input must come from a matching containing this edge. Removing that edge leaves a matching disjoint from its endpoints, so there are at most F(P minus one) losing inputs. The universal lower bound gives the reverse inequality, hence exactly that many losses and the stated winning fraction.

Finally, the winning probability of a distribution is the finite weighted mean of the deterministic winning fractions. Nonnegative weights of total mass one preserve their common upper bound. Combining this upper bound with the deterministic strategy just described proves both parts of the proposition. The conclusion concerns uniform inputs and every odd P at least three; it makes no assertion about the quantum value, even polygons, or polygons inscribed in a larger game.

## References

- Truth anchor: `D5/S3/QuantumBounds/PolygonGameClassicalValue.IsMatching`
- Truth anchor: `D5/S3/QuantumBounds/PolygonGameClassicalValue.claim`
- Truth anchor: `D5/S3/QuantumBounds/PolygonGameClassicalValue.matchingInput`
- Truth anchor: `D5/S3/QuantumBounds/PolygonGameClassicalValue.result`
- Truth anchor: `D5/S3/QuantumBounds/PolygonGameClassicalValue.winProbability`
- Truth anchor: `D5/S3/QuantumBounds/PolygonGameClassicalValue.wins`
- Dependency: [D5/S0/Automata/TwoStateCertificateWidth](../../S0/Automata/TwoStateCertificateWidth.md)
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](../../S1/Words/AdmissibleWords/AdmissibleCount.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciRankEulerTail](../Arith/Robin/FibonacciRankEulerTail.md)
- Dependency: [D5/S3/Quantum/Information/BargmannImaginaryMaximizers](../Quantum/Information/BargmannImaginaryMaximizers.md)
