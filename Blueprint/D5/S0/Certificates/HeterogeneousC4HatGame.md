# Heterogeneous C4 Hat Games

## Abstract

Explicit legal strategies win two heterogeneous four-cycle hat games.

The coordinates 0, 1, 2, 3 denote A, B, Z, Omega in that order. The undirected cycle is A-B-Z-Omega-A: A and Z each see B and Omega. The parameter functions h and g give the number of available colours and the exact number of distinct guesses at each vertex. Fin(n) consists of the integers from zero through n minus one.

McInnis, arXiv:2507.21487v1, Section 1.1 and Question 7.1.8(1), supplies the Czech game and the open question. The definitions below are this repository's coordinate representation of its C4 restriction; the two explicit winning strategies and their finite coverage proofs are repository constructions.

**Definition 1.1 (Legal local plans).**

$$\begin{aligned}\forall h, g: \operatorname{Fin}(4) \to Nat,\\\forall v, left, right: \operatorname{Fin}(4),\\\operatorname{LocalPlan}(h, g, v, left, right) = ((\operatorname{Fin}(\operatorname{h}(left)) \times \operatorname{Fin}(\operatorname{h}(right))) \to \{guesses: \operatorname{Finset}(\operatorname{Fin}(\operatorname{h}(v))) \mid \operatorname{card}(guesses) = \operatorname{g}(v)\}).\end{aligned}$$

*Formalization.* `D5/S0/Certificates/HeterogeneousC4HatGame.LocalPlan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input contains exactly the colours at left and right. The output is a finite subset of the vertex's own colour type, together with a proof that its cardinality is exactly g(v).

**Definition 1.2 (All four-vertex colourings).**

$$\begin{aligned}\forall h: \operatorname{Fin}(4) \to Nat,\\\operatorname{Coloring}(h) = \operatorname{Fin}(\operatorname{h}(0)) \times \operatorname{Fin}(\operatorname{h}(1)) \times \operatorname{Fin}(\operatorname{h}(2)) \times \operatorname{Fin}(\operatorname{h}(3)).\end{aligned}$$

*Formalization.* `D5/S0/Certificates/HeterogeneousC4HatGame.Coloring` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Cartesian product is associated to the right, as in Lean.

**Definition 1.3 (Legal C4 strategies).**

$$\begin{aligned}\forall h, g: \operatorname{Fin}(4) \to Nat,\\\operatorname{Strategy}(h, g) = \operatorname{LocalPlan}(h, g, 0, 1, 3) \times\\\operatorname{LocalPlan}(h, g, 1, 0, 2) \times \operatorname{LocalPlan}(h, g, 2, 1, 3) \times\\\operatorname{LocalPlan}(h, g, 3, 2, 0).\end{aligned}$$

*Formalization.* `D5/S0/Certificates/HeterogeneousC4HatGame.Strategy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product is associated to the right. Their ordered inputs are (B,Omega), (A,Z), (B,Omega), (Z,A).

**Definition 1.4 (Correct guesses at each vertex).**

$$\begin{aligned}\forall h, g: \operatorname{Fin}(4) \to Nat,\\\forall s: \operatorname{Strategy}(h, g),\\\forall c: \operatorname{Coloring}(h),\\\operatorname{GuessesCorrectly}(h, g, s, c) = [c.1 \in \operatorname{val}((s.1)((c.2.1, c.2.2.2))), c.2.1 \in \operatorname{val}((s.2.1)((c.1, c.2.2.1))),\\c.2.2.1 \in \operatorname{val}((s.2.2.1)((c.2.1, c.2.2.2))), c.2.2.2 \in \operatorname{val}((s.2.2.2)((c.2.2.1, c.1)))].\end{aligned}$$

*Formalization.* `D5/S0/Certificates/HeterogeneousC4HatGame.GuessesCorrectly` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The bracketed four-vector is the function on Fin(4) with these entries in coordinate order. Applying it at v selects entry v. The operator val forgets the cardinality proof in a local-plan output.

**Definition 1.5 (A strategy wins every colouring).**

$$\begin{aligned}\forall h, g: \operatorname{Fin}(4) \to Nat,\\\forall s: \operatorname{Strategy}(h, g),\\\operatorname{Wins}(h, g, s) \iff (\forall c: \operatorname{Coloring}(h), \exists v: \operatorname{Fin}(4), \operatorname{GuessesCorrectly}(h, g, s, c, v)).\end{aligned}$$

*Formalization.* `D5/S0/Certificates/HeterogeneousC4HatGame.Wins` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The strategy is fixed before the colouring is chosen. The correctly guessing vertex may depend on the colouring.

**Definition 1.6 (Existence of a winning strategy).**

$$\begin{aligned}\forall h, g: \operatorname{Fin}(4) \to Nat,\\\operatorname{Winnable}(h, g) \iff (\exists s: \operatorname{Strategy}(h, g), \operatorname{Wins}(h, g, s)).\end{aligned}$$

*Formalization.* `D5/S0/Certificates/HeterogeneousC4HatGame.Winnable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A game is winnable when some tuple of legal local plans wins every colouring.

**Example 1.7 (A strategy for hatness (3,4,4,3)).**

$$
\exists s: \operatorname{Strategy}((3, 4, 4, 3), (2, 1, 1, 1)), \operatorname{Wins}((3, 4, 4, 3), (2, 1, 1, 1), s)
$$

*Source.* Repository-derived.

*Commentary.*

The bound witness s is the private Lean strategy3443. Its A table has input Fin(4) times Fin(3) and returns two-element subsets of Fin(3). Its B table has input Fin(3) times Fin(4) and output Fin(4); its Z table has input Fin(4) times Fin(3) and output Fin(4); its Omega table has input Fin(4) times Fin(3) and output Fin(3). The B, Z, and Omega outputs become singleton subsets. The subtype proofs certify guessness (2,1,1,1), and the private coordinate coverage proposition is checked by kernel decide on all 144 colourings.

**Example 1.8 (A strategy for hatness (3,4,4,4)).**

$$
\exists s: \operatorname{Strategy}((3, 4, 4, 4), (2, 1, 1, 1)), \operatorname{Wins}((3, 4, 4, 4), (2, 1, 1, 1), s)
$$

*Source.* Repository-derived.

*Commentary.*

The bound witness s is the private Lean strategy3444. Its A table has input Fin(4) times Fin(4) and returns two-element subsets of Fin(3). Its B table has input Fin(3) times Fin(4) and output Fin(4); its Z table has input Fin(4) times Fin(4) and output Fin(4); its Omega table has input Fin(4) times Fin(3) and output Fin(4). The B, Z, and Omega outputs become singleton subsets. The subtype proofs certify guessness (2,1,1,1), and the private coordinate coverage proposition is checked by kernel decide on all 192 colourings.

**Theorem 1.9 (Two winning C4 instances).**

$$(\operatorname{Winnable}((3, 4, 4, 3), (2, 1, 1, 1))) \land (\operatorname{Winnable}((3, 4, 4, 4), (2, 1, 1, 1))).$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/HeterogeneousC4HatGame.c4_three_four_winnable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both conjuncts use source order A,B,Z,Omega and guessness (2,1,1,1). The first has hatness (3,4,4,3); the second has hatness (3,4,4,4). Each tuple denotes its coordinate function on Fin(4).

The proof supplies the two explicit legal strategies. At A the table entries are two-element subsets; at B, Z, and Omega the entries are single colours, used as singleton subsets. Kernel decide checks the two private coordinate coverage propositions on all 144 and 192 colourings respectively. The Boolean membership checks are proved equivalent to GuessesCorrectly.

This proves only the two positive C4 cases. The negative direction with hatness four at A has only external DRAT verification in the source-aligned probe; it has no kernel theorem here. No result is asserted for cycles with at least five vertices.

## References

- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.Coloring`
- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.GuessesCorrectly`
- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.LocalPlan`
- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.Strategy`
- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.Winnable`
- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.Wins`
- Truth anchor: `D5/S0/Certificates/HeterogeneousC4HatGame.c4_three_four_winnable`
