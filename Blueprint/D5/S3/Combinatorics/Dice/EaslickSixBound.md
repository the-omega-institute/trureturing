# EaslickSixBound

## Abstract

The complete dice conjecture follows from an exhaustive six-face upper bound and uniform longer cycles.

**Definition 1.1 (Arbitrary finite graph rank certificate checker).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)], \forall V \in \operatorname{List}\left(A\right), E \in (A \to (A \to \mathit{Bool})), r \in (A \to \mathit{Nat}), F \in (\mathit{Nat} \to \operatorname{List}\left(A\right)), W \in (\mathit{Nat} \to (A \times (A \times A))), b \in \mathit{Nat},\; \operatorname{checkRank}\left(V, E, r, F, W, b\right) = \mathit{true} \Leftrightarrow \left(\forall d \in A,\; d \in V \Rightarrow \left(\left(\left(\left(d \in F\left(r\left(d\right)\right) \land \operatorname{length}\left(\operatorname{dedup}\left(F\left(r\left(d\right)\right)\right)\right) = \operatorname{length}\left(F\left(r\left(d\right)\right)\right)\right) \land \operatorname{length}\left(F\left(r\left(d\right)\right)\right) \le b + 1\right) \land \left(\forall x \in A,\; \left(x \in V \land E\left(d, x\right) = \mathit{true}\right) \Rightarrow r\left(x\right) \le r\left(d\right)\right)\right) \land \left(\operatorname{length}\left(F\left(r\left(d\right)\right)\right) \le b \lor \left(\left(\left(\operatorname{fst}\left(W\left(r\left(d\right)\right)\right) \in F\left(r\left(d\right)\right) \land \operatorname{fst}\left(\operatorname{snd}\left(W\left(r\left(d\right)\right)\right)\right) \in F\left(r\left(d\right)\right)\right) \land \operatorname{fst}\left(W\left(r\left(d\right)\right)\right) \ne \operatorname{fst}\left(\operatorname{snd}\left(W\left(r\left(d\right)\right)\right)\right)\right) \land \left(\forall x \in A,\; x \in F\left(r\left(d\right)\right) \Rightarrow \left(\left(E\left(\operatorname{fst}\left(W\left(r\left(d\right)\right)\right), x\right) = \mathit{true} \Rightarrow x = \operatorname{snd}\left(\operatorname{snd}\left(W\left(r\left(d\right)\right)\right)\right)\right) \land \left(E\left(\operatorname{fst}\left(\operatorname{snd}\left(W\left(r\left(d\right)\right)\right)\right), x\right) = \mathit{true} \Rightarrow x = \operatorname{snd}\left(\operatorname{snd}\left(W\left(r\left(d\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Dice/EaslickSixBound.checkRank` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

Input consists of any finite vertex list, an executable Boolean edge function, a natural rank function, finite rank fibers, a collision triple for each rank, and a proposed bound b. For every input vertex the checker tests membership in its supplied fiber, absence of duplicates, capacity at most b+1, and weak rank decrease on every input edge. Each fiber must either have size at most b or supply two distinct member vertices whose every internal outgoing edge has the same target. These are executable checks, not assumed graph laws. The checker may reject certificates for graphs whose cycles nevertheless satisfy the bound; only soundness is asserted.

In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries.

**Theorem 1.2 (General rank checker soundness).**

$$\forall A \in \mathit{Type},\; [\operatorname{DecidableEq}\left(A\right)], [\operatorname{Inhabited}\left(A\right)], \forall V \in \operatorname{List}\left(A\right), E \in (A \to (A \to \mathit{Bool})), r \in (A \to \mathit{Nat}), F \in (\mathit{Nat} \to \operatorname{List}\left(A\right)), W \in (\mathit{Nat} \to (A \times (A \times A))), b \in \mathit{Nat},\; \forall c \in \operatorname{List}\left(A\right),\; \left(\left(\left(\left(\operatorname{checkRank}\left(V, E, r, F, W, b\right) = \mathit{true} \land \operatorname{Nodup}\left(c\right)\right) \land c \ne \operatorname{nil}\left(\right)\right) \land c \subseteq V\right) \land \operatorname{IsChain}\left(\lambda (u:A) \mapsto \lambda (z:A) \mapsto E\left(u, z\right) = \mathit{true}, \operatorname{append}\left(c, \operatorname{singleton}\left(\operatorname{head}\left(c\right)\right)\right)\right)\right) \Rightarrow \operatorname{length}\left(c\right) \le b$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.checkRank_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For an arbitrary decidable inhabited vertex type and all checker inputs, a successful Boolean check bounds the length of every nonempty simple closed edge chain contained in the input vertex list by b. The proof derives constancy of rank around the cycle, containment in one rank fiber, and the capacity bound. If the capacity is b+1 and a longer cycle existed, it would exhaust that fiber and force equal successors at two distinct positions, contradicting successor injectivity. No law of the graph is a hypothesis beyond the executable check and the given cycle's defining conditions.

In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries.

**Theorem 1.3 (Actual first rank checker input).**

$$\operatorname{checkRank}\left(\mathit{dice6}, \lambda (d:\operatorname{List}\left(\mathit{Nat}\right)) \mapsto \lambda (e:\operatorname{List}\left(\mathit{Nat}\right)) \mapsto \operatorname{decide}\left(\operatorname{winCount}\left(d, e\right) = 19\right), \mathit{rank6}, \mathit{fiber6}, \mathit{cuts6}, 6\right) = \mathit{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.sixRank_check` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

The complete recursive enumeration of six-face dice, exact score-19 Boolean edges, retained rank and fiber tables, and the two collision triples pass the arbitrary-input checker with bound six by kernel reduction. This is the actual computed first instance. Every numeric and checking premise is discharged. six_cycle_bound consumes checkRank_sound applied to this successful check, and S_six and conjecture_one consume that universal conclusion.

In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries.

**Theorem 1.4 (The global six-face upper bound).**

$$\forall k \in \mathit{Nat},\; \operatorname{HasCycle}\left(6, k\right) \Rightarrow k \le 6$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.six_cycle_bound` (`✓ std3`). ∎

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

For every natural k, HasCycle(6,k) implies k at most six. A complete recursive enumeration includes all 462 sorted six-face dice with labels from one through six, including repetitions and the standard die. Every score-19 edge weakly decreases the certified rank. A closed cycle therefore has one rank and lies in its entire rank fiber. All fibers have at most seven elements. In each seven-element fiber, two distinct vertices have the same unique internal successor. A seven-cycle would exhaust that fiber, contradicting injectivity of the cyclic successor operation on distinct vertices. The certificate is checked by Lean kernel reduction; its rank data are a witness, never an assumed law.

In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries.

**Theorem 1.5 (The attained six-face maximum).**

$$\operatorname{S}\left(6\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.S_six` (`✓ std3`). ∎

*Citation.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

S(6) holds: an explicit six-cycle attains the global upper bound of six. The upper bound applies to every simple directed cycle in the full graph at the true least attainable strict-win probability above one half.

In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries.

**Theorem 1.6 (The complete Easlick conjecture).**

$$\operatorname{S}\left(6\right) \land \left(\forall n \in \mathit{Nat},\; 7 \le n \Rightarrow \left(\neg \operatorname{S}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one` (`✓ std3`). ∎

*Resolves.* `Problems/easlick-2026-minimal-advantage-cycle-conjecture-one` (proved) by `D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"easlick-2026-minimal-advantage-cycle-conjecture-one","declaration_gid":"D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Terry Easlick (2026). *Computer-assisted results for n-sided non-transitive dice taking face values in [n]*. URL: <https://arxiv.org/abs/2610.40321v1>.

*Commentary.*

The complete proposition is S(6) and, for every natural n at least seven, not S(n). Natural n faithfully represents the source integer range n at least three. Dice are all nondecreasing lists of n labels in the interval from one through n. Repeated faces and the standard tuple remain included. Strict-win probability is unconditional on the uniform independent product of face indices. The attained minimum is proved, not taken from the author parity formula. S quantifies over all longer simple cycles, with no finite cutoff.

In these formulas, at is zero-based list indexing, length and dedup are list length and duplicate removal, head is Lean head!, fst and snd are product projections, and List subset means membership inclusion. dice6, rank6, fiber6 and cuts6 are the private Lean inputs; decide converts the displayed decidable proposition to Bool. The checker definitions are characterized by equality to the Boolean value true, including empty-input behavior. All quantifiers include their full carrier types and anonymous instance dictionaries.

## References

- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.S_six`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.checkRank`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.checkRank_sound`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.conjecture_one`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.sixRank_check`
- Truth anchor: `D5/S3/Combinatorics/Dice/EaslickSixBound.six_cycle_bound`
- Dependency: [D5/S3/Combinatorics/Dice/EaslickPaddedCycles](EaslickPaddedCycles.md)
