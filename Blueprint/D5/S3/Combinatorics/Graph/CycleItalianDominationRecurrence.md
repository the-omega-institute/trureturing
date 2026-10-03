# Italian dominating functions on cycles

## Abstract

The total number of Italian dominating functions on the labelled cycle C_n, for n at least three, satisfies a constant-coefficient recurrence of order five. Its first five values are 23, 60, 167, 467 and 1297. A bijection with closed sequences in a nine-state transfer matrix identifies the count with a power trace; a five-state factorization then supplies the recurrence.

**Definition 1.1 (The Italian condition).**

$$\forall (n : \mathbb{N}), \forall (f : \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(3\right)), (\operatorname{IsItalian}\left(n, f\right)) \Leftrightarrow (\forall (i : \operatorname{Fin}\left(n\right)), (f\left(i\right) = 0) \Rightarrow (2 \le \operatorname{val}\left(f\left(\left((\operatorname{finRotate}\left(n\right))^{-1}\right)\left(i\right)\right)\right) + \operatorname{val}\left(f\left(\operatorname{finRotate}\left(n\right)\left(i\right)\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.IsItalian` (`✓ std3`).

*Citation.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Shao and Zhao, Definition 2.1 (p. 5): "An Italian dominating function (IDF) on G = (V, E) is a function f : V → {0, 1, 2} such that for every v ∈ V with f(v) = 0, Σ_{u∈N(v)} f(u) ≥ 2. The weight of f is ω(f) = Σ_{v∈V} f(v)." The vertices are labelled by Fin n and the values by Fin 3. Write r_n = finRotate n; its inverse and itself are the cyclic predecessor and successor. For n ≥ 3 these are distinct and form exactly the open neighbourhood in SimpleGraph.cycleGraph n, so the displayed sum is the neighbourhood sum of Definition 2.1. For n < 3 the definition is a cyclic-word condition; no simple-cycle interpretation is asserted. The operator val takes a Fin 3 value to its natural-number value.

**Definition 1.2 (The total count).**

$$\forall (n : \mathbb{N}), \operatorname{a}\left(n\right) = \operatorname{card}\left(\operatorname{filter}\left(\operatorname{univ}\left(\right)_{(\operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(3\right))}, (f : \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(3\right)) \mapsto \operatorname{IsItalian}\left(n, f\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.a` (`✓ std3`).

*Citation.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Shao and Zhao, Definition 1.1 (p. 3): "where d_I(G, k) counts the Italian dominating functions of weight k." For n ≥ 3, a(n) is therefore Σ_k d_I(C_n, k): all labelled maps satisfying the Italian condition are counted once, without identifying rotations or reflections. In the displayed expression, univ is the finite set of all maps of the indicated type, filter selects those satisfying IsItalian, and card is the Finset cardinality. Section 2.1 (p. 5) states: "A cycle graph C_n (n ≥ 3) has vertices v_1, v_2, …, v_n and edges v_i v_{i+1} for i = 1, …, n − 1 plus the edge v_n v_1." Labelling i by v_{i+1} gives the cycle used here.

**Definition 1.3 (The recurrence and its initial values).**

$$(claim) \Leftrightarrow ((\forall (n : \mathbb{N}), (3 \le n) \Rightarrow ((\operatorname{a}\left(n + 5\right) : \mathbb{Z}) = 2 \cdot (\operatorname{a}\left(n + 4\right) : \mathbb{Z}) + 2 \cdot (\operatorname{a}\left(n + 3\right) : \mathbb{Z}) + (\operatorname{a}\left(n + 2\right) : \mathbb{Z}) - (\operatorname{a}\left(n + 1\right) : \mathbb{Z}) - (\operatorname{a}\left(n\right) : \mathbb{Z}))) \land ((\operatorname{a}\left(3\right) = 23) \land ((\operatorname{a}\left(4\right) = 60) \land ((\operatorname{a}\left(5\right) = 167) \land ((\operatorname{a}\left(6\right) = 467) \land (\operatorname{a}\left(7\right) = 1297))))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Shao and Zhao, §9 (the section starts on p. 28; this bullet is on p. 29): "Several directions remain open for future work: … • Deriving a complete linear recurrence for the total count Σ_k d_I(C_n, k) using the transfer matrix formulation (the observed limiting ratio ≈ 2.7843 is the dominant eigenvalue of the corresponding transfer matrix)." The displayed proposition gives a recurrence for every n ≥ 3 and the five initial values that determine all subsequent terms. Every count in the recurrence is explicitly coerced from the natural numbers to the integers, so subtraction is integer subtraction; the initial equalities are in the natural numbers. The order here describes the supplied recurrence; minimality is not asserted by this proposition.

**Theorem 1.4 (A complete order-five recurrence).**

$$(\forall (n : \mathbb{N}), (3 \le n) \Rightarrow ((\operatorname{a}\left(n + 5\right) : \mathbb{Z}) = 2 \cdot (\operatorname{a}\left(n + 4\right) : \mathbb{Z}) + 2 \cdot (\operatorname{a}\left(n + 3\right) : \mathbb{Z}) + (\operatorname{a}\left(n + 2\right) : \mathbb{Z}) - (\operatorname{a}\left(n + 1\right) : \mathbb{Z}) - (\operatorname{a}\left(n\right) : \mathbb{Z}))) \land ((\operatorname{a}\left(3\right) = 23) \land ((\operatorname{a}\left(4\right) = 60) \land ((\operatorname{a}\left(5\right) = 167) \land ((\operatorname{a}\left(6\right) = 467) \land (\operatorname{a}\left(7\right) = 1297)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.result` (`✓ std3`). ∎

*Resolves.* `Problems/shao-zhao-2026-cycle-italian-domination-recurrence` (proved) by `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"shao-zhao-2026-cycle-italian-domination-recurrence","declaration_gid":"D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pingping Shao; Chengye Zhao (2026). *Counting Weight-k Italian Dominating Sets on Trees and Cycles*. DOI: [10.48550/arXiv.2610.00108](https://doi.org/10.48550/arXiv.2610.00108). URL: <https://arxiv.org/abs/2610.00108v1>.

*Commentary.*

Use pair states (a,b) in {0,1,2}². A transition from (a,b) to (b,c) is allowed exactly when b ≠ 0 or a+c ≥ 2. Mapping f to the sequence of pairs (f at the predecessor of i, f at i), and decoding the second coordinates, gives mutually inverse maps between Italian functions and closed state sequences. An induction expands a matrix power as a sum of path products; closing the paths gives the trace. The transition rows agree in the five groups {(0,0)}, {(1,0)}, {(2,0)}, {(*,1)}, {(*,2)}. Their indicator matrix R and representative-row matrix S satisfy T = R S and S R = Q, with Q having rows (0,0,0,0,1), (0,0,0,1,1), (1,0,0,1,1), (0,1,0,1,1), (0,0,1,1,1). Cyclicity of trace gives a(n) = trace(Q^n) for positive n. The identity Q^5 − 2Q^4 − 2Q^3 − Q^2 + Q + I = 0, multiplied by Q^n and traced, yields the recurrence. The traces of Q^3 through Q^7 give the five initial values.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.IsItalian`
- Truth anchor: `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.a`
- Truth anchor: `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/CycleItalianDominationRecurrence.result`
