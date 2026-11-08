# Finite-word balance

## Abstract

Every word has exactly card(A)^(k+1) preimages under an arbitrary surjective finite-alphabet integer block rule.

Let A be any finite alphabet in any universe, k a natural number, and h an arbitrary rule on windows of length k+2. The native integer code sends x to i ↦ h(j ↦ x(i+j)). Surjectivity refers to all integer configurations. The result uses no permutation condition on either endpoint, and imposes no support or periodicity restriction.

**Definition 1.1 (Apply a rule to a finite word).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\\forall k: \mathbb{N},\\\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\forall n: \mathbb{N},\\\forall p: (\operatorname{Fin}(n + k + 1) \to A),\\\forall i: \operatorname{Fin}(n),\\\operatorname{wordMap}(h, p, i) = \operatorname{h}((j: \operatorname{Fin}(k + 2) \mapsto \operatorname{p}(\operatorname{val}(i) + \operatorname{val}(j))))\end{aligned}$$

*Formalization.* `D5/S1/Dynamics/Symbolic/SurjectiveWordBalance.wordMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source word has length n+k+1 and its image has length n. In the displayed window, p(val(i)+val(j)) means evaluation at the unique Fin(n+k+1) index with that natural value. The bounds i<n and j<k+2 prove that the index is in range.

**Theorem 1.2 (Every finite output fiber has the same exact size).**

$$\begin{aligned}\forall u: \operatorname{Universe}(),\forall A: \operatorname{Type}(u),\\{}[\operatorname{Finite}(A)],\\\forall k: \mathbb{N},\\\forall h: ((\operatorname{Fin}(k + 2) \to A) \to A),\\\operatorname{Function.Surjective}(\operatorname{BipermutativeLift.code}(h)) \Rightarrow\\\forall n: \mathbb{N},\\\forall w: (\operatorname{Fin}(n) \to A),\\\operatorname{Nat.card}(\{p: (\operatorname{Fin}(n + k + 1) \to A) \mid \forall i: \operatorname{Fin}(n), \operatorname{h}((j: \operatorname{Fin}(k + 2) \mapsto \operatorname{p}(\operatorname{val}(i) + \operatorname{val}(j)))) = \operatorname{w}(i)\}) = \operatorname{Nat.card}(A)^{k + 1}\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Symbolic/SurjectiveWordBalance.surjective_word_balance` (`✓ std3`). ∎

*Citation.* Benjamin Hellouin de Menibus, Ville Salo, and Ilkka Törmä (2025). *Symbol Frequencies in Surjective Cellular Automata*. DOI: [10.48550/arXiv.2504.06058](https://doi.org/10.48550/arXiv.2504.06058). URL: <https://arxiv.org/html/2504.06058v2>.

*Commentary.*

For every universe u, every A : Type(u) with Finite(A), every natural k, every local rule h with Function.Surjective(BipermutativeLift.code(h)), every natural n and every word w : Fin(n) → A, the subtype of source words satisfying all n overlapping local equations has cardinality card(A)^(k+1). The telescope includes empty and singleton alphabets and n=0. There is no supplied balance or fiber certificate and no lower bound on card(A).

Write r=k+1 and L=n+r. Surjectivity gives native finite-difference preinjectivity by the Garden-of-Eden theorem. For a nonempty alphabet, concatenate m independently chosen source words from one fiber and insert them into a constant integer configuration. Each of the m length-n output blocks is the prescribed w. The remaining affected outputs form m+1 gaps, each of length r. Recording these gaps is injective: equal records give equal complete images, and preinjectivity identifies the inserted configurations and hence all chosen words. If the fiber size is t and q=card(A), this yields t^m ≤ q^(r(m+1)) for every m. If t>q^r, the unbounded powers of t/q^r contradict that estimate. Thus every fiber has size at most q^r. All q^(n+r) source words partition into q^n fibers. Their upper bounds sum to q^(n+r), so each fiber attains its bound. For an empty alphabet, the positive source length makes each source fiber empty; the same exact statement covers n=0.

The cited Section 2 states this classical balance property for a forward neighborhood [0,r]. The parameter correspondence is r=k+1. For a nonempty finite alphabet, dividing the count q^r by the q^(n+r) equally likely input words gives cylinder probability q^(-n), the uniform product-law preservation consequence. A conditional source law requires a separate probability construction. No probability assertion on an empty alphabet and no literature novelty are claimed.

## References

- Truth anchor: `D5/S1/Dynamics/Symbolic/SurjectiveWordBalance.surjective_word_balance`
- Truth anchor: `D5/S1/Dynamics/Symbolic/SurjectiveWordBalance.wordMap`
- Dependency: [D5/S1/Dynamics/Symbolic/GardenOfEden](GardenOfEden.md)
