# Noncommuting deformed Jucys--Murphy operators on the cyclic orbit

## Abstract

Coulter and Do's b-deformed Jucys--Murphy operators fail to commute on the cyclic orbit X(6). The word J_6 J_6 J_5 J_4 J_3 applied to the identity pair partition gives unequal coefficients after J_2 J_4 and J_4 J_2.

**Definition 1.1 (Pair partitions).**

$$\forall k : \mathbb{N}, \operatorname{P}\left(k\right) = \{p : \operatorname{Fin}\left(2 \cdot k\right) \to \operatorname{Fin}\left(2 \cdot k\right) \mid (\forall x : \operatorname{Fin}\left(2 \cdot k\right), p\left(p\left(x\right)\right) = x) \land (\forall x : \operatorname{Fin}\left(2 \cdot k\right), p\left(x\right) \ne x)\}$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.P` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

A pair partition is encoded by its fixed-point-free involutive partner map. Its two-element orbits are its unordered pairs. Fin(2k) uses labels 0 through 2k-1, shifted down by one from the paper's labels 1 through 2k. The displayed set is a subtype. Type in the formulas permits an arbitrary Lean universe.

**Definition 1.2 (Consecutive identity pairs).**

$$\forall k : \mathbb{N}, \forall x : \operatorname{Fin}\left(2 \cdot k\right), \operatorname{val}\left(\operatorname{val}\left(\operatorname{e}\left(k\right)\right)\left(x\right)\right) = \operatorname{ite}\left(\operatorname{mod}\left(\operatorname{val}\left(x\right), 2\right) = 0, \operatorname{val}\left(x\right) + 1, \operatorname{natSub}\left(\operatorname{val}\left(x\right), 1\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.e` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

The identity pair partition is (1 2 | 3 4 | ... | 2k-1 2k) in the paper's labels. Here val extracts the partner map from a pair partition, or the natural-number label from a Fin element, according to its argument. The functions natSub and mod denote natural-number subtraction and remainder; natSub is truncated at zero. ite(c,t,f) returns t when c holds and f otherwise.

**Definition 1.3 (Transposition action).**

$$\forall k : \mathbb{N}, \forall a : \operatorname{Fin}\left(2 \cdot k\right), \forall c : \operatorname{Fin}\left(2 \cdot k\right), \forall p : \operatorname{P}\left(k\right), \forall x : \operatorname{Fin}\left(2 \cdot k\right), \operatorname{val}\left(\operatorname{act}\left(a, c, p\right)\right)\left(x\right) = \operatorname{swap}\left(a, c\right)\left(\operatorname{val}\left(p\right)\left(\operatorname{swap}\left(a, c\right)\left(x\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.act` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Page 8: "the pair {a, b} appears in the pair partition m if and only if the pair {σ(a), σ(b)} appears in the pair partition σ · m". Relabelling by the transposition swapping a and c is conjugation of the partner map. swap(a,c) denotes the involutive permutation of Fin(2k).

**Definition 1.4 (Alternating walk).**

$$\forall k : \mathbb{N}, \forall p : \operatorname{P}\left(k\right), \forall x : \operatorname{Fin}\left(2 \cdot k\right), (\operatorname{walk}\left(p, x, 0\right) = x) \land (\forall n : \mathbb{N}, \operatorname{walk}\left(p, x, n + 1\right) = \operatorname{ite}\left(\operatorname{mod}\left(n, 2\right) = 0, \operatorname{val}\left(\operatorname{e}\left(k\right)\right)\left(\operatorname{walk}\left(p, x, n\right)\right), \operatorname{val}\left(p\right)\left(\operatorname{walk}\left(p, x, n\right)\right)\right))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.walk` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Starting at x, the walk first follows an identity edge, then a matching edge, and repeats these two edge colours. The recurrence uses the natural-number remainder modulo two.

**Definition 1.5 (Charge from the cycle maximum).**

$$\forall k : \mathbb{N}, \forall p : \operatorname{P}\left(k\right), \forall x : \operatorname{Fin}\left(2 \cdot k\right), \operatorname{charge}\left(p, x\right) = \operatorname{snd}\left(\operatorname{foldl}\left((\lambda s : \mathbb{N}\times \operatorname{Bool}, \lambda n : \mathbb{N}, \operatorname{ite}\left(\operatorname{fst}\left(s\right) < \operatorname{val}\left(\operatorname{walk}\left(p, x, n\right)\right), (\operatorname{val}\left(\operatorname{walk}\left(p, x, n\right)\right), \operatorname{beq}\left(\operatorname{mod}\left(n, 2\right), 0\right)), s\right)), (\operatorname{val}\left(x\right), \operatorname{true}), \operatorname{range}\left(2 \cdot k\right)\right)\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.charge` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Definition 4.1, page 21: "To each vertex v ∈ Γ(m), assign a charge q(v) ∈ {+, −} such that the vertex with the largest label in each cycle is assigned + and such that each edge in Γ(m) is incident to one vertex with positive change and one vertex with negative charge." The walk implementation records the first occurrence of the maximum in its first 2k positions. A strict increase replaces the stored pair; ties retain it. true denotes positive charge, beq is Boolean equality, range(N) is [0,...,N-1], and foldl applies its update in this order. fst and snd project a pair. An alternating walk of an even component visits that component and repeats with even period. The maximum therefore has positive charge and both edge colours reverse charge. This interpretation of the algorithm is mathematical exposition, rather than an additional theorem asserted here.

**Definition 1.6 (Transposition weight on the output matching).**

$$\forall K : \operatorname{Type}, [\operatorname{One}\left(K\right)] \forall b : K, \forall k : \mathbb{N}, \forall p : \operatorname{P}\left(k\right), \forall a : \operatorname{Fin}\left(2 \cdot k\right), \forall c : \operatorname{Fin}\left(2 \cdot k\right), \operatorname{weight}\left(b, p, a, c\right) = \operatorname{ite}\left(\operatorname{charge}\left(p, a\right) = \operatorname{charge}\left(p, c\right), 1, b\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.weight` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Definition 4.1, page 21: "Set ω^(b)(m,n) = 1 if q(i) = q(j) and set ω^(b)(m,n) = b if q(i) ≠ q(j)." weight(b,p,a,c) is this rule restricted to the specified transposition (a c), with p as the first argument and act(a,c,p) as the second. The paper establishes independence of the transposition used. Only transposition-related pairs enter J, so the other cases of the full weight function are unnecessary here.

**Definition 1.7 (Coefficient form of the deformed operators).**

$$\forall K : \operatorname{Type}, [\operatorname{CommRing}\left(K\right)] \forall b : K, \forall k : \mathbb{N}, \forall i : \mathbb{N}, \forall w : \operatorname{P}\left(k\right) \to K, \forall p : \operatorname{P}\left(k\right), \operatorname{J}\left(b, k, i\right)\left(w, p\right) = \operatorname{ite}\left((0 < i) \land (i \le k), \sum_{a : \operatorname{Fin}\left(\operatorname{natSub}\left(2 \cdot i, 2\right)\right)} \operatorname{weight}\left(b, p, \operatorname{Fin.mk}\left(\operatorname{val}\left(a\right)\right), \operatorname{Fin.mk}\left(\operatorname{natSub}\left(2 \cdot i, 2\right)\right)\right) \cdot w\left(\operatorname{act}\left(\operatorname{Fin.mk}\left(\operatorname{val}\left(a\right)\right), \operatorname{Fin.mk}\left(\operatorname{natSub}\left(2 \cdot i, 2\right)\right), p\right)\right), 0\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.J` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Definition 5.1, page 33: "For k a positive integer, let 𝒱ₖ = ℂ(b)[𝒫ₖ] be the vector space with basis the set of pair partitions of {1, 2, …, 2k}. Define the b-deformed Jucys–Murphy operators 𝒥₁, 𝒥₂, …, 𝒥ₖ: 𝒱ₖ → 𝒱ₖ by 𝒥ᵢ(m) = ∑_(a=1)^(2i−2) ω^(b)((a 2i−1) · m, m) (a 2i−1) · m, where m ∈ 𝒫ₖ and ω^(b) is the weight function of Definition 4.1. We interpret the formula for i = 1 as 𝒥₁ = 0 and refer to these operators collectively as 𝒥-operators." The displayed formula gives the coefficient at output p. The unique contributing input for each transposition is act(a,2i-2,p), because the transposition is its own inverse. Charges thus belong to p. The map is linear over K. J is extended by zero outside 1 ≤ i ≤ k. The bounds and indices use natural subtraction. Fin.mk(r) constructs the element of Fin(2k) with natural label r, with bounds supplied by 0 < i <= k and a : Fin(2i-2).

**Definition 1.8 (Identity basis vector).**

$$\forall K : \operatorname{Type}, [\operatorname{Zero}\left(K\right)] [\operatorname{One}\left(K\right)] \forall k : \mathbb{N}, \forall p : \operatorname{P}\left(k\right), (\operatorname{single}\left(k\right)\left(p\right) : K) = \operatorname{ite}\left(p = \operatorname{e}\left(k\right), 1, 0\right)$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.single` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

The identity basis vector has coefficient one at e(k) and zero at every other matching. Since P(k) is finite, all coefficient functions correspond to finite linear combinations of the paper's basis.

**Definition 1.9 (Cyclic orbit of the generated algebra).**

$$\forall K : \operatorname{Type}, [\operatorname{CommRing}\left(K\right)] \forall b : K, \forall k : \mathbb{N}, \forall v : \operatorname{P}\left(k\right) \to K, (v \in \operatorname{X}\left(b, k\right)) \Leftrightarrow (\exists A : \operatorname{End}\left(K, \operatorname{P}\left(k\right) \to K\right), (A \in \operatorname{adjoin}\left(K, \operatorname{range}\left(\lambda i : \mathbb{N}, \operatorname{J}\left(b, k, i\right)\right)\right)) \land (A\left(\operatorname{single}\left(k\right)\right) = v))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.X` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Definition 5.3, page 34: "For k a positive integer, let 𝒳(k) = ⟨𝒥₁, 𝒥₂, …, 𝒥ₖ⟩ · 𝔢ₖ ⊆ 𝒱ₖ. That is, 𝒳(k) is the orbit of 𝔢ₖ under the action of the algebra of 𝒥-operators." adjoin is the unital K-subalgebra generated by the range of i ↦ J(b,k,i). The extra generators are zero, so the range over all natural indices generates the same algebra as indices 1 through k. X is a set of coefficient functions, described by the displayed membership equivalence.

**Definition 1.10 (Coulter--Do Conjecture 5.4(a)).**

$$(claim) \Leftrightarrow (\forall k : \mathbb{N}, (1 \le k) \Rightarrow (\forall m : \mathbb{N}, \forall n : \mathbb{N}, (1 \le m) \Rightarrow ((m \le n) \Rightarrow ((n \le k) \Rightarrow (\forall v : \operatorname{P}\left(k\right) \to \operatorname{RatFunc}\left(\mathbb{C}\right), (v \in \operatorname{X}\left(\operatorname{RatFunc.X}, k\right)) \Rightarrow (\operatorname{J}\left(\operatorname{RatFunc.X}, k, m\right)\left(\operatorname{J}\left(\operatorname{RatFunc.X}, k, n\right)\left(v\right)\right) = \operatorname{J}\left(\operatorname{RatFunc.X}, k, n\right)\left(\operatorname{J}\left(\operatorname{RatFunc.X}, k, m\right)\left(v\right)\right)))))))$$

*Formalization.* `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.claim` (`✓ std3`).

*Citation.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Conjecture 5.4(a), page 34: "The 𝒥-operators commute when restricted to 𝒳(k) — that is, 𝒥ₘ 𝒥ₙ (v) = 𝒥ₙ 𝒥ₘ (v) for 1 ⩽ m ⩽ n ⩽ k and for all v ∈ 𝒳(k)." The encoding quantifies over every positive natural k and all ordered indices in that interval. It uses K = RatFunc C, the rational-function field C(b), and b = RatFunc.X, an indeterminate. Operator equality on each v is equality of coefficient functions; b is never fixed to a complex number in the claim.

**Theorem 1.11 (Refutation on X(6)).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Coulter, Xavier; Do, Norman (2025). *From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*. DOI: [10.48550/arXiv.2506.04002](https://doi.org/10.48550/arXiv.2506.04002). URL: <https://arxiv.org/abs/2506.04002v1>.

*Commentary.*

Let v = J_6 J_6 J_5 J_4 J_3 e_6 and T = (1 5 | 2 7 | 3 9 | 4 11 | 6 10 | 8 12). The generating word places v in X(6). Coefficientwise ring-homomorphism transport embeds the integer-polynomial model into C(b), then evaluates its polynomial coefficients at 2. The T-coefficients of J_2 J_4 v and J_4 J_2 v evaluate to 78 and 81. Injectivity of the polynomial embedding shows that the original coefficients in C(b) cannot agree. A support invariant for increasing words and the forced partner at the top pair reduce the finite sums to a backward path.

## References

- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.J`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.P`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.X`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.act`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.charge`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.claim`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.e`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.result`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.single`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.walk`
- Truth anchor: `D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.weight`
