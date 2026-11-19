# Freeman's Upper-Limsup Density Bound Fails

## Abstract

A positive non-eventually-periodic sequence has 2-palindromic upper-limsup density one.

**Definition 1.1 (Finite rational continued fractions).**

$$(finiteCF([])=0) \land (\forall (a: \mathbb{N}), \forall (tail: List(\mathbb{N})), finiteCF(a::tail)=\operatorname{GenContFract}.\operatorname{convs}'((\langle (a: \mathbb{Q}), \operatorname{Stream}'.\operatorname{Seq}.\operatorname{ofList}(\operatorname{List}.\operatorname{map}(\operatorname{fun} (b: \mathbb{N}) \mapsto \langle 1, (b: \mathbb{Q})\rangle, tail))\rangle: GenContFract(\mathbb{Q})), \operatorname{List}.\operatorname{length}(tail)))$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.finiteCF` (`✓ std3`).

*Citation.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

Section 2 (page 2) writes: “Given i∈ℕ₀, a (rational) continued fraction is denoted by [a₀,a₁,…,aᵢ], where a₀∈ℕ₀ and, for each k such that 1≤k≤i, we have aₖ∈ℕ.” The rational evaluator is GenContFract.convs' at tail.length, with all partial numerators equal to one. The empty-list value zero is excluded from every qualifying prefix.

**Definition 1.2 (Finite m-palindromes).**

$$\forall (m: \mathbb{N}), \forall (U: List(\mathbb{N})), IsFiniteMPalindrome(m, U)\iff ((U\neq []) \land ((\forall (a: \mathbb{N}), a \in U \implies 0<a) \land (finiteCF(U)=(m: \mathbb{Q})\cdot finiteCF(\operatorname{List}.\operatorname{reverse}(U)))))$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.IsFiniteMPalindrome` (`✓ std3`).

*Citation.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

Section 2 (pages 2–3): “Given A=(a₀,…,aᵢ)∈ℕ*, the reversal of A is defined as Ã = (aᵢ,…,a₀). If there exists a number m∈ℕ such that [A]=m[Ã], we say that A is an m-palindrome, or m-palindromic.” Lists encode finite words. List.reverse reverses their digits; every digit and the length of a qualifying word are strictly positive.

**Definition 1.3 (Qualifying positive prefix lengths).**

$$\forall (m: \mathbb{N}), \forall (A: \mathbb{N} \to \mathbb{N}), \forall (n: \mathbb{N}), PrefixLength(m, A, n)\iff ((0<n) \land (IsFiniteMPalindrome(m, \operatorname{List}.\operatorname{ofFn}(\operatorname{fun} (i: Fin(n)) \mapsto A(val(i))))))$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.PrefixLength` (`✓ std3`).

*Citation.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

A prefix of length n consists of the digits A(0),…,A(n−1), formed by List.ofFn on Fin n. Section 2 (page 2): “For A∈𝒜*, we write |A| to denote the number of terms in A, and say that A has length |A|.” Thus the prefix ending at index i has length i+1.

**Definition 1.4 (Infinite m-palindromic sequences).**

$$\forall (m: \mathbb{N}), \forall (A: \mathbb{N} \to \mathbb{N}), IsMPalindromic(m, A)\iff \operatorname{Set}.\operatorname{Infinite}(\{n: \mathbb{N} | PrefixLength(m, A, n)\})$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.IsMPalindromic` (`✓ std3`).

*Citation.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

Section 2 (page 3): “In the case of an irrational continued fraction α=[A]=[a₀,a₁,…], we say that α (equivalently, A) is an m-palindrome, or m-palindromic, if there exist infinitely many indices i for which the prefix (a₀,…,aᵢ) is an m-palindrome.” Infinite sets of positive lengths express precisely this condition.

**Definition 1.5 (The upper-limsup density).**

$$\forall (m: \mathbb{N}), \forall (A: \mathbb{N} \to \mathbb{N}), density(m, A)=\operatorname{Filter}.\operatorname{limsup}(\operatorname{fun} (k: \mathbb{N}) \mapsto \frac{(\operatorname{Nat}.\operatorname{nth}(PrefixLength(m, A), k): \mathbb{R})}{(\operatorname{Nat}.\operatorname{nth}(PrefixLength(m, A), k+1): \mathbb{R})}, \operatorname{Filter}.\operatorname{atTop})$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.density` (`✓ std3`).

*Citation.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

Section 6 (page 8): “Given any irrational m-palindromic continued fraction α=[A], let {Pₖ(A)}ₖ₌₀⁺∞ denote a sequence of m-palindromic prefixes (a₀,…,aᵢₖ) for A such that, for each k∈ℕ, there is no index j such that iₖ₋₁<j<iₖ and for which (a₀,…,a_j) is an m-palindrome. Define the m-palindromic density of α to be the number” dₘ(α)=limsup_{k→+∞}|Pₖ(A)|/|Pₖ₊₁(A)|. Nat.nth enumerates every qualifying length increasingly; both lengths are cast to ℝ before division.

**Definition 1.6 (Conjecture 7.1, first sentence).**

$$claim\iff (\forall (m: \mathbb{N}), 0<m \implies \forall (A: \mathbb{N} \to \mathbb{N}), (\forall (n: \mathbb{N}), 0<A(n)) \implies IsMPalindromic(m, A) \implies \neg \operatorname{D5}.\operatorname{S1}.\operatorname{Words}.\operatorname{Complexity}.\operatorname{EventuallyPeriodicWord}(A) \implies density(m, A)\leq \frac{1}{\operatorname{Real}.\operatorname{goldenRatio}})$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.claim` (`✓ std3`).

*Citation.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

Conjecture 7.1 (page 10): “For m∈ℕ and A∈ℕ^ℕ₀ an m-palindromic sequence that is not eventually periodic, we have dₘ([A])≤1/φ. Furthermore, for r,s∈ℕ with r≠s, we have dₘ([F(m,r,s)])=1/φ.” Only the first sentence is asserted by claim. Lean ℕ includes zero, so m>0 and positivity of every digit are explicit. Eventual periodicity means ∃s p:ℕ, p>0 ∧ ∀t, A(s+t+p)=A(s+t). Real.goldenRatio is (1+√5)/2. The separate Fibonacci equality is left open.

**Theorem 1.7 (Density one refutes the upper bound).**

$$\neg (\forall (m: \mathbb{N}), 0<m \implies \forall (A: \mathbb{N} \to \mathbb{N}), (\forall (n: \mathbb{N}), 0<A(n)) \implies IsMPalindromic(m, A) \implies \neg \operatorname{D5}.\operatorname{S1}.\operatorname{Words}.\operatorname{Complexity}.\operatorname{EventuallyPeriodicWord}(A) \implies density(m, A)\leq \frac{1}{\operatorname{Real}.\operatorname{goldenRatio}})$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/palindromic-density` (refuted) by `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"palindromic-density","declaration_gid":"D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* David M. Freeman (2017). *Generalized Palindromic Continued Fractions*. DOI: [10.1216/RMJ-2018-48-1-219](https://doi.org/10.1216/RMJ-2018-48-1-219). URL: <https://arxiv.org/abs/1604.06755v2>.

*Commentary.*

Set m=2. Begin with the stage [4,2]; replace stage k by k+2 copies of it, then k+1 copies of [6,3], then k+2 further copies of stage k. The nested prefixes define a positive infinite sequence. Weighted transpose preserves the matrices of these stages and their powers, as in Freeman's Lemmas 3.1–3.2 and section-7 block substitution. Lengths (k+1)·length(stage k) and (k+2)·length(stage k) both qualify. The next length in the complete list is at most the latter, so arbitrarily late consecutive ratios are at least (k+1)/(k+2). Their upper limsup is one. Arbitrarily long [6,3] blocks followed by [4,2] exclude every eventual period. Since 1/Real.goldenRatio<1, the asserted universal upper bound fails. The finite computations establish no infinite conclusion.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.IsFiniteMPalindrome`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.IsMPalindromic`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.PrefixLength`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.claim`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.density`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.finiteCF`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/FreemanPalindromicDensityRefutation.result`
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](../../Words/Complexity/MorseHedlund.md)
