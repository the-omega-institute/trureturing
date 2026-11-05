# The Bajnok–Beatty sharp maximum for radius at least three

## Abstract

The exact maximum order, including an actual finite noncyclic product attaining it.

**Definition 1.1 (The natural maximum expression).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySharpMaximum.MaximumOrder`

*Formalization.* `D5/S3/FiniteGroups/BajnokBeattySharpMaximum.MaximumOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

For every natural s, MaximumOrder(s) is 2s² when 2s+1 is prime; otherwise it is 2s²+2s−(p²−1)/2, where p is the least prime factor of 2s+1. The expression is in natural numbers, with natural subtraction and division. The maximum theorem below applies only to s ≥ 3. In that range the composite arithmetic proves that neither subtraction truncates and that the correction (p²−1)/2 is an integer at least four.

**Theorem 1.2 (Universal upper bound and exact attainment).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattySharpMaximum.sharp_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattySharpMaximum.sharp_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

For every natural s ≥ 3, every additive commutative group G in any universe with Finite G, and every a,b in G, assume G is noncyclic, a ≠ b, and every g in G has a representation g=x•a+y•b for integers x,y with |x|+|y| ≤ s. Then Nat.card G ≤ MaximumOrder(s) and, literally in natural arithmetic, Nat.card G ≤ 2s²+2s−4. Moreover, there exist natural c ≥ 2 and k ≥ 1 and distinct a,b in ZMod c × ZMod(c k) such that this product is noncyclic and finite, the same signed radius-s cover holds for every element, and its cardinality equals MaximumOrder(s). The existential assertion supplies the group, its actual pair, noncyclicity, finiteness, cover and exact cardinality together.

The upper proof consumes BajnokBeattyFiniteUpper.finite_noncyclic_upper and splits on primality of 2s+1. Its composite doubled-cardinality estimate becomes the displayed natural maximum through an exact nontruncation identity. In the prime case the attaining group is ZMod s × ZMod(2s), with pair (1,1),(0,1). In the composite case write 2s+1=p(2t+1), where p is its least prime factor and t ≥ 1. The attaining group is ZMod p × ZMod(2pt(t+1)), with pair (1,t),(1,t+1); here c=p and k=2t(t+1). Twice its cardinality equals (2s+1)²−p².

The explicit lower families and their reflection mechanism are the known lower direction of Bajnok–Beatty, arXiv:2406.04045v1, Theorem 1.7. To verify the actual covers, two diagonal relation vectors (A,B),(A,−B) with positive A,B and A+B ≤ 2s+1 reduce every integer coefficient pair to one of radius at most s: first take remainders into [0,A) × [−B,B), then, if necessary, reflect by the diagonal relation on the same side. Integer integrality preserves the odd boundary 2s+1. Explicit surjectivity and the relations transport these representatives to every product element. This is a formal assembly of the literal Conjecture 1.6 maximum in the stated v1 scope; no current literature novelty or priority is claimed. The separate radius-two exception is outside this theorem.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySharpMaximum.MaximumOrder`
- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattySharpMaximum.sharp_maximum`
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyFiniteUpper](BajnokBeattyFiniteUpper.md)
