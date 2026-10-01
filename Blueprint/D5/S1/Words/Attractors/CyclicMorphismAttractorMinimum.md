# String attractors of cyclically maximal morphisms

## Abstract

Original cyclic morphism prefixes have the unrestricted attractor minimum of Conjecture 42.

Gheeraert, Romana and Stipulanti's Conjecture 42 concerns the original alphabet and every positive prefix length. Coefficients may vanish except at the first and last letters. Cyclic maximality is weak: equal rotations, proper powers, and unary primitive roots are included. The source is arXiv:2302.13647v2; published suppliers and the proved finite bridges are identified individually.

**Definition 1.1 (Original substitution).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicMorphism`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicMorphism` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every natural k, proof hk of 0 < k, coefficient function c : Fin k → Nat and letter a : Fin k, cyclicMorphism hk c a is the list consisting of c(a) copies of the original letter 0 followed by the singleton letter a+1 if a.val+1 < k. Otherwise it is exactly c(a) copies of 0. The latter branch contains no appended letter. This is the substitution in Definition 2 of arXiv:2302.13647v2.

**Definition 1.2 (Periodic coefficient digit).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicDigit`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicDigit` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k, c : Fin k → Nat and a : Fin k, cyclicDigit c a equals c(a)-1 when a.val+1=k, and c(a) otherwise. Subtraction is natural-number subtraction. This represents the coefficient word in Proposition 34(3); positivity of the last coefficient makes natural decrement agree with the source integer decrement.

**Definition 1.3 (Original cyclic phase).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicNext`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicNext` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k and a : Fin k, cyclicNext hk a is the original letter with value (a.val+1) modulo k, with its Fin k bound certified by hk.

**Definition 1.4 (Weak cyclic maximum).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.CyclicMaximal`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.CyclicMaximal` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k and c : Fin k → Nat, form the length-k list d=List.ofFn(cyclicDigit c), in increasing original-letter order. CyclicMaximal c means: for every natural rotation amount r, d.rotate r is lexicographically less than or equal to d. Equality is allowed; no primitivity condition is imposed. This is the condition in Proposition 34(3).

**Definition 1.5 (Literal substitution iterate).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicWord`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicWord` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k, c : Fin k → Nat and natural n, cyclicWord hk c n is morphismPower (cyclicMorphism hk c) n [0], a list of original Fin k letters. The zero iterate is the singleton [0]. This is the iterate u_n of Definition 2.

**Definition 1.6 (Original iterate length).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicLength`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicLength` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k, c : Fin k → Nat and natural n, cyclicLength hk c n is the length of cyclicWord hk c n. Write this length as U(n). This is U_n of Definition 2.

**Definition 1.7 (Same fixed-point prefix).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicPrefix`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k, c : Fin k → Nat and natural m, cyclicPrefix hk c m is (cyclicWord hk c m).take m. This is a finite definition, with no growth or fixed-point premise. Under the hypotheses of cyclic_iterate_structure its length is exactly m and it agrees with take m of every sufficiently long iterate.

**Definition 1.8 (Original-letter interior).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicInterior`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicInterior` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k and c : Fin k → Nat, cyclicInterior hk c is a function Nat → Fin k → List (Fin k). Its value at (0,a) is the empty list. Its value at (n+1,a) is wordPower (cyclicDigit c a) (cyclicWord hk c n), concatenated with cyclicInterior hk c n (cyclicNext hk a). Here wordPower j v concatenates j copies of v.

**Definition 1.9 (Finite periodic digit segment).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicSegment`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicSegment` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k, c : Fin k → Nat, natural n and a : Fin k, cyclicSegment hk c n a is the length-n list whose position i : Fin n is cyclicDigit c at the original letter (a.val+i.val) modulo k.

**Definition 1.10 (Original coefficient blocks).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicBlockProduct`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicBlockProduct` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k, c : Fin k → Nat, naturals n,count and proof hcount : count ≤ k, cyclicBlockProduct hk c n count hcount is the flattened list of blocks indexed by a : Fin count in increasing order. Block a is wordPower (c(a)) (cyclicWord hk c (n-1-a.val)), with a embedded into Fin k using hcount. All differences are natural-number subtraction. This is the block expression in Proposition 4, represented by a finite indexed list and flattening.

**Definition 1.11 (Complete minimum proposition).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.CyclicAttractorMinimum`

*Formalization.* `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.CyclicAttractorMinimum` (`✓ std3`).

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 0 < k and c : Fin k → Nat, CyclicAttractorMinimum hk c means: for every natural m with 0 < m, both clauses hold. First, for every natural i with i ≤ k-2, U(i) ≤ m and m < U(i+1), gamma(cyclicPrefix hk c m)=i+1. Second, U(k-1) ≤ m implies gamma(cyclicPrefix hk c m)=k. These are implications for all m and i; the definition adds no coefficient, rotation or primitivity hypotheses. This proposition records the full assertion of Conjecture 42; the definition supplies no proof of it.

**Theorem 1.12 (Nesting and stable prefix semantics).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_iterate_structure`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_iterate_structure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every natural k with hk : 2 ≤ k and c : Fin k → Nat with 1 ≤ c(0) and 1 ≤ c(k-1), the following six conclusions hold without a cyclic-maximality premise. For every natural n and letter a : Fin k, morphismPower (cyclicMorphism hk0 c) n [a] equals cyclicInterior hk0 c n a followed by the singleton original letter (a.val+n) modulo k, where hk0 certifies 0 < k. For every n, cyclicWord hk0 c n is a prefix of cyclicWord hk0 c (n+1), and U(n) < U(n+1). For every n, n+1 ≤ U(n). The function n ↦ U(n+1)-U(n) is monotone. Finally, for every naturals m,n with m ≤ U(n), cyclicPrefix hk0 c m equals (cyclicWord hk0 c n).take m. These nesting and unbounded-length statements identify the finite presentation with every original fixed-point prefix. Definition 2 and the working hypotheses supply the published fixed-point setting. The six-clause finite presentation, including the original-letter interior, growth gaps and prefix-stability bridge, is proved here.

**Theorem 1.13 (All-level fractional prefixes).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_fractional_prefix`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_fractional_prefix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 2 ≤ k, c : Fin k → Nat with 1 ≤ c(0), 1 ≤ c(k-1), CyclicMaximal c, and every natural n, (cyclicWord hk0 c (n+1)).dropLast is a prefix of wordPower (c(0)+1) (cyclicWord hk0 c n). Here hk0 certifies 0 < k. The assertion is about literal original-letter lists at every level. Weak rotation comparison includes equal rotations, arbitrary zero middle coefficients, proper powers and unary primitive roots. The fractional-prefix implication is published as Proposition 34(3 implies 1). This finite formulation additionally gives the explicit c(0)+1 power cap by an original-letter induction; it is a proved supplier of the full result.

**Theorem 1.14 (Short and full original recurrences).**

Lean statement: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_word_recurrence`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_word_recurrence` (`✓ std3`). ∎

*Citation.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every k with hk : 2 ≤ k and c : Fin k → Nat with 1 ≤ c(0) and 1 ≤ c(k-1), two identities hold without cyclic maximality. For every natural n with hn : n < k, cyclicWord hk0 c n equals cyclicBlockProduct hk0 c n n hn.le concatenated with the singleton original letter n : Fin k. For every natural n with k ≤ n, cyclicWord hk0 c n equals cyclicBlockProduct hk0 c n k le_rfl. Here hk0 certifies 0 < k; these use all original coefficient blocks, including zero multiplicities. Both identities are the published recurrences of Proposition 4, proved here for the original substitution rather than assumed.

**Theorem 1.15 (The full original Conjecture 42 minimum).**

$$\forall k \in \mathbb{N},\; \forall c \in Function\left(Fin\left(k\right), \mathbb{N}\right),\; \left(2 \le k \land \left(1 \le coefficient\left(c, 0\right) \land \left(1 \le coefficient\left(c, k - 1\right) \land CyclicMaximal\left(c\right)\right)\right)\right) \Rightarrow \left(\forall m \in \mathbb{N},\; 0 < m \Rightarrow \left(\left(\forall i \in \mathbb{N},\; \left(i \le k - 2 \land \left(cyclicLength\left(c, i\right) \le m \land m < cyclicLength\left(c, i + 1\right)\right)\right) \Rightarrow gamma\left(cyclicPrefix\left(c, m\right)\right) = i + 1\right) \land \left(cyclicLength\left(c, k - 1\right) \le m \Rightarrow gamma\left(cyclicPrefix\left(c, m\right)\right) = k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.result` (`✓ std3`). ∎

*Resolves.* `Problems/parry-string-attractor-minimum` (proved) by `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"parry-string-attractor-minimum","declaration_gid":"D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* France Gheeraert, Giuseppe Romana, Manon Stipulanti (2023). *String attractors of some simple-Parry automatic sequences*. URL: <https://arxiv.org/abs/2302.13647v2>.

*Commentary.*

For every natural k with 2 ≤ k, coefficient function c : Fin k → Nat with c(0) ≥ 1 and c(k-1) ≥ 1, and CyclicMaximal c, for every natural m > 0: for every natural i ≤ k-2 with U(i) ≤ m < U(i+1), gamma(cyclicPrefix hk0 c m)=i+1; and if U(k-1) ≤ m, gamma(cyclicPrefix hk0 c m)=k. Here hk0 certifies 0 < k, U(n)=cyclicLength hk0 c n, and gamma minimizes over all eligible finite subsets of original positions with equal occurrences wholly inside the same prefix. The original alphabet, arbitrary zero middle coefficients, equality of rotations, proper powers, unary primitive roots and all positive prefix lengths remain in scope. The endpoint intervals and full-k residual scan construct the upper bound; unrestricted singleton factors give the matching lower bound. The proof includes r=0, empty residual intervals and the terminal scan level. No paper statement is a premise.

## References

- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.CyclicAttractorMinimum`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.CyclicMaximal`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicBlockProduct`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicDigit`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicInterior`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicLength`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicMorphism`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicNext`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicPrefix`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicSegment`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclicWord`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_fractional_prefix`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_iterate_structure`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.cyclic_word_recurrence`
- Truth anchor: `D5/S1/Words/Attractors/CyclicMorphismAttractorMinimum.result`
- Dependency: [D5/S1/Recurrence/Raney/MaximalBlockEvolution](../../Recurrence/Raney/MaximalBlockEvolution.md)
- Dependency: [D5/S1/Words/Attractors/FiniteWordAttractors](FiniteWordAttractors.md)
- Dependency: [D5/S1/Words/Attractors/PeriodicPrefixAttractors](PeriodicPrefixAttractors.md)
