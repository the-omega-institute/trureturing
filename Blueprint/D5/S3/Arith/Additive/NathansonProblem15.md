# Nathanson's Problem 15

## Abstract

Prescribed intervals and consecutive pairs in iterated integer sumsets

**Definition 1.1 (Signed digit).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (i : \operatorname{Fin}\left(m\right)), \operatorname{digit}\left(h, u, v, i\right) = (u\left(i\right) : \mathbb{Z}) - ((h : \mathbb{Z}) - 1) \cdot (v\left(i\right) : \mathbb{Z})$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem15.digit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first label contributes one unit of its place and the second label contributes minus h − 1 units, multiplied by the respective counts.

**Definition 1.2 (Signed radix code).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \operatorname{radixCode}\left(h, u, v\right) = \sum_{i : \operatorname{Fin}\left(m\right)} (\operatorname{digit}\left(h, u, v, i\right) \cdot ((h : \mathbb{Z})^{2} + 1)^{\operatorname{Fin}.\operatorname{val}\left(i\right)})$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem15.radixCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base is h² + 1, one more than the width of the allowed digit interval.

**Definition 1.3 (Radix generators).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (M : \mathbb{Z}), \forall (t : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), \operatorname{radixGenerators}\left(h, M, t\right) = (\operatorname{let} a : (\operatorname{Fin}\left(m\right) \to \mathbb{Z}) := \operatorname{fun} (i : \operatorname{Fin}\left(m\right)) \mapsto M \cdot ((h : \mathbb{Z})^{2} + 1)^{\operatorname{Fin}.\operatorname{val}\left(i\right)} \operatorname{in} \operatorname{Sum}.\operatorname{elim}\left(a, (\operatorname{fun} (i : \operatorname{Fin}\left(m\right)) \mapsto t\left(i\right) - ((h : \mathbb{Z}) - 1) \cdot a\left(i\right))\right))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem15.radixGenerators` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prescribed point, two generators are indexed by the two copies of Fin m.

**Theorem 1.4 (The prescribed interval equivalences).**

$$\forall (h : \mathbb{N}), \forall (q : \mathbb{N}), \forall (n : \mathbb{N}), \forall (N : \mathbb{Z}), (2 \le h) \Rightarrow \left((2 \le q) \Rightarrow \left((1 \le n) \Rightarrow \left(((n : \mathbb{Z}) + 2 \le N) \Rightarrow \forall (c : \operatorname{Fin}\left(q\right) \to \mathbb{Z}), (\forall (i : \operatorname{Fin}\left(q\right)), \forall (j : \operatorname{Fin}\left(q\right)), (\operatorname{Fin}.\operatorname{val}\left(j\right) = \operatorname{Fin}.\operatorname{val}\left(i\right) + 1) \Rightarrow N \le c\left(j\right) - c\left(i\right)) \Rightarrow \exists (A : \operatorname{Finset}\left(\mathbb{Z}\right)), (\operatorname{Finset}.\operatorname{card}\left(A\right) \le 2 \cdot q \cdot (n + 1)) \land ((\forall (x : \mathbb{Z}), ((\operatorname{Set}.\operatorname{Icc}\left(x, x + (n : \mathbb{Z})\right) \subseteq \operatorname{SMul}.\operatorname{smul}\left(h, (A : \operatorname{Set}\left(\mathbb{Z}\right))\right)) \Leftrightarrow (\exists (i : \operatorname{Fin}\left(q\right)), x = c\left(i\right)))) \land (\forall (x : \mathbb{Z}), ((\operatorname{Set}.\operatorname{Icc}\left(x, x + 1\right) \subseteq \operatorname{SMul}.\operatorname{smul}\left(h, (A : \operatorname{Set}\left(\mathbb{Z}\right))\right)) \Leftrightarrow (\exists (i : \operatorname{Fin}\left(q\right)), (\operatorname{Set}.\operatorname{Icc}\left(x, x + 1\right) \subseteq \operatorname{Set}.\operatorname{Icc}\left(c\left(i\right), c\left(i\right) + (n : \mathbb{Z})\right)) \land (\operatorname{Set}.\operatorname{Icc}\left(c\left(i\right), c\left(i\right) + (n : \mathbb{Z})\right) \subseteq \operatorname{SMul}.\operatorname{smul}\left(h, (A : \operatorname{Set}\left(\mathbb{Z}\right))\right))))))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15` (`✓ std3`). ∎

*Resolves.* `Problems/nathanson-2026-problem-15-prescribed-intervals` (proved) by `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nathanson-2026-problem-15-prescribed-intervals","declaration_gid":"D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems in additive number theory, VII: The structure of additive h-bases for n*. URL: <https://arxiv.org/abs/2605.26425v3>.

*Commentary.*

Section 5, Problem 15 asks for both interval equivalences and an estimate for the size of the finite generator set. The source indexes the starts from 1 through q. The Lean index i : Fin q represents source index i.val + 1. The natural parameters h, q and n have the stated lower bounds, N denotes the integer gap N_q, and x ranges over all integers in each equivalence. Pointwise scalar multiplication adds exactly h elements with repetitions allowed. The construction uses two labelled generators per prescribed point, giving at most 2q(n + 1) distinct generators. Each sum is represented by nonnegative label counts of total weight h, even when some generator values coincide. The signed digits are uᵢ − (h − 1)vᵢ. Their allowed interval has width h², so equal codes in base h² + 1 have equal digits by successively reducing modulo the base. If two distinct count pairs have equal digits, a change in a second-label count forces one pair to spend all h terms at a single index. Both pairs then have zero digits. A zero code uses h − 1 first labels and one second label at a single index, and its sum is exactly the prescribed point at that index. The construction scales the code by twice the remainder bound plus two, which separates unequal codes by at least two. Adjacent sums must share a code and come from distinct multiplicity pairs, so their common code is zero. Each is then a prescribed point, and the spacing forces both into one prescribed interval.

## References

- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.digit`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.radixCode`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.radixGenerators`
