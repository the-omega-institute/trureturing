# Nathanson's Problem 15

## Abstract

Prescribed intervals and consecutive pairs in iterated integer sumsets

**Theorem 1.1 (Signed radix injectivity).**

$$\forall (m : \mathbb{N}), \forall (B : \mathbb{Z}), (1 < B) \Rightarrow \forall (d : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), \forall (e : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), (\forall (i : \operatorname{Fin}\left(m\right)), \operatorname{Int}.\operatorname{natAbs}\left(d\left(i\right) - e\left(i\right)\right) < \operatorname{Int}.\operatorname{natAbs}\left(B\right)) \Rightarrow \left((\sum_{i : \operatorname{Fin}\left(m\right)} (d\left(i\right) \cdot B^{\operatorname{Fin}.\operatorname{val}\left(i\right)}) = \sum_{i : \operatorname{Fin}\left(m\right)} (e\left(i\right) \cdot B^{\operatorname{Fin}.\operatorname{val}\left(i\right)})) \Rightarrow d = e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.signed_radix_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Reducing the two sums modulo the radix gives equality of their first digits, since the difference has magnitude less than the radix. Removing those digits reduces to the shorter expansion.

**Definition 1.2 (Signed digit).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (i : \operatorname{Fin}\left(m\right)), \operatorname{digit}\left(h, u, v, i\right) = (u\left(i\right) : \mathbb{Z}) - ((h : \mathbb{Z}) - 1) \cdot (v\left(i\right) : \mathbb{Z})$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem15.digit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first label contributes one unit of its place and the second label contributes minus h − 1 units, multiplied by the respective counts.

**Theorem 1.3 (Collisions of signed digits).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), (2 \le h) \Rightarrow \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \Rightarrow \forall (u' : \operatorname{Fin}\left(m\right) \to \mathbb{N}) (v' : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u'\left(i\right) + v'\left(i\right)) = h) \Rightarrow \left((\operatorname{digit}\left(h, u, v\right) = \operatorname{digit}\left(h, u', v'\right)) \Rightarrow \left(((u, v) \ne (u', v')) \Rightarrow \operatorname{digit}\left(h, u, v\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.digit_eq_zero_of_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two distinct multiplicity pairs give the same digits, a changed second-label count forces one pair to spend all h terms on a single index.

**Theorem 1.4 (Zero digits).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), (2 \le h) \Rightarrow \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \Rightarrow \left((\operatorname{digit}\left(h, u, v\right) = 0) \Leftrightarrow (\exists (j : \operatorname{Fin}\left(m\right)), \forall (i : \operatorname{Fin}\left(m\right)), (u\left(i\right) = (\operatorname{if} i = j \operatorname{then} h - 1 \operatorname{else} 0)) \land (v\left(i\right) = (\operatorname{if} i = j \operatorname{then} 1 \operatorname{else} 0)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.digit_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero digit vector spends h − 1 first labels and one second label at a single index.

**Definition 1.5 (Signed radix code).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \operatorname{radixCode}\left(h, u, v\right) = \sum_{i : \operatorname{Fin}\left(m\right)} (\operatorname{digit}\left(h, u, v, i\right) \cdot ((h : \mathbb{Z})^{2} + 1)^{\operatorname{Fin}.\operatorname{val}\left(i\right)})$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem15.radixCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The base is h² + 1, one more than the width of the allowed digit interval.

**Theorem 1.6 (Equality of radix codes).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), (2 \le h) \Rightarrow \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \Rightarrow \forall (u' : \operatorname{Fin}\left(m\right) \to \mathbb{N}) (v' : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u'\left(i\right) + v'\left(i\right)) = h) \Rightarrow \left((\operatorname{radixCode}\left(h, u, v\right) = \operatorname{radixCode}\left(h, u', v'\right)) \Leftrightarrow (\operatorname{digit}\left(h, u, v\right) = \operatorname{digit}\left(h, u', v'\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.radixCode_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weight bound keeps each difference of corresponding digits strictly below the base in magnitude.

**Theorem 1.7 (Zero radix code).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), (2 \le h) \Rightarrow \forall (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \forall (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \Rightarrow \left((\operatorname{radixCode}\left(h, u, v\right) = 0) \Leftrightarrow (\exists (j : \operatorname{Fin}\left(m\right)), \forall (i : \operatorname{Fin}\left(m\right)), (u\left(i\right) = (\operatorname{if} i = j \operatorname{then} h - 1 \operatorname{else} 0)) \land (v\left(i\right) = (\operatorname{if} i = j \operatorname{then} 1 \operatorname{else} 0)))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.radixCode_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Signed radix injectivity reduces the zero-code criterion to the zero-digit criterion.

**Theorem 1.8 (Labelled sums and multiplicities).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (z : \mathbb{Z}), \forall (a : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), \forall (b : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), (z \in \operatorname{SMul}.\operatorname{smul}\left(h, \operatorname{Set}.\operatorname{range}\left(\operatorname{Sum}.\operatorname{elim}\left(a, b\right)\right)\right)) \Leftrightarrow (\exists (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \exists (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \land (\sum_{i : \operatorname{Fin}\left(m\right)} ((u\left(i\right) : \mathbb{Z}) \cdot a\left(i\right) + (v\left(i\right) : \mathbb{Z}) \cdot b\left(i\right)) = z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.mem_labelled_sum_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two families supply independent labels even when some of their values coincide. Pointwise natural scalar multiplication of a set denotes addition of exactly h elements with repetitions allowed.

**Definition 1.9 (Radix generators).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (M : \mathbb{Z}), \forall (t : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), \operatorname{radixGenerators}\left(h, M, t\right) = (\operatorname{let} a : (\operatorname{Fin}\left(m\right) \to \mathbb{Z}) := \operatorname{fun} (i : \operatorname{Fin}\left(m\right)) \mapsto M \cdot ((h : \mathbb{Z})^{2} + 1)^{\operatorname{Fin}.\operatorname{val}\left(i\right)} \operatorname{in} \operatorname{Sum}.\operatorname{elim}\left(a, (\operatorname{fun} (i : \operatorname{Fin}\left(m\right)) \mapsto t\left(i\right) - ((h : \mathbb{Z}) - 1) \cdot a\left(i\right))\right))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonProblem15.radixGenerators` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each prescribed point, two generators are indexed by the two copies of Fin m.

**Theorem 1.10 (Radix code and remainder).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), \forall (M : \mathbb{Z}), \forall (z : \mathbb{Z}), \forall (t : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), (z \in \operatorname{SMul}.\operatorname{smul}\left(h, \operatorname{Set}.\operatorname{range}\left(\operatorname{radixGenerators}\left(h, M, t\right)\right)\right)) \Leftrightarrow (\exists (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \exists (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \land (M \cdot \operatorname{radixCode}\left(h, u, v\right) + \sum_{i : \operatorname{Fin}\left(m\right)} ((v\left(i\right) : \mathbb{Z}) \cdot t\left(i\right)) = z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.mem_radixGenerators_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scaled code captures positional contributions. Only the second labels contribute to the remainder.

**Theorem 1.11 (Values with code zero).**

$$\forall (m : \mathbb{N}), \forall (h : \mathbb{N}), (2 \le h) \Rightarrow \forall (t : \operatorname{Fin}\left(m\right) \to \mathbb{Z}), \forall (z : \mathbb{Z}), (z \in \operatorname{Set}.\operatorname{range}\left(t\right)) \Leftrightarrow (\exists (u : \operatorname{Fin}\left(m\right) \to \mathbb{N}), \exists (v : \operatorname{Fin}\left(m\right) \to \mathbb{N}), (\sum_{i : \operatorname{Fin}\left(m\right)} (u\left(i\right) + v\left(i\right)) = h) \land ((\operatorname{radixCode}\left(h, u, v\right) = 0) \land (\sum_{i : \operatorname{Fin}\left(m\right)} ((v\left(i\right) : \mathbb{Z}) \cdot t\left(i\right)) = z)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.mem_range_iff_zero_code_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A zero-code sum gives the prescribed point at its unique occupied index, and every prescribed point has that representation.

**Theorem 1.12 (The prescribed interval equivalences).**

$$\forall (h : \mathbb{N}), \forall (q : \mathbb{N}), \forall (n : \mathbb{N}), \forall (N : \mathbb{Z}), (2 \le h) \Rightarrow \left((2 \le q) \Rightarrow \left((1 \le n) \Rightarrow \left(((n : \mathbb{Z}) + 2 \le N) \Rightarrow \forall (c : \operatorname{Fin}\left(q\right) \to \mathbb{Z}), (\forall (i : \operatorname{Fin}\left(q\right)), \forall (j : \operatorname{Fin}\left(q\right)), (\operatorname{Fin}.\operatorname{val}\left(j\right) = \operatorname{Fin}.\operatorname{val}\left(i\right) + 1) \Rightarrow N \le c\left(j\right) - c\left(i\right)) \Rightarrow \exists (A : \operatorname{Finset}\left(\mathbb{Z}\right)), (\operatorname{Finset}.\operatorname{card}\left(A\right) \le 2 \cdot q \cdot (n + 1)) \land ((\forall (x : \mathbb{Z}), (\operatorname{Set}.\operatorname{Icc}\left(x, x + (n : \mathbb{Z})\right) \subseteq \operatorname{SMul}.\operatorname{smul}\left(h, (A : \operatorname{Set}\left(\mathbb{Z}\right))\right)) \Leftrightarrow (\exists (i : \operatorname{Fin}\left(q\right)), x = c\left(i\right))) \land (\forall (x : \mathbb{Z}), (\operatorname{Set}.\operatorname{Icc}\left(x, x + 1\right) \subseteq \operatorname{SMul}.\operatorname{smul}\left(h, (A : \operatorname{Set}\left(\mathbb{Z}\right))\right)) \Leftrightarrow (\exists (i : \operatorname{Fin}\left(q\right)), (\operatorname{Set}.\operatorname{Icc}\left(x, x + 1\right) \subseteq \operatorname{Set}.\operatorname{Icc}\left(c\left(i\right), c\left(i\right) + (n : \mathbb{Z})\right)) \land (\operatorname{Set}.\operatorname{Icc}\left(c\left(i\right), c\left(i\right) + (n : \mathbb{Z})\right) \subseteq \operatorname{SMul}.\operatorname{smul}\left(h, (A : \operatorname{Set}\left(\mathbb{Z}\right))\right)))))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *Problems in additive number theory, VII: The structure of additive h-bases for n*. URL: <https://arxiv.org/abs/2605.26425v3>.

*Commentary.*

Section 5, Problem 15 asks for both interval equivalences and an estimate for the size of the finite generator set. The source indexes the starts from 1 through q. The Lean index i : Fin q represents source index i.val + 1. The natural parameters h, q and n have the stated lower bounds, N denotes the integer gap N_q, and x ranges over all integers in each equivalence. Pointwise scalar multiplication adds exactly h elements with repetitions allowed. The construction uses two labelled generators per prescribed point. A scale greater than twice the remainder bound separates unequal codes by at least two. Adjacent sums must share a code and come from distinct multiplicity pairs, so their common code is zero. Each is then a prescribed point, and the spacing forces both into one prescribed interval.

## References

- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.digit`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.digit_eq_zero_iff`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.digit_eq_zero_of_collision`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.mem_labelled_sum_iff`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.mem_radixGenerators_iff`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.mem_range_iff_zero_code_sum`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.nathanson_problem15`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.radixCode`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.radixCode_eq_iff`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.radixCode_eq_zero_iff`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.radixGenerators`
- Truth anchor: `D5/S3/Arith/Additive/NathansonProblem15.signed_radix_injective`
