# LabeledComplementAlgebra

## Abstract

Finite binary Riordan complements: LabeledComplementAlgebra

**Definition 1.1 (riordanGraph).**

$$\forall (n: \operatorname{Nat}), \forall (g: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), \forall (f: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), \operatorname{riordanGraph}\left(n\right)\left(g\right)\left(f\right) = \operatorname{SimpleGraph}.\operatorname{fromRel}\left(((i: \operatorname{Fin}\left(n\right) \mapsto (j: \operatorname{Fin}\left(n\right) \mapsto (j.\operatorname{val} < i.\operatorname{val}) \land (\operatorname{PowerSeries}.\operatorname{coeff}\left((i.\operatorname{val} - 1)\right)\left((g \cdot f^{j.\operatorname{val}})\right) = 1))))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.riordanGraph` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A401493, revision 10, COMMENTS (unpaginated): "A Riordan graph of order n is a simple graph on the vertices 1..n whose adjacency matrix A satisfies A(i,j) = [t^(i-2)] g(t)*f(t)^(j-1) mod 2 for i > j, for some power series g, f over GF(2) with f(0) = 0. Equivalently, the strictly lower triangular part of A is the binary Riordan matrix (g,f) of order n-1 (Cheon, Jung, Kitaev and Mojallal, 2019)." The vertex i : Fin n corresponds to label i.val + 1. The function SimpleGraph.fromRel supplies symmetry and excludes loops.

**Definition 1.2 (IsLabeledRiordan).**

$$\forall (n: \operatorname{Nat}), \forall (G: \operatorname{SimpleGraph}\left((\operatorname{Fin}\left(n\right))\right)), (\operatorname{IsLabeledRiordan}\left(G\right)) \Leftrightarrow (\exists (g: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), \exists (f: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right) = 0) \land (G = \operatorname{riordanGraph}\left(n\right)\left(g\right)\left(f\right)))$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.IsLabeledRiordan` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A401493, revision 10, COMMENTS (unpaginated): "A Riordan graph of order n is a simple graph on the vertices 1..n whose adjacency matrix A satisfies A(i,j) = [t^(i-2)] g(t)*f(t)^(j-1) mod 2 for i > j, for some power series g, f over GF(2) with f(0) = 0. Equivalently, the strictly lower triangular part of A is the binary Riordan matrix (g,f) of order n-1 (Cheon, Jung, Kitaev and Mojallal, 2019)." The existential predicate counts graphs on the fixed labels i.val + 1 and imposes no properness condition.

**Definition 1.3 (ComplementCompatible).**

$$\forall (n: \operatorname{Nat}), \operatorname{ComplementCompatible}\left(n\right) = \{G: \operatorname{SimpleGraph}\left((\operatorname{Fin}\left(n\right))\right) \mid (\operatorname{IsLabeledRiordan}\left(G\right)) \land (\operatorname{IsLabeledRiordan}\left(G^{\operatorname{c}}\right))\}$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.ComplementCompatible` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A401496, revision 9, NAME (unpaginated): "Number of labeled Riordan graphs of order n whose complement, with the same vertex labeling, is also a labeled Riordan graph." The subtype consists of graphs themselves, rather than parameter pairs or isomorphism classes.

**Definition 1.4 (a).**

$$\forall (n: \operatorname{Nat}), \operatorname{a}\left(n\right) = \operatorname{Nat}.\operatorname{card}\left((\operatorname{ComplementCompatible}\left(n\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.a` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A401496, revision 9, NAME (unpaginated): "Number of labeled Riordan graphs of order n whose complement, with the same vertex labeling, is also a labeled Riordan graph." Nat.card counts the finite graph subtype.

**Definition 1.5 (a001651).**

$$\forall (i: \operatorname{Nat}), \operatorname{a001651}\left(i\right) = i + \operatorname{Nat}.\operatorname{div}\left(i, 2\right) + 1$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.a001651` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The zero-based list of positive integers not divisible by three is i + Nat.div i 2 + 1.

**Definition 1.6 (a113836).**

$$\forall (m: \operatorname{Nat}), \operatorname{a113836}\left(m\right) = \sum_{i \in \operatorname{Finset}.\operatorname{range}\left(m\right)} 2^{(\operatorname{a001651}\left(i\right) - 1)}$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.a113836` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A113836 is the sum of powers of two with exponents one less than the first m positive nonmultiples of three. At zero the sum is empty.

**Definition 1.7 (ogf).**

$$\operatorname{ogf} = \operatorname{PowerSeries}.\operatorname{mk}\left((n: \operatorname{Nat} \mapsto \operatorname{if} n = 0 \operatorname{then} 0 \operatorname{else} (\operatorname{a}\left(n\right) : \operatorname{Rat}))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.ogf` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The formal generating series has constant coefficient zero and coefficient a n at every positive degree n.

**Definition 1.8 (conjecturedOGF).**

$$\operatorname{conjecturedOGF} = \operatorname{PowerSeries}.\operatorname{X} \cdot (1 - 2 \cdot \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 + 3 \cdot \operatorname{PowerSeries}.\operatorname{X}) \cdot \operatorname{PowerSeries}.\operatorname{invOfUnit}\left(((1 - \operatorname{PowerSeries}.\operatorname{X}) \cdot (1 - 8 \cdot \operatorname{PowerSeries}.\operatorname{X}^{2}))\right)\left(1\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.conjecturedOGF` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A401496, revision 9, FORMULA 5 (unpaginated): "Conjecture: G.f.: x*(1 - 2*x)*(1 + 3*x)/((1 - x)*(1 - 8*x^2))." PowerSeries.invOfUnit expresses formal inversion of the denominator, whose constant coefficient is one.

**Definition 1.9 (claim).**

$$(\operatorname{claim}) \Leftrightarrow ((\operatorname{a}\left(1\right) = 1) \land ((\operatorname{a}\left(2\right) = 2) \land (((\forall (n: \operatorname{Nat}), \left(3 \le n\right) \to \left((\operatorname{a}\left(n\right) : \operatorname{Int}) = 8 \cdot (\operatorname{a}\left((n - 2)\right) : \operatorname{Int}) - 4\right))) \land (((\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left((\operatorname{a}\left((n + 1)\right) : \operatorname{Int}) - (\operatorname{a}\left(n\right) : \operatorname{Int}) = (2 : \operatorname{Int})^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot (n - 1), 2\right))}\right))) \land (((\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left(\operatorname{a}\left(n\right) = 1 + \sum_{k \in \operatorname{Finset}.\operatorname{range}\left((n - 1)\right)} 2^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot k, 2\right))}\right))) \land (((\forall (n: \operatorname{Nat}), \left(2 \le n\right) \to \left(\operatorname{a}\left(n\right) = \operatorname{a113836}\left((n - 1)\right) + 1\right))) \land (((\forall (k: \operatorname{Nat}), \left(1 \le k\right) \to \left((\operatorname{a}\left((2 \cdot k)\right) : \operatorname{Rat}) = \frac{(10 \cdot (8 : \operatorname{Rat})^{(k - 1)} + 4)}{7}\right))) \land (((\forall (k: \operatorname{Nat}), (\operatorname{a}\left((2 \cdot k + 1)\right) : \operatorname{Rat}) = \frac{(3 \cdot (8 : \operatorname{Rat})^{k} + 4)}{7})) \land (\operatorname{ogf} = \operatorname{conjecturedOGF})))))))))$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.claim` (`✓ std3`).

*Citation.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A401496, revision 9, FORMULA 1–5 (unpaginated): "Conjecture: a(n) = 8*a(n-2) - 4 for n >= 3." "Conjecture: a(n+1) - a(n) = 2^floor(3*(n-1)/2), so a(n) = 1 + Sum_{k=1..n-1} 2^floor(3*(k-1)/2)." "Conjecture: a(n) = A113836(n-1) + 1." "Conjecture: a(2*k) = (108^(k-1) + 4)/7 and a(2*k+1) = (38^k + 4)/7." "Conjecture: G.f.: x*(1 - 2*x)*(1 + 3*x)/((1 - x)*(1 - 8*x^2))." The concatenations 108 and 38 are interpreted as the products 10 times 8 and 3 times 8, respectively. Author confirmation of this typography is unavailable. The identity involving A113836 has domain n at least two. Integer differences and rational quotients preserve the stated equalities; Nat.div denotes floor division.

**Theorem 1.10 (count one).**

$$\operatorname{a}\left(1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.count_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

There is exactly one complement-compatible graph on one vertex.

**Definition 1.11 (prefixCount).**

$$\forall (n: \operatorname{Nat}), \operatorname{prefixCount}\left(n\right) = 1 + \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n\right)} 2^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot k, 2\right))}$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.prefixCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The prefix count is one plus the first n powers of two with exponents Nat.div (3 * k) 2.

**Definition 1.12 (truncateMap).**

$$\forall (N: \operatorname{Nat}), \forall (f: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), \operatorname{truncateMap}\left(N\right)\left(f\right) = \operatorname{AdjoinRoot}.\operatorname{mk}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right)\left((\operatorname{PowerSeries}.\operatorname{trunc}\left((N + 1)\right)\left(f\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Truncate the series at length N + 1 and take its residue modulo the polynomial X to the power N + 1.

**Theorem 1.13 (monicModulus).**

$$\forall (N: \operatorname{Nat}), (((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})).\operatorname{Monic}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.monicModulus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The defining power of the polynomial X is monic.

**Theorem 1.14 (modulusDegree).**

$$\forall (N: \operatorname{Nat}), (((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})).\operatorname{natDegree} = N + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.modulusDegree` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The degree of the defining power of the polynomial X is N + 1.

**Definition 1.15 (coefficientEquiv).**

$$\forall (N: \operatorname{Nat}), \operatorname{coefficientEquiv}\left(N\right) = (((\operatorname{AdjoinRoot}.\operatorname{powerBasisAux}'\left((\operatorname{monicModulus}\left(N\right))\right))).\operatorname{equivFun}).\operatorname{trans}\left((\operatorname{LinearEquiv}.\operatorname{piCongrLeft}'\left((\operatorname{ZMod}\left(2\right))\right)\left((\operatorname{Function}.\operatorname{const}\left((\operatorname{Fin}\left(((((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})).\operatorname{natDegree})\right))\right)\left((\operatorname{ZMod}\left(2\right))\right))\right)\left((\operatorname{finCongr}\left((\operatorname{modulusDegree}\left(N\right))\right))\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.coefficientEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The power basis of the quotient identifies its elements with their N + 1 coefficients.

**Definition 1.16 (truncatedCoeff).**

$$\forall (N: \operatorname{Nat}), \forall (i: \operatorname{Nat}), \forall (f: (\operatorname{AdjoinRoot}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right))), \operatorname{truncatedCoeff}\left(N\right)\left(i\right)\left(f\right) = ((\operatorname{AdjoinRoot}.\operatorname{modByMonicHom}\left((\operatorname{monicModulus}\left(N\right))\right)\left(f\right))).\operatorname{coeff}\left(i\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncatedCoeff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Take the coefficient of the unique representative polynomial of degree less than N + 1.

**Theorem 1.17 (truncatedCoeff truncateMap).**

$$\forall (N: \operatorname{Nat}), \forall (f: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), \forall (i: \operatorname{Nat}), (i < N + 1) \Rightarrow (\operatorname{truncatedCoeff}\left(N\right)\left(i\right)\left((\operatorname{truncateMap}\left(N\right)\left(f\right))\right) = \operatorname{PowerSeries}.\operatorname{coeff}\left(i\right)\left(f\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncatedCoeff_truncateMap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Below the truncation length, taking a quotient coefficient recovers the original series coefficient.

**Theorem 1.18 (truncateMap eq iff).**

$$\forall (N: \operatorname{Nat}), \forall (f: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), \forall (g: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), (\operatorname{truncateMap}\left(N\right)\left(f\right) = \operatorname{truncateMap}\left(N\right)\left(g\right)) \Leftrightarrow (\forall (i: \operatorname{Nat}), (i < N + 1) \Rightarrow (\operatorname{PowerSeries}.\operatorname{coeff}\left(i\right)\left(f\right) = \operatorname{PowerSeries}.\operatorname{coeff}\left(i\right)\left(g\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Two quotient elements agree exactly when all coefficients below the truncation length agree.

**Theorem 1.19 (truncateMap eq zero iff).**

$$\forall (N: \operatorname{Nat}), \forall (f: \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)), (\operatorname{truncateMap}\left(N\right)\left(f\right) = 0) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{X} : \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)} \mid f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A series maps to zero exactly when it is divisible by X to the truncation length.

**Theorem 1.20 (complement orientation card).**

$$\forall (V: \operatorname{Type}), \forall (P: \operatorname{SimpleGraph}\left(V\right) \to \operatorname{Prop}), \forall (v: V), \forall (w: V), (v \ne w) \Rightarrow (\operatorname{Nat}.\operatorname{card}\left(\{G: \operatorname{SimpleGraph}\left(V\right) \mid (P\left(G\right)) \land (P\left(G^{\operatorname{c}}\right))\}\right) = 2 \cdot \operatorname{Nat}.\operatorname{card}\left(\{G: \operatorname{SimpleGraph}\left(V\right) \mid (P\left(G\right)) \land ((P\left(G^{\operatorname{c}}\right)) \land (G.\operatorname{Adj}\left(v\right)\left(w\right)))\}\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.complement_orientation_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Complementation pairs the graphs, and the presence of one fixed edge selects exactly one graph in each pair.

**Theorem 1.21 (unit parameter criterion).**

$$\forall (R: \operatorname{Type}), [\operatorname{CommRing}\left(R\right)] [\operatorname{CharP}\left(R\right)\left(2\right)] \forall (g: \operatorname{Units}\left(R\right)), \forall (H: \operatorname{Units}\left(R\right)), \forall (f: R), \forall (u: R), \forall (t: R), ((\forall (j: \operatorname{Nat}), (g : R) \cdot f^{j} + ((H : R) + g) \cdot u^{j} = (H : R) \cdot t^{j})) \Leftrightarrow ((f = t + (((H : R) + g) \cdot (\operatorname{Units}.\operatorname{val}\left(g^{-1}\right) : R)) \cdot (u + t)) \land (((H : R) + g) \cdot (u + t)^{2} = 0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.unit_parameter_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Over a commutative ring of characteristic two, the all-column equations with two unit parameters are equivalent to a linear displacement equation and one square-annihilator equation.

**Theorem 1.22 (truncateMap isUnit).**

$$\forall (N: \operatorname{Nat}), \forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(f\right) = 1) \Rightarrow (\operatorname{IsUnit}\left((\operatorname{truncateMap}\left(N\right)\left(f\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_isUnit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A series with constant coefficient one maps to a unit of the finite quotient.

**Definition 1.23 (allOnes).**

$$\operatorname{allOnes} = \operatorname{PowerSeries}.\operatorname{mk}\left((\operatorname{Function}.\operatorname{const}\left(\operatorname{Nat}\right)\left(1\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.allOnes` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Every coefficient of this series is one.

**Theorem 1.24 (allOnes constant).**

$$\operatorname{PowerSeries}.\operatorname{constantCoeff}\left(\operatorname{allOnes}\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.allOnes_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The constant coefficient of the all-ones series is one.

**Theorem 1.25 (shifted square divisibility).**

$$\forall (f: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), \forall (N: \operatorname{Nat}), \forall (k: \operatorname{Nat}), ((\operatorname{PowerSeries}.\operatorname{X} : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))^{N} \mid \operatorname{PowerSeries}.\operatorname{X}^{k} \cdot f^{2}) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{X} : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))^{(\operatorname{Nat}.\operatorname{div}\left((N - k + 1), 2\right))} \mid f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.shifted_square_divisibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

A shifted square is divisible by a power of X exactly when the original series vanishes below the displayed half-threshold. Nat.div denotes floor division on natural numbers.

**Theorem 1.26 (zero prefix card).**

$$\forall (N: \operatorname{Nat}), \forall (q: \operatorname{Nat}), (q \le N) \Rightarrow (\operatorname{Nat}.\operatorname{card}\left(\{f: \operatorname{Fin}\left(N\right) \to (\operatorname{ZMod}\left(2\right)) \mid \forall (i: \operatorname{Fin}\left(N\right)), \left(i.\operatorname{val} < q\right) \to \left(f\left(i\right) = 0\right)\}\right) = 2^{(N - q)})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.zero_prefix_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Binary vectors with a prescribed zero prefix have one free binary coordinate at each remaining position.

**Definition 1.27 (canonicalSeries).**

$$\forall (N: \operatorname{Nat}), \forall (x: \operatorname{AdjoinRoot}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right)), \operatorname{canonicalSeries}\left(N\right)\left(x\right) = ((\operatorname{AdjoinRoot}.\operatorname{modByMonicHom}\left((\operatorname{monicModulus}\left(N\right))\right)\left(x\right) : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right)) : \operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.canonicalSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

Embed the unique representative polynomial of degree less than N + 1 into the ring of power series.

**Theorem 1.28 (truncateMap canonicalSeries).**

$$\forall (N: \operatorname{Nat}), \forall (x: (\operatorname{AdjoinRoot}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right))), \operatorname{truncateMap}\left(N\right)\left((\operatorname{canonicalSeries}\left(N\right)\left(x\right))\right) = x$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_canonicalSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The representative series maps back to its original quotient element.

**Theorem 1.29 (coefficientEquiv apply).**

$$\forall (N: \operatorname{Nat}), \forall (x: (\operatorname{AdjoinRoot}\left(((\operatorname{Polynomial}.\operatorname{X} : \operatorname{Polynomial}\left((\operatorname{ZMod}\left(2\right))\right))^{(N + 1)})\right))), \forall (i: \operatorname{Fin}\left((N + 1)\right)), \operatorname{coefficientEquiv}\left(N\right)\left(x\right)\left(i\right) = \operatorname{PowerSeries}.\operatorname{coeff}\left(i.\operatorname{val}\right)\left((\operatorname{canonicalSeries}\left(N\right)\left(x\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.coefficientEquiv_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The coordinates of a quotient element are the coefficients of its representative series.

**Theorem 1.30 (image square annihilator).**

$$\forall (N: \operatorname{Nat}), \forall (k: \operatorname{Nat}), (k \le N + 1) \Rightarrow (\forall (v: \operatorname{Units}\left((\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))\right)), \forall (w: \operatorname{Units}\left((\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))\right)), \forall (s: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), ((\exists (delta: (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))), (\operatorname{truncateMap}\left(N\right)\left((\operatorname{PowerSeries}.\operatorname{X}^{k} \cdot (v : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))) \cdot delta^{2})\right) = 0) \land (\operatorname{truncateMap}\left(N\right)\left((\operatorname{PowerSeries}.\operatorname{X}^{k} \cdot (v : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))) \cdot (w : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right))) \cdot delta)\right) = \operatorname{truncateMap}\left(N\right)\left(s\right)))) \Leftrightarrow ((\operatorname{PowerSeries}.\operatorname{X} : (\operatorname{PowerSeries}\left((\operatorname{ZMod}\left(2\right))\right)))^{(k + \operatorname{Nat}.\operatorname{div}\left((N + 1 - k + 1), 2\right))} \mid s))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.image_square_annihilator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

For two unit multipliers, the image subject to the square-annihilator constraint is exactly the displayed coefficient tail. Nat.div denotes floor division on natural numbers.

**Theorem 1.31 (claim of sum).**

$$(\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left(\operatorname{a}\left(n\right) = \operatorname{prefixCount}\left((n - 1)\right)\right)) \Rightarrow ((\operatorname{a}\left(1\right) = 1) \land ((\operatorname{a}\left(2\right) = 2) \land (((\forall (n: \operatorname{Nat}), \left(3 \le n\right) \to \left((\operatorname{a}\left(n\right) : \operatorname{Int}) = 8 \cdot (\operatorname{a}\left((n - 2)\right) : \operatorname{Int}) - 4\right))) \land (((\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left((\operatorname{a}\left((n + 1)\right) : \operatorname{Int}) - (\operatorname{a}\left(n\right) : \operatorname{Int}) = (2 : \operatorname{Int})^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot (n - 1), 2\right))}\right))) \land (((\forall (n: \operatorname{Nat}), \left(1 \le n\right) \to \left(\operatorname{a}\left(n\right) = 1 + \sum_{k \in \operatorname{Finset}.\operatorname{range}\left((n - 1)\right)} 2^{(\operatorname{Nat}.\operatorname{div}\left(3 \cdot k, 2\right))}\right))) \land (((\forall (n: \operatorname{Nat}), \left(2 \le n\right) \to \left(\operatorname{a}\left(n\right) = \operatorname{a113836}\left((n - 1)\right) + 1\right))) \land (((\forall (k: \operatorname{Nat}), \left(1 \le k\right) \to \left((\operatorname{a}\left((2 \cdot k)\right) : \operatorname{Rat}) = \frac{(10 \cdot (8 : \operatorname{Rat})^{(k - 1)} + 4)}{7}\right))) \land (((\forall (k: \operatorname{Nat}), (\operatorname{a}\left((2 \cdot k + 1)\right) : \operatorname{Rat}) = \frac{(3 \cdot (8 : \operatorname{Rat})^{k} + 4)}{7})) \land (\operatorname{ogf} = \operatorname{conjecturedOGF})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.claim_of_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Arnauld Mesinga Mwafise (2026). *OEIS A401496: labeled Riordan graphs with labeled Riordan complements*. URL: <https://oeis.org/A401496>.

*Commentary.*

The finite-sum formula implies the recurrence, successive differences, auxiliary sequence identity, parity formulas and generating-function identity.

## References

- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.ComplementCompatible`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.IsLabeledRiordan`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.a`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.a001651`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.a113836`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.allOnes`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.allOnes_constant`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.canonicalSeries`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.claim`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.claim_of_sum`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.coefficientEquiv`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.coefficientEquiv_apply`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.complement_orientation_card`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.conjecturedOGF`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.count_one`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.image_square_annihilator`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.modulusDegree`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.monicModulus`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.ogf`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.prefixCount`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.riordanGraph`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.shifted_square_divisibility`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_canonicalSeries`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_eq_iff`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_eq_zero_iff`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncateMap_isUnit`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncatedCoeff`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.truncatedCoeff_truncateMap`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.unit_parameter_criterion`
- Truth anchor: `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.zero_prefix_card`
