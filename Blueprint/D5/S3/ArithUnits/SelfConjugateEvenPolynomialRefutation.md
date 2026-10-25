# Self-conjugate even polynomials and a uniform degree obstruction

## Abstract

Every odd power of X^4+X^2 from the third onward obstructs the proposed sparse-power characterization.

Throughout, R is the formal polynomial ring F2[X], X is its indeterminate, C embeds a field element as a constant polynomial, comp denotes polynomial composition, coeff denotes a coefficient, and support is the finite set of exponents with nonzero coefficients. The notation natDegree is the natural degree used by Lean; every family member considered below is nonzero. Equalities are formal polynomial equalities, rather than equalities of functions on F2.

**Definition 1.1 (The coefficient field).**

$$F2 = \operatorname{ZMod}\left(2\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.F2` (`✓ std3`).

*Citation.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

F2 is ZMod 2, the field with two elements. All coefficients and arbitrary constants in the representations below belong to this same field.

**Definition 1.2 (The invariant base polynomial).**

$$U = X^{4} + X^{2}$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Acknowledgement.* Sandro Mattarei and Marco Pizzato (2017). *Generalizations of self-reciprocal polynomials*. DOI: [10.1016/j.ffa.2017.08.004](https://doi.org/10.1016/j.ffa.2017.08.004). URL: <https://arxiv.org/abs/1609.07677v2>.

*Commentary.*

In characteristic two, (X+1)^2 = X^2+1 and (X+1)^4 = X^4+1. The two constant terms cancel, so U.comp(X+1)=U. Its highest term has coefficient one, and its degree is four. Also U=(X^2+X)^2. More generally, for any prime p and field K of characteristic p, with indeterminate T, the polynomials in K[T] fixed by translation T+1 are polynomials in T^p-T. This is the existing result in Section 5 of the second reference; the family calculation here uses Frobenius directly.

**Definition 1.3 (The entire power family).**

$$\forall r \in \mathbb{N},\; \operatorname{P}\left(r\right) = U^{r}$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.P` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

P is defined for every natural r, including zero. The obstruction uses every odd r at least three, without an upper bound. Composition preserves powers, hence every P(r) is fixed by translation by one. Monicity is preserved by powers, giving degree 4r.

**Definition 1.4 (All simultaneous witness properties).**

$$\forall r \in \mathbb{N},\; \operatorname{FamilyEvent}\left(r\right) \Leftrightarrow \left(\operatorname{P}\left(r\right) \ne 0 \land \left(\operatorname{Monic}\left(\operatorname{P}\left(r\right)\right) \land \left(\operatorname{comp}\left(\operatorname{P}\left(r\right), X + 1\right) = \operatorname{P}\left(r\right) \land \left(\left(\forall n \in \mathbb{N},\; n \in \operatorname{support}\left(\operatorname{P}\left(r\right)\right) \Rightarrow \operatorname{Even}\left(n\right)\right) \land \left(\operatorname{natDegree}\left(\operatorname{P}\left(r\right)\right) = 4 \cdot r \land \left(\operatorname{Even}\left(\operatorname{natDegree}\left(\operatorname{P}\left(r\right)\right)\right) \land \left(\operatorname{coeff}\left(\operatorname{P}\left(r\right), 0\right) = 0 \land \left(\operatorname{Even}\left(\operatorname{card}\left(\operatorname{support}\left(\operatorname{P}\left(r\right)\right)\right)\right) \land \left(X \mid \operatorname{P}\left(r\right) \land \left(\operatorname{comp}\left(\operatorname{P}\left(r\right), -X\right) = \operatorname{P}\left(r\right) \land \left(\forall c \in F2,\; \forall m \in \mathbb{N},\; \forall k \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; \operatorname{P}\left(r\right) \ne \operatorname{C}\left(c\right) + \sum_{i \in \operatorname{Fin}\left(m\right)}X^{2^{\operatorname{k}\left(i\right)}}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.FamilyEvent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Acknowledgement.* Sandro Mattarei and Marco Pizzato (2017). *Generalizations of self-reciprocal polynomials*. DOI: [10.1016/j.ffa.2017.08.004](https://doi.org/10.1016/j.ffa.2017.08.004). URL: <https://arxiv.org/abs/1609.07677v2>.

*Commentary.*

FamilyEvent(r) contains all of the displayed clauses together. The no-representation clause quantifies over every c in F2, every natural m and every function k from Fin(m) to the naturals. Empty sums, repeated indices and k(i)=0 are included.

$\forall r \in \mathbb{N},\; \left(\operatorname{Odd}\left(r\right) \land 3 \le r\right) \Rightarrow \operatorname{FamilyEvent}\left(r\right)$

For every odd natural r at least three these properties hold. To see the even-exponent clause, write P(r) as the expansion by two of (X^2+X)^r: expansion replaces X by X^2, so its coefficients vanish at odd exponents. Since r is positive, evaluation at zero is zero, which is also the constant coefficient and implies divisibility by X. Evaluation at one is zero because U(1)=1+1=0. Every nonzero coefficient in F2 is one, so evaluation at one equals the support cardinality cast into F2. Its vanishing gives even support cardinality. The degree 4r is even, and the reflection identity follows from -X=X in characteristic two.

The degree obstruction is uniform: odd r is coprime to 2 and therefore to every 2^k for every natural k. If 4r=2^k, then r divides 2^k, forcing r=1, contrary to r at least three. Monicity gives coefficient one at exponent 4r. Each proposed powers-of-two monomial has coefficient zero there; an arbitrary constant also has coefficient zero because 4r is positive. Finite addition preserves that zero coefficient, independently of cancellations or repeated indices. This contradicts formal polynomial equality.

**Definition 1.5 (Six explicit conventional domains).**

Lean statement: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.EvenReading`

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.EvenReading` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

EvenReading has exactly six constructors: exponents, degree, support, zeroConstant, divisibleByX and reflection. The source does not define its word even. These alternatives describe the stated conventional readings without asserting a unique author-intended meaning. The zero-constant and X-divisibility alternatives are equivalent but are kept explicit.

**Definition 1.6 (The domain belonging to each reading).**

$$\forall p \in R,\; \left(\operatorname{Domain}\left(exponents, p\right) \Leftrightarrow \left(\forall n \in \mathbb{N},\; n \in \operatorname{support}\left(p\right) \Rightarrow \operatorname{Even}\left(n\right)\right)\right) \land \left(\left(\operatorname{Domain}\left(degree, p\right) \Leftrightarrow \operatorname{Even}\left(\operatorname{natDegree}\left(p\right)\right)\right) \land \left(\left(\operatorname{Domain}\left(support, p\right) \Leftrightarrow \operatorname{Even}\left(\operatorname{card}\left(\operatorname{support}\left(p\right)\right)\right)\right) \land \left(\left(\operatorname{Domain}\left(zeroConstant, p\right) \Leftrightarrow \operatorname{coeff}\left(p, 0\right) = 0\right) \land \left(\left(\operatorname{Domain}\left(divisibleByX, p\right) \Leftrightarrow X \mid p\right) \land \left(\operatorname{Domain}\left(reflection, p\right) \Leftrightarrow \operatorname{comp}\left(p, -X\right) = p\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.Domain` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

The six domain predicates respectively mean even supported exponents, even natural degree, even support cardinality, zero constant coefficient, divisibility by X, and invariance under reflection. Every eligible P(r) lies in their intersection. For this nonzero family, the natural degree is the ordinary polynomial degree.

**Definition 1.7 (Both branches of the source parity rule).**

$$\forall p \in R,\; \forall m \in \mathbb{N},\; \operatorname{SourceParity}\left(p, m\right) \Leftrightarrow \left(\left(\operatorname{coeff}\left(p, 0\right) \ne 0 \Rightarrow \operatorname{Odd}\left(m\right)\right) \land \left(\operatorname{coeff}\left(p, 0\right) = 0 \Rightarrow \operatorname{Even}\left(m\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.SourceParity` (`✓ std3`).

*Citation.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

The phrase that X^0 is a term means that the constant coefficient of p is nonzero. SourceParity retains the implication to odd m in that case and the implication to even m otherwise. For the zero-constant family, this source rule would require even m. The contradiction already excludes all m before imposing this restriction.

**Definition 1.8 (The literal displayed representation).**

$$\forall p \in R,\; \operatorname{DisplayedRepresentation}\left(p\right) \Leftrightarrow \left(\exists m \in \mathbb{N},\; \exists k \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; p = \sum_{i \in \operatorname{Fin}\left(m\right)}X^{2^{\operatorname{k}\left(i\right)}} \land \operatorname{SourceParity}\left(p, m\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.DisplayedRepresentation` (`✓ std3`).

*Citation.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

This is exactly the finite sum displayed in Conjecture 2, together with its two prose parity branches. The indices are arbitrary naturals, with no distinctness or injectivity assumption. In particular, m=0 and exponent index zero remain allowed. The display has no separate constant term; its mention of a constant in prose is preserved by SourceParity rather than silently repaired.

**Definition 1.9 (Separate optional-constant robustness).**

$$\forall p \in R,\; \operatorname{ConstantRepresentation}\left(p\right) \Leftrightarrow \left(\exists c \in F2,\; \exists m \in \mathbb{N},\; \exists k \in \operatorname{Fin}\left(m\right) \to \mathbb{N},\; p = \operatorname{C}\left(c\right) + \sum_{i \in \operatorname{Fin}\left(m\right)}X^{2^{\operatorname{k}\left(i\right)}} \land \operatorname{SourceParity}\left(p, m\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.ConstantRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

ConstantRepresentation adds an arbitrary c in F2 as C(c) while retaining the same source parity predicate. This explicitly labelled variant is broader than the literal display. The family excludes it even without the parity predicate; it is robustness of the same witnesses, rather than a replacement source assertion.

**Definition 1.10 (The complete universally quantified published iff).**

$$\forall e \in EvenReading,\; \operatorname{PublishedIff}\left(e\right) \Leftrightarrow \left(\forall p \in R,\; \operatorname{Domain}\left(e, p\right) \Rightarrow \left(\operatorname{comp}\left(p, X + 1\right) = p \Leftrightarrow \operatorname{DisplayedRepresentation}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.PublishedIff` (`✓ std3`).

*Citation.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

For each reading e, PublishedIff(e) quantifies over every formal polynomial p in R with Domain(e,p). It retains both directions of self-conjugacy if and only if the displayed representation, with both source parity branches inside that representation. No restriction to the power family is added to this universal assertion.

**Definition 1.11 (The complete optional-constant variant).**

$$\forall e \in EvenReading,\; \operatorname{OptionalConstantIff}\left(e\right) \Leftrightarrow \left(\forall p \in R,\; \operatorname{Domain}\left(e, p\right) \Rightarrow \left(\operatorname{comp}\left(p, X + 1\right) = p \Leftrightarrow \operatorname{ConstantRepresentation}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.OptionalConstantIff` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

This is the same universal iff with ConstantRepresentation on its right-hand side. Its optional constant is separate from the source display. Refuting the literal iff does not require identifying a corrected sufficient condition.

**Definition 1.12 (The disjunction of the complete interpretation alternatives).**

$$claim \Leftrightarrow \left(\exists e \in EvenReading,\; \operatorname{PublishedIff}\left(e\right) \lor \operatorname{OptionalConstantIff}\left(e\right)\right)$$

*Formalization.* `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Commentary.*

claim asserts that at least one of the six complete PublishedIff assertions or its optional-constant counterpart holds. It contains no assumption that any auxiliary family property is true. Its negation therefore refutes every complete alternative, rather than refuting a conjunction through an unrelated failed clause.

**Theorem 1.13 (Every complete alternative is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/klostermeyer-self-conjugate-even-polynomial-conjecture-2` (refuted) by `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"klostermeyer-self-conjugate-even-polynomial-conjecture-2","declaration_gid":"D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* William F. Klostermeyer (2026). *Prime Nullspace Matrices and Even Dominating Sets*. URL: <https://arxiv.org/html/2610.31475v1#Thmconj2>.

*Acknowledgement.* Sandro Mattarei and Marco Pizzato (2017). *Generalizations of self-reciprocal polynomials*. DOI: [10.1016/j.ffa.2017.08.004](https://doi.org/10.1016/j.ffa.2017.08.004). URL: <https://arxiv.org/abs/1609.07677v2>.

*Commentary.*

$\forall e \in EvenReading,\; \left(\neg \operatorname{PublishedIff}\left(e\right)\right) \land \left(\neg \operatorname{OptionalConstantIff}\left(e\right)\right)$

For every odd r at least three and every reading e, FamilyEvent(r) supplies both Domain(e,P(r)) and self-conjugacy. A displayed representation would give the excluded optional-constant equality at c=0; a ConstantRepresentation would give it at its own c. Applying the necessary direction of either complete iff to this actual P(r) is therefore contradictory. This is a full source-iff bridge under each reading, not merely a failure of an auxiliary family condition. Taking r=3 discharges existence of a witness after the uniform argument, and refutes the existential disjunction claim.

The meaning intended by the author for even remains unverified. The refutation covers the six explicit conventional domains in the published unrestricted polynomial context; an added authoritative restriction excluding this family would require a different statement. The optional-constant result is separately identified robustness. Neither a unique semantic repair nor a new invariant-algebra mechanism is asserted.

## References

- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.ConstantRepresentation`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.DisplayedRepresentation`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.Domain`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.EvenReading`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.F2`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.FamilyEvent`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.OptionalConstantIff`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.P`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.PublishedIff`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.SourceParity`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.U`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.claim`
- Truth anchor: `D5/S3/ArithUnits/SelfConjugateEvenPolynomialRefutation.result`
