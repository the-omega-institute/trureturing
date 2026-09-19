# Sharma's primitive-polynomial Conjecture 4.2 is false

## Abstract

A degree-41 finite-field certificate refutes Sharma's full primitive-polynomial conjecture.

**Definition 1.1 (The source multiplicative-generator property).**

$$(\operatorname{SourcePrimitivePolynomial}\left(p, K, f\right)) \Leftrightarrow (\exists L \in Type,\; ((\operatorname{Field}\left(L\right)) \land ((\operatorname{Fintype}\left(L\right)) \land (\operatorname{Algebra}\left(K, L\right)))) \land (\exists alpha \in L,\; (\operatorname{finrank}\left(K, L\right) = p) \land ((\operatorname{minpoly}\left(K, alpha\right) = f) \land (\operatorname{orderOf}\left(alpha\right) = \operatorname{card}\left(L\right) - 1))))$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.SourcePrimitivePolynomial` (`✓ std3`).

*Citation.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

SourcePrimitivePolynomial is the source meaning of monic minimal polynomial: there must be an extension L of degree p containing an element alpha whose minimal polynomial is the displayed polynomial and whose multiplicative order is card(L)-1. This is not Polynomial.IsPrimitive, which is the unrelated coefficient-content predicate.

**Definition 1.2 (A multiplicative generator in the base field).**

$$(\operatorname{PrimitiveLambda}\left(lambda\right)) \Leftrightarrow (\operatorname{orderOf}\left(lambda\right) = \operatorname{card}\left(K\right) - 1)$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.PrimitiveLambda` (`✓ std3`).

*Citation.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

PrimitiveLambda(lam) means orderOf lam equals card(K)-1. The source quantifies over every such lambda in every finite field of cardinality p squared.

**Definition 1.3 (The source leading coefficient).**

$$SourceLeadingCoefficient = 1$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.SourceLeadingCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The actual source coefficient is 1 in Fin 2. This constant occurs in the original public theorem statement and is also the arena input state.

**Definition 1.4 (The coefficient-parameterized source polynomial).**

$$\operatorname{sourcePolynomial}\left(p, c, lambda\right) = \operatorname{C}\left(\operatorname{val}\left(c\right)\right) \cdot X^{p} + X + \operatorname{C}\left(lambda\right)$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.sourcePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

For a coefficient cut c, sourcePolynomial is C(val(c)) X^p + X + C(lam). The actual source coefficient is the Fin 2 value 1; the coefficient parameter is retained in the full family so that the law measures the stated input.

**Definition 1.5 (The complete universal source claim at one coefficient).**

$$(\operatorname{claimFor}\left(c\right)) \Leftrightarrow (\forall p \in Nat,\; ((\operatorname{Prime}\left(p\right)) \land (\operatorname{Odd}\left(p\right))) \Rightarrow (\forall K \in Type,\; ((\operatorname{Field}\left(K\right)) \land ((\operatorname{Fintype}\left(K\right)) \land (\operatorname{CharP}\left(K, p\right)))) \Rightarrow ((\operatorname{card}\left(K\right) = p^{2}) \Rightarrow (\forall lambda \in \operatorname{Element}\left(K\right),\; (\operatorname{PrimitiveLambda}\left(lambda\right)) \Rightarrow (\operatorname{SourcePrimitivePolynomial}\left(p, K, \operatorname{sourcePolynomial}\left(p, c, lambda\right)\right))))))$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.claimFor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The quantifier order is the source order: every natural odd prime p, every finite field K of cardinality p squared and characteristic p, and every multiplicative generator lambda. No coefficient-content interpretation or finite-prime weakening is substituted.

**Definition 1.6 (Sharma's full Conjecture 4.2).**

$$fullClaim \Leftrightarrow \left(\forall p \in Nat,\; ((\operatorname{Prime}\left(p\right)) \land (\operatorname{Odd}\left(p\right))) \Rightarrow (\forall K \in Type,\; ((\operatorname{Field}\left(K\right)) \land ((\operatorname{Fintype}\left(K\right)) \land (\operatorname{CharP}\left(K, p\right)))) \Rightarrow ((\operatorname{card}\left(K\right) = p^{2}) \Rightarrow (\forall lambda \in \operatorname{Element}\left(K\right),\; (\operatorname{PrimitiveLambda}\left(lambda\right)) \Rightarrow (\operatorname{SourcePrimitivePolynomial}\left(p, K, \operatorname{sourcePolynomial}\left(p, 1, lambda\right)\right)))))\right)$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullClaim` (`✓ std3`).

*Citation.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

This is the literal global conjecture with SourcePrimitivePolynomial as its conclusion. Its negation is the public result below.

**Definition 1.7 (The public negation target).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.publicResult`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.publicResult` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

publicResult is definitionally the negation of claimFor SourceLeadingCoefficient. The Lean theorem result proves this proposition unconditionally.

**Definition 1.8 (The executable quadratic field at p equals 41).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.QuadraticField41`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.QuadraticField41` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The counterexample arena is QuadraticAlgebra (ZMod 41) 3 0, with the nonsquare witness and finite cardinality supplied in Lean. Its cardinality is 41 squared.

**Definition 1.9 (The primitive lambda certificate).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.lambda41`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.lambda41` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

lambda41 is the element 5 + u in the quadratic algebra. The kernel-checked power chain proves order 1680, which is the nonzero-group order 1681 minus one.

**Definition 1.10 (The dense coefficient list).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificateCoefficients`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificateCoefficients` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The eight-product certificate starts from the explicit 41-entry coefficient list. Every list entry is a concrete element of the quadratic field and is consumed by the kernel-checked coefficient reducer.

**Definition 1.11 (The certificate polynomial).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificatePolynomial`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificatePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

certificatePolynomial is the Horner polynomial reconstructed from the full coefficient list. Its product identities are checked in the kernel rather than imported as a numeric assertion.

**Definition 1.12 (The hypothetical extension group order).**

$$certificateN = 1681^{41} - 1$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificateN` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The hypothetical degree-41 extension has this nonzero-group order. It is divisible by 83, and its quotient by 83 is positive and strictly smaller.

**Definition 1.13 (The universal root certificate).**

$$\forall L \in Type,\; ((\operatorname{Field}\left(L\right)) \land (\operatorname{Algebra}\left(QuadraticField41, L\right))) \Rightarrow (\forall alpha \in L,\; (\operatorname{aeval}\left(alpha, \operatorname{sourcePolynomial}\left(41, c, lambda41\right)\right) = 0) \Rightarrow (\operatorname{aeval}\left(alpha, certificatePolynomial\right)^{83} = alpha))$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.denseCertificateIdentityFor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

For every field extension L and every root alpha of the coefficient-dependent source polynomial, evaluating the certificate polynomial gives z with z^83 = alpha. This is the certificate-dependent obstruction used in the full refutation.

**Definition 1.14 (The complete coefficient-sensitive law).**

$$(\operatorname{natDegree}\left(\operatorname{sourcePolynomial}\left(41, c, lambda41\right)\right) = 41) \land ((\operatorname{denseCertificateIdentityFor}\left(c\right)) \land (\neg \operatorname{claimFor}\left(c\right)))$$

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullCounterexampleLaw` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The law contains all three substantive components: actual degree 41, the universal root certificate, and negation of the full claim at the observed coefficient. Changing the coefficient to zero gives degree one, so the altered law fails and the readout is genuinely varied and slot-sensitive.

**Definition 1.15 (The finite source counterexample arena).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.sourceCounterexampleArena`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.sourceCounterexampleArena` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The arena's law reads the actual coefficient SourceLeadingCoefficient from the registered state and then applies fullCounterexampleLaw. The inline registration constructs a LegacyPrimitiveRealization equivalence: the forward direction proves the source degree and certificate and retains the incoming claim negation; the reverse direction projects that negation.

**Definition 1.16 (The actual source coefficient realization).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.actualSourceCoefficientRealization`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.actualSourceCoefficientRealization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The actual realization returns each coefficient cut unchanged. It therefore reads the source coefficient 1 through the enrolled direct record and feeds that value into the degree, certificate, and claim-negation law.

**Definition 1.17 (The altered coefficient realization).**

Lean statement: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.alternateSourceCoefficientRealization`

*Formalization.* `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.alternateSourceCoefficientRealization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

The altered realization returns coefficient zero. Its degree-one polynomial proves the required sensitivity witness for the same declared law.

**Theorem 1.18 (The full source conjecture is false).**

$$\neg fullClaim$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Avnish K. Sharma (2026). *Primitive Polynomials of the Form g(x)+λ over Finite Fields: Non-Existence Results and Conjectures*. URL: <https://arxiv.org/abs/2608.07262v2>.

*Commentary.*

At p=41 take K = QuadraticAlgebra (ZMod 41) 3 0 and lambda = 5 + u. The certificate proves lambda has full multiplicative order 1680. If the source claim supplied an extension L of degree 41 with a primitive root alpha of the polynomial X^41 + X + lambda, the eight exact product identities would give z^83 = alpha. Since L has cardinality 1681^41, the finite-field exponent gives z^(card(L)-1)=1, hence alpha^((1681^41-1)/83) = 1. This forces the claimed order card(L)-1 to divide a strict smaller positive exponent, a contradiction. Thus the full universal conjecture is negated unconditionally. The certificate is for the source multiplicative-generator/minimal-polynomial meaning, not a polynomial coefficient-content surrogate.

## References

- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.PrimitiveLambda`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.QuadraticField41`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.SourceLeadingCoefficient`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.SourcePrimitivePolynomial`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.actualSourceCoefficientRealization`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.alternateSourceCoefficientRealization`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificateCoefficients`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificateN`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.certificatePolynomial`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.claimFor`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.denseCertificateIdentityFor`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullClaim`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.fullCounterexampleLaw`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.lambda41`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.publicResult`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.result`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.sourceCounterexampleArena`
- Truth anchor: `D5/S3/ArithUnits/SharmaPrimitivePolynomialRefutation.sourcePolynomial`
