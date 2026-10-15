# Integral sign gluing and coefficient halves

## Abstract

Integral sign components are glued by their literal common residue, with a canonical inverse.

For q natural put S(q)=sum over k<q of X^k, f(q)=X^q-S(q), g(q)=X^q+S(q), F(q)=f(q)g(q), and W(q)=S(q)-(X-1)X^q. Plus(q) and Minus(q) are the literal integer polynomial quotients by f and g. reduce maps each integer coefficient to ZMod 2 and fixes X. Common(q) is (ZMod 2)[X]/reduce(g(q)); g(q)=S(q+1). The ring maps rplus and rminus descend this same coefficient reduction. Compatible(q) is their RingHom.pullback subring of Plus(q) times Minus(q). fp is the original ResetSignIntegerCyclic quotient map.

**Theorem 1.1 (The actual sum and intersection ideals).**

$$\forall q \in Nat,\; \operatorname{sup}\left(\operatorname{span}\left(\operatorname{f}\left(q\right)\right), \operatorname{span}\left(\operatorname{g}\left(q\right)\right)\right) = \operatorname{spanPair}\left(2, \operatorname{g}\left(q\right)\right) \land \operatorname{inf}\left(\operatorname{span}\left(\operatorname{f}\left(q\right)\right), \operatorname{span}\left(\operatorname{g}\left(q\right)\right)\right) = \operatorname{span}\left(\operatorname{F}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.sign_ideals` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

span is the principal ideal in Int[X], spanPair generates an ideal with two elements, and sup and inf are the ideal sum and intersection. The geometric identity supplied by ResetSignIntegerCyclic gives X*f+(2-X)*g=2. Since f=g-2*S, the sum is (2,g). For a common multiple f*a=g*b the same certificate makes 2*b a multiple of f. Take its monic f remainder. Remainders commute with integer scalar multiplication, and each integer coefficient is free of two-torsion. Thus f divides b and F divides the common multiple. Integral comaximality is neither assumed nor used.

**Theorem 1.2 (Compatibility detects every even remainder coefficient).**

$$\forall q \in Nat, z \in \operatorname{Compatible}\left(q\right), i \in Nat,\; \operatorname{divides}\left(2, \operatorname{coeff}\left(\operatorname{sub}\left(\operatorname{a0}\left(q, \operatorname{fst}\left(\operatorname{value}\left(z\right)\right)\right), \operatorname{b0}\left(q, \operatorname{snd}\left(\operatorname{value}\left(z\right)\right)\right)\right), i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.compatible_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

a0 and b0 are AdjoinRoot.modByMonicHom for the monic degree-q polynomials f and g. They are canonical representatives, including zero. Mapping these remainders to characteristic two agrees with the common monic remainder. The compatibility equation therefore makes reduce(a0-b0)=0, so every integer coefficient is even. No nonnegative-coefficient assumption is present.

**Theorem 1.3 (The literal equivalence and both inverse identities).**

$$\forall q \in Nat,\; \operatorname{positive}\left(q\right) \Rightarrow \left(\left(\forall v \in \operatorname{QF}\left(q\right),\; \operatorname{fromCompatible}\left(q, \operatorname{toCompatible}\left(q, v\right)\right) = v\right) \land \left(\left(\forall z \in \operatorname{Compatible}\left(q\right),\; \operatorname{toCompatible}\left(q, \operatorname{fromCompatible}\left(q, z\right)\right) = z\right) \land \left(\left(\forall p \in IntPolynomial,\; \operatorname{value}\left(\operatorname{gluing}\left(q, \operatorname{fp}\left(q, p\right)\right)\right) = \operatorname{pair}\left(\operatorname{mk}\left(\operatorname{f}\left(q\right), p\right), \operatorname{mk}\left(\operatorname{g}\left(q\right), p\right)\right)\right) \land \left(\left(\forall z \in \operatorname{Compatible}\left(q\right),\; \operatorname{inverseApply}\left(\operatorname{gluing}\left(q\right), z\right) = \operatorname{fp}\left(q, \operatorname{sub}\left(\operatorname{a0}\left(q, \operatorname{fst}\left(\operatorname{value}\left(z\right)\right)\right), \operatorname{mul}\left(\operatorname{mul}\left(X, \operatorname{f}\left(q\right)\right), \operatorname{half}\left(\operatorname{sub}\left(\operatorname{a0}\left(q, \operatorname{fst}\left(\operatorname{value}\left(z\right)\right)\right), \operatorname{b0}\left(q, \operatorname{snd}\left(\operatorname{value}\left(z\right)\right)\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall z \in \operatorname{Compatible}\left(q\right),\; \operatorname{degreeLess}\left(\operatorname{a0}\left(q, \operatorname{fst}\left(\operatorname{value}\left(z\right)\right)\right), q\right) \land \operatorname{degreeLess}\left(\operatorname{b0}\left(q, \operatorname{snd}\left(\operatorname{value}\left(z\right)\right)\right), q\right)\right) \land \left(\forall z \in \operatorname{Compatible}\left(q\right),\; \operatorname{half}\left(\operatorname{sub}\left(\operatorname{a0}\left(q, \operatorname{fst}\left(\operatorname{value}\left(z\right)\right)\right), \operatorname{b0}\left(q, \operatorname{snd}\left(\operatorname{value}\left(z\right)\right)\right)\right)\right) = \operatorname{coefficientHalfRangeSum}\left(q, \operatorname{sub}\left(\operatorname{a0}\left(q, \operatorname{fst}\left(\operatorname{value}\left(z\right)\right)\right), \operatorname{b0}\left(q, \operatorname{snd}\left(\operatorname{value}\left(z\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.integral_gluing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

positive(q) means 0<q. degreeLess is polynomial degree strictly below q, including zero. coefficientHalfRangeSum(q,p) is sum over i<q of monomial i (p.coeff(i)/2). mk denotes the indicated polynomial quotient map; value forgets pullback membership. half divides every coefficient by 2 using integer Euclidean division, so negative coefficients are included. Since a0-b0=2*half(a0-b0), the polynomial p=a0-X*f*half(a0-b0) projects to a0 modulo f and to b0 modulo g: p-b0=(2-X)*g*half(a0-b0). This proves the pullback-side inverse identity. The intersection ideal identity reflects equality from both components back to QF, proving the other inverse identity. gluing has toCompatible as its forward ring homomorphism and this exact fromCompatible as its inverse. All positive q, including q=1, are retained; no entropy assertion occurs.

**Theorem 1.4 (Forward time, original sign, scalars and the common quotient).**

$$\forall q \in Nat,\; \operatorname{value}\left(\operatorname{gluing}\left(q, \operatorname{fp}\left(q, X\right)\right)\right) = \operatorname{pair}\left(\operatorname{root}\left(\operatorname{f}\left(q\right)\right), \operatorname{root}\left(\operatorname{g}\left(q\right)\right)\right) \land \left(\operatorname{value}\left(\operatorname{gluing}\left(q, \operatorname{fp}\left(q, \operatorname{W}\left(q\right)\right)\right)\right) = \operatorname{pair}\left(1, \operatorname{neg}\left(1\right)\right) \land \left(\left(\forall z \in Int,\; \operatorname{value}\left(\operatorname{gluing}\left(q, \operatorname{fp}\left(q, \operatorname{C}\left(z\right)\right)\right)\right) = \operatorname{pair}\left(\operatorname{integerCastPlus}\left(z\right), \operatorname{integerCastMinus}\left(z\right)\right)\right) \land \left(\left(\forall p \in IntPolynomial,\; \operatorname{commonQuotientEquiv}\left(q, \operatorname{mkSumIdeal}\left(p\right)\right) = \operatorname{commonPolynomial}\left(q, p\right)\right) \land \operatorname{reduce}\left(\operatorname{g}\left(q\right)\right) = \operatorname{geometricSum}\left(\operatorname{succ}\left(q\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.gluing_generators` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

commonQuotientEquiv identifies Int[X] modulo the actual sum ideal with Common(q). Its map is literally coefficient reduction followed by the common quotient, fixing X. Its kernel proof uses monic division by g and evenness of the remainder; coefficient lifts give surjectivity. The identities W=1-X*f and W=-1+(2-X)*g give the two sign images. Each integer maps to the same integer in both components. At q=1 this is the congruence pullback of two copies of Int over the two-element field.

The construction is a repository derivation from standard quotient, monic division and pullback APIs in pinned Mathlib, together with ResetSignIntegerCyclic's literal geometric certificate. It supplies the integral reconstruction used by ResetIntegralUnits and the original native action in ResetNativeUnitNormalForm; no literature novelty is claimed. Uniform eigenlattices, conductor, additive cokernel and common-residue action are further consequences requiring their own statements. Compatible is a subring containing one, so its quotient inside the product would be additive, not a ring quotient.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.compatible_even`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.gluing_generators`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.integral_gluing`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetIntegralGluing.sign_ideals`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetSignIntegerCyclic](ResetSignIntegerCyclic.md)
