# Manju–Sharma Conjecture 4.4: the printed criterion fails

## Abstract

The printed adjugate denominator accepts a noninner derivation on the actual fourth cyclotomic integer ring.

The source is Manju and Sharma, Twisted Derivations in Algebraic Number Fields, arXiv:2412.03507v2, Definition 2.1 and Section 4.2, Conjectures 4.3–4.4. The original TeX reference in 4.4 is to 4.3. Its denominator is p to the e, not the absolute determinant p to the power p to the e. The original version 1 also prints that denominator. Adjugate means classical adjugate. The source locators are TeX lines 120, 135–137, 470–472, 1276–1277, 1281–1283 and 1287–1289. Table 3 has the opposite matrix sign in this case; the defining multiplication operator in Section 4 fixes the sign used here.

**Definition 1.1 (Integral innerness).**

$$\forall O \in Type,\; (\operatorname{CommRing}\left(O\right)) \Rightarrow (\forall sigma \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall tau \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall D \in \operatorname{LinearMap}\left(Int, O, O\right),\; (\operatorname{IsInner}\left(sigma, tau, D\right)) \Leftrightarrow (\exists gamma \in O,\; \forall x \in O,\; \operatorname{apply}\left(D, x\right) = gamma \cdot \operatorname{apply}\left(tau, x\right) - \operatorname{apply}\left(sigma, x\right) \cdot gamma))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.IsInner` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

For every commutative ring O with its integer algebra structure, sigma and tau are integer-algebra endomorphisms and D is integer-linear. The witness gamma belongs to O itself. The equation is required for every x, exactly as in Definition 2.1.

**Definition 1.2 (The literal printed integrality test).**

$$\forall iota \in Type,\; ((\operatorname{Fintype}\left(iota\right)) \land (\operatorname{DecidableEq}\left(iota\right))) \Rightarrow (\forall p \in Nat,\; \forall e \in Nat,\; \forall A \in \operatorname{Matrix}\left(iota, iota, Int\right),\; \forall C \in \operatorname{Function}\left(iota, Int\right),\; (\operatorname{PrintedIntegralTest}\left(p, e, A, C\right)) \Leftrightarrow (\exists X \in \operatorname{Function}\left(iota, Int\right),\; \forall i \in iota,\; \operatorname{inverse}\left(\operatorname{rat}\left(p\right)^{e}\right) \cdot \operatorname{apply}\left(\operatorname{mulVec}\left(\operatorname{rat}\left(\operatorname{adjugate}\left(A\right)\right), \operatorname{rat}\left(C\right)\right), i\right) = \operatorname{rat}\left(\operatorname{apply}\left(X, i\right)\right)))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.PrintedIntegralTest` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The arbitrary finite decidable index type iota indexes a square integer matrix and an integer column. rat denotes coefficientwise inclusion into the rationals; inverse is rational inversion. There must be an integer vector X equal coordinatewise to the rational vector inverse(p^e) times adjugate(A)C. No integral solution of AX=C is assumed.

**Definition 1.3 (The full universal source claim).**

$$(claim) \Leftrightarrow (\forall p \in Nat,\; \forall k \in Nat,\; ((\operatorname{Prime}\left(p\right)) \land ((k \ne 1) \land (3 \le p^{k}))) \Rightarrow (\forall K \in Type,\; ((\operatorname{Field}\left(K\right)) \land ((\operatorname{NumberField}\left(K\right)) \land ((\operatorname{IsCyclotomicExtension}\left(\operatorname{singleton}\left(p^{k}\right), Rat, K\right)) \land (\operatorname{NeZero}\left(p^{k}\right))))) \Rightarrow (\forall zeta \in K,\; (\operatorname{IsPrimitiveRoot}\left(zeta, p^{k}\right)) \Rightarrow (\forall pb \in \operatorname{PowerBasis}\left(Int, \operatorname{RingOfIntegers}\left(K\right)\right),\; ((\operatorname{gen}\left(pb\right) = \operatorname{toInteger}\left(zeta\right)) \land (\operatorname{dim}\left(pb\right) = p^{k - 1} \cdot \left(p - 1\right))) \Rightarrow (\forall sigma \in \operatorname{AlgHom}\left(Int, \operatorname{RingOfIntegers}\left(K\right), \operatorname{RingOfIntegers}\left(K\right)\right),\; \forall tau \in \operatorname{AlgHom}\left(Int, \operatorname{RingOfIntegers}\left(K\right), \operatorname{RingOfIntegers}\left(K\right)\right),\; (sigma \ne tau) \Rightarrow (\forall u \in Nat,\; \forall v \in Nat,\; \forall e \in Nat,\; \forall m \in Nat,\; ((u < p^{k}) \land ((v < p^{k}) \land ((\operatorname{Coprime}\left(u, p^{k}\right)) \land ((\operatorname{Coprime}\left(v, p^{k}\right)) \land ((u \ne v) \land ((\operatorname{apply}\left(sigma, \operatorname{toInteger}\left(zeta\right)\right) = \operatorname{toInteger}\left(zeta\right)^{u}) \land ((\operatorname{apply}\left(tau, \operatorname{toInteger}\left(zeta\right)\right) = \operatorname{toInteger}\left(zeta\right)^{v}) \land ((0 < m) \land ((\neg p \mid m) \land (v = u + p^{e} \cdot m)))))))))) \Rightarrow (\forall D \in \operatorname{LinearMap}\left(Int, \operatorname{RingOfIntegers}\left(K\right), \operatorname{RingOfIntegers}\left(K\right)\right),\; (\forall x \in \operatorname{RingOfIntegers}\left(K\right),\; \forall y \in \operatorname{RingOfIntegers}\left(K\right),\; \operatorname{apply}\left(D, x \cdot y\right) = \operatorname{apply}\left(D, x\right) \cdot \operatorname{apply}\left(tau, y\right) + \operatorname{apply}\left(sigma, x\right) \cdot \operatorname{apply}\left(D, y\right)) \Rightarrow (((\operatorname{IsInner}\left(sigma, tau, D\right)) \Leftrightarrow (\operatorname{PrintedIntegralTest}\left(p, e, \operatorname{leftMulMatrix}\left(\operatorname{basis}\left(pb\right), \operatorname{apply}\left(tau, \operatorname{toInteger}\left(zeta\right)\right) - \operatorname{apply}\left(sigma, \operatorname{toInteger}\left(zeta\right)\right)\right), \operatorname{repr}\left(\operatorname{basis}\left(pb\right), \operatorname{apply}\left(D, \operatorname{toInteger}\left(zeta\right)\right)\right)\right))) \land (((\forall i \in \operatorname{Fin}\left(p^{k - 1} \cdot \left(p - 1\right)\right),\; \operatorname{intCast}\left(p\right)^{e} \mid \operatorname{apply}\left(\operatorname{repr}\left(\operatorname{basis}\left(pb\right), \operatorname{apply}\left(D, \operatorname{toInteger}\left(zeta\right)\right)\right), i\right)) \Rightarrow (\operatorname{IsInner}\left(sigma, tau, D\right))) \land ((\forall i \in \operatorname{Fin}\left(p^{k - 1} \cdot \left(p - 1\right)\right),\; \operatorname{intCast}\left(p\right) \mid \operatorname{apply}\left(\operatorname{repr}\left(\operatorname{basis}\left(pb\right), \operatorname{apply}\left(D, \operatorname{toInteger}\left(zeta\right)\right)\right), i\right)) \Rightarrow (\operatorname{IsInner}\left(sigma, tau, D\right))))))))))))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.claim` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

All natural primes p and admissible k are quantified, with k unequal to one and p^k at least three. The field K is a rational cyclotomic number field with a primitive p^k root zeta, and O is its actual RingOfIntegers. The integral root z is toInteger(zeta). Every ordered integral power basis pb with generator z and dimension p^(k-1)(p-1) is included. The two distinct algebra endomorphisms preserve one and hence are nonzero. The representatives u and v lie below p^k, are coprime to it and distinct; their root images and the factorization v=u+p^e*m are explicit. Here e is nonnegative, m positive and p does not divide m. Every integer-linear D obeying the twisted law on every pair x,y is included. A is literally leftMulMatrix of tau(z)-sigma(z) in pb.basis and C is literally repr(D(z)); the formula repeats these definitions instead of quantifying independent matrices. Both extra sufficient implications are retained.

**Definition 1.4 (The actual fourth cyclotomic field).**

$$K4 = \operatorname{CyclotomicField}\left(4, Rat\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.K4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

K4 is Mathlib's CyclotomicField 4 Rat with its field, number-field and rational cyclotomic instances.

**Definition 1.5 (Its actual algebraic integer ring).**

$$O4 = \operatorname{RingOfIntegers}\left(K4\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.O4` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

O4 is the actual ring of integers, rather than an independently stipulated quadratic pair algebra.

**Definition 1.6 (A primitive fourth root).**

$$root = \operatorname{zeta}\left(4, Rat, K4\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.root` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The existing zeta_spec theorem proves that this chosen field element has exact order four.

**Definition 1.7 (The corresponding integral root).**

$$z = \operatorname{toInteger}\left(root\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The integral primitive-root API supplies z in O4. The private z_sq proves z*z=-1.

**Definition 1.8 (The existing integral power basis).**

$$pb = \operatorname{integralPowerBasis}\left(root\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.pb` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The existing integralPowerBasis_dim theorem computes dimension two. Its verified reindex b is the ordered basis (1,z), not a replacement carrier or an assumed Gaussian identification.

**Definition 1.9 (A proved generator-preserving Gaussian equivalence).**

$$\forall a \in Int,\; \forall c \in Int,\; \operatorname{apply}\left(gaussianEquiv, \operatorname{gaussian}\left(a, c\right)\right) = \operatorname{intCast}\left(a\right) + \operatorname{intCast}\left(c\right) \cdot z$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.gaussianEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

Zsqrtd.lift constructs a ring homomorphism from GaussianInt using z*z=-1. Nonsquareness of minus one gives injectivity by the upstream lift_injective theorem. Reconstruction using the actual two-term integral basis gives surjectivity. Thus gaussianEquiv is an actual integer-algebra equivalence and sends the Gaussian generator to z. This supplies the multiplication and coordinate bridge; no identification is an extra hypothesis.

**Definition 1.10 (Conjugation on the actual integer ring).**

$$\forall x \in O4,\; \operatorname{apply}\left(tau, x\right) = \operatorname{apply}\left(gaussianEquiv, \operatorname{star}\left(\operatorname{apply}\left(\operatorname{symm}\left(gaussianEquiv\right), x\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.tau` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

Conjugation is transported through the proved algebra equivalence. It is an integer-algebra endomorphism and sends z to -z=z^3. The other twist is the identity, with u=1 and v=3.

**Definition 1.11 (The transported imaginary-coordinate map).**

$$\forall x \in O4,\; \operatorname{apply}\left(derivation, x\right) = \operatorname{apply}\left(gaussianEquiv, \operatorname{gaussian}\left(\operatorname{im}\left(\operatorname{apply}\left(\operatorname{symm}\left(gaussianEquiv\right), x\right)\right), 0\right)\right)$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.derivation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The Gaussian imaginary coordinate is an additive map and therefore integer-linear. Transport gives D(a+bz)=b as an O4-valued integer-linear map. The all-input Gaussian product identity D(xy)=D(x)conjugate(y)+xD(y) is proved by coordinate multiplication and transported. Thus no generator-only check replaces the full twisted Leibniz law.

**Theorem 1.12 (The full printed Conjecture 4.4 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.result` (`✓ std3`). ∎

*Resolves.* `Problems/manju-sharma-2024-conjecture-4-4-refutation` (refuted) by `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"manju-sharma-2024-conjecture-4-4-refutation","declaration_gid":"D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

Take p=2, k=2, n=4, u=1, v=3, e=1 and m=1. All unit, ordering, prime and factorization conditions hold. In the actual ordered integral basis (1,z), tau(z)-z=-2z, so multiplication has columns (0,-2) and (2,0). The actual matrix is [[0,2],[-2,0]] and the actual vector of D(z)=1 is (1,0). Its classical adjugate is [[0,-2],[2,0]], so the literal printed test gives (1/2)adj(A)C=(0,1), an integer vector. The determinant is 4, consistent with the inherited conjectural value plus or minus 2^(2^1). That determinant is a consequence of this matrix, never a premise of the claim or counterexample.

If an integral gamma=a+bz made D inner, evaluation at z would give 1=gamma*(-z)-z*gamma=2b-2az. The real coordinate forces 1=2b, impossible over the integers. The proof pulls gamma back along the actual proved equivalence; it does not assume existence of an integral solution. The full universal iff would force this noninner D to be inner because its printed test holds. This contradicts the parity equation and proves literally Not claim.

The counterexample negates the entire conjunction comprising the iff and both additional sufficient assertions. It does not separately refute either sufficient assertion, a corrected determinant-denominator statement, Conjecture 4.3 in general, or a corrigendum. Both sufficient assertions have false antecedents here, since the first coordinate of C is one. The quadratic classification is prior literature. The conclusion concerns the literal printed named conjecture; it makes no global priority claim.

## References

- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.IsInner`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.K4`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.O4`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.PrintedIntegralTest`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.claim`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.derivation`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.gaussianEquiv`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.pb`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.result`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.root`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.tau`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour.z`
