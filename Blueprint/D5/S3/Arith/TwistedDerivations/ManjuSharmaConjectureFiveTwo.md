# Manju–Sharma Conjecture 5.2: the full outer criterion fails

## Abstract

The literal adjugate test in Conjecture 5.2 misses a nonzero outer class on the actual fourth cyclotomic integer ring.

The source is Manju and Sharma, Twisted Derivations in Algebraic Number Fields, arXiv:2412.03507v2, Section 5.2, Conjecture 5.2, TeX lines 2240–2242. Its inherited hypotheses are those of Conjecture 4.3, rather than the conjectural determinant conclusion. Definition 2.1 defines outer derivations as quotient classes; the Remark at TeX lines 156–158 identifies non-inner representatives with nonzero classes. The criterion and the universal strict inclusion are retained together.

**Definition 1.1 (All twisted derivations).**

$$\forall O \in Type,\; (\operatorname{CommRing}\left(O\right)) \Rightarrow (\forall sigma \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall tau \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall D \in \operatorname{LinearMap}\left(Int, O, O\right),\; (\operatorname{member}\left(D, \operatorname{derivations}\left(sigma, tau\right)\right)) \Leftrightarrow (\forall x \in O,\; \forall y \in O,\; \operatorname{apply}\left(D, x \cdot y\right) = \operatorname{apply}\left(D, x\right) \cdot \operatorname{apply}\left(tau, y\right) + \operatorname{apply}\left(sigma, x\right) \cdot \operatorname{apply}\left(D, y\right)))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.derivations` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

For any commutative ring O, sigma and tau are unital integer-algebra endomorphisms. The carrier consists of integer-linear maps satisfying the displayed identity for every x and y. Zero, addition and integer scalar multiplication preserve that identity.

**Definition 1.2 (The submodule of integral inner derivations).**

$$\forall O \in Type,\; (\operatorname{CommRing}\left(O\right)) \Rightarrow (\forall sigma \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall tau \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall D \in \operatorname{derivations}\left(sigma, tau\right),\; (\operatorname{member}\left(D, \operatorname{inner}\left(sigma, tau\right)\right)) \Leftrightarrow (\operatorname{IsInner}\left(sigma, tau, \operatorname{val}\left(D\right)\right)))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.inner` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The ambient module is the actual module of twisted derivations. Membership requires a single gamma in O valid for every input, exactly the reused IsInner definition. A multiplier only in the fraction field is insufficient. Zero, sums and integer multiples have integral multipliers.

**Definition 1.3 (The quotient class of a derivation).**

$$\forall O \in Type,\; (\operatorname{CommRing}\left(O\right)) \Rightarrow (\forall sigma \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall tau \in \operatorname{AlgHom}\left(Int, O, O\right),\; \forall D \in \operatorname{derivations}\left(sigma, tau\right),\; \operatorname{outerClass}\left(sigma, tau, D\right) = \operatorname{apply}\left(\operatorname{mkQ}\left(\operatorname{inner}\left(sigma, tau\right)\right), D\right))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.outerClass` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

The map is the canonical linear quotient map Der to Der/Inn. Mathlib's mk_eq_zero theorem gives class(D)=0 if and only if D belongs to Inn. Consequently class(D) is nonzero if and only if the representative is non-inner; the proof uses this exact equivalence.

**Definition 1.4 (The entire universal conjunction).**

$$(claim) \Leftrightarrow (\forall p \in Nat,\; \forall k \in Nat,\; ((\operatorname{Prime}\left(p\right)) \land ((k \ne 1) \land (3 \le p^{k}))) \Rightarrow (\forall K \in Type,\; ((\operatorname{Field}\left(K\right)) \land ((\operatorname{NumberField}\left(K\right)) \land ((\operatorname{IsCyclotomicExtension}\left(\operatorname{singleton}\left(p^{k}\right), Rat, K\right)) \land (\operatorname{NeZero}\left(p^{k}\right))))) \Rightarrow (\forall zeta \in K,\; (\operatorname{IsPrimitiveRoot}\left(zeta, p^{k}\right)) \Rightarrow (\forall pb \in \operatorname{PowerBasis}\left(Int, \operatorname{RingOfIntegers}\left(K\right)\right),\; ((\operatorname{gen}\left(pb\right) = \operatorname{toInteger}\left(zeta\right)) \land (\operatorname{dim}\left(pb\right) = p^{k - 1} \cdot \left(p - 1\right))) \Rightarrow (\forall sigma \in \operatorname{AlgHom}\left(Int, \operatorname{RingOfIntegers}\left(K\right), \operatorname{RingOfIntegers}\left(K\right)\right),\; \forall tau \in \operatorname{AlgHom}\left(Int, \operatorname{RingOfIntegers}\left(K\right), \operatorname{RingOfIntegers}\left(K\right)\right),\; (sigma \ne tau) \Rightarrow (\forall u \in Nat,\; \forall v \in Nat,\; \forall e \in Nat,\; \forall m \in Nat,\; ((0 < u) \land ((0 < v) \land ((u < p^{k}) \land ((v < p^{k}) \land ((\operatorname{Coprime}\left(u, p^{k}\right)) \land ((\operatorname{Coprime}\left(v, p^{k}\right)) \land ((u \ne v) \land ((\operatorname{apply}\left(sigma, \operatorname{toInteger}\left(zeta\right)\right) = \operatorname{toInteger}\left(zeta\right)^{u}) \land ((\operatorname{apply}\left(tau, \operatorname{toInteger}\left(zeta\right)\right) = \operatorname{toInteger}\left(zeta\right)^{v}) \land ((0 < m) \land ((\neg p \mid m) \land ((v = u + p^{e} \cdot m) \lor (u = v + p^{e} \cdot m))))))))))))) \Rightarrow ((\forall D \in \operatorname{derivations}\left(sigma, tau\right),\; (\operatorname{outerClass}\left(sigma, tau, D\right) \ne 0) \Leftrightarrow (\neg \operatorname{PrintedIntegralTest}\left(p, e, \operatorname{leftMulMatrix}\left(\operatorname{basis}\left(pb\right), \operatorname{apply}\left(tau, \operatorname{toInteger}\left(zeta\right)\right) - \operatorname{apply}\left(sigma, \operatorname{toInteger}\left(zeta\right)\right)\right), \operatorname{repr}\left(\operatorname{basis}\left(pb\right), \operatorname{apply}\left(\operatorname{val}\left(D\right), \operatorname{toInteger}\left(zeta\right)\right)\right)\right))) \land ((\operatorname{inner}\left(sigma, tau\right) < \operatorname{top}\left(\operatorname{derivations}\left(sigma, tau\right)\right)) \land (\exists D \in \operatorname{derivations}\left(sigma, tau\right),\; \operatorname{outerClass}\left(sigma, tau, D\right) \ne 0)))))))))$$

*Formalization.* `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.claim` (`✓ std3`).

*Citation.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

Every rational prime p is included, with k a natural number unequal to one and p^k at least three. K is an actual rational cyclotomic number field, O its full RingOfIntegers, z the integral primitive root, and pb every integral power basis with generator z and dimension p^(k-1)(p-1). Its basis_eq_pow field fixes the source ordering (1,z,...). Unital maps of this nontrivial ring are nonzero. The unit representatives u and v satisfy 1<=u,v<p^k, coprimality and distinctness, and give the actual root images. The exponent e is nonnegative; m is positive and prime to p. The disjunction includes the positive source factorization in either order. A is always the actual left multiplication matrix of tau(z)-sigma(z), and C is the actual coordinate column of D(z). PrintedIntegralTest is reused without changing its literal p^e denominator or its classical adjugate. The second conjunct asserts that Inn is a proper submodule of the full derivation module, together with its stated nonzero-class interpretation, for every admissible pair, independently of any chosen D.

To compare the two source orders, exchange sigma,u with tau,v. Commutativity and the product law applied to y,x give the same space of derivations. Replacing the integral inner multiplier gamma by -gamma leaves the inner submodule unchanged. The actual matrix becomes -A while C is unchanged. The existing adjugate_smul identity gives Adj(-A)=(-1)^(N-1)Adj(A), so the rational test vector only changes by an integer sign. Integrality, its negation and the strict inclusion are therefore unchanged. This explains the explicit two-order quantifier without imposing the determinant conjecture or excluding a reversed distinct pair.

**Theorem 1.5 (The full printed Conjecture 5.2 is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Praveen Manju and Rajendra Kumar Sharma (2024). *Twisted Derivations in Algebraic Number Fields*. URL: <https://arxiv.org/abs/2412.03507v2>.

*Commentary.*

Reuse the actual fourth cyclotomic field and its full ring of integers from ManjuSharmaConjectureFourFour. Take p=k=2, u=1, v=3, e=m=1, sigma the identity, tau conjugation, and the ordered integral basis (1,z), z^2=-1. The existing pointed Gaussian algebra equivalence defines the genuine integer-linear derivation D(a+bz)=b and proves its twisted law on every pair of algebraic integers.

The existing derivation_not_inner theorem gives non-innerness over the full integer ring, hence the quotient class is nonzero by mk_eq_zero. The existing printed_test uses the actual matrix A=[[0,2],[-2,0]], C=(1,0), Adj(A)=[[0,-2],[2,0]], and (1/2)Adj(A)C=(0,1). Thus the printed test is integral despite the nonzero outer class. The forward direction of the conjectured biconditional says that this same vector is not integral, a contradiction. Primitive-root power injectivity verifies distinctness of the twists from their root images.

This refutes the entire conjunction by falsifying its criterion. It does not refute the universal strict-inclusion assertion separately, nor a criterion with a corrected denominator. In the concrete fourth-root case the exhibited nonzero quotient class supports existence of outer derivations. Conjecture 4.3 is never assumed. The mathematics of the actual cyclotomic counterexample is reused from the existing Conjecture 4.4 result; the conclusion here concerns the distinct full printed Conjecture 5.2.

## References

- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.claim`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.derivations`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.inner`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.outerClass`
- Truth anchor: `D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFiveTwo.result`
- Dependency: [D5/S3/Arith/TwistedDerivations/ManjuSharmaConjectureFourFour](ManjuSharmaConjectureFourFour.md)
