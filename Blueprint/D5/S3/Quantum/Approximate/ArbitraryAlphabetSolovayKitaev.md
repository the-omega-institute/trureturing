# Ordinary-word Solovay–Kitaev approximation

## Abstract

Every finite inverse-closed dense alphabet in SU(2) approximates all targets by ordinary lists with a uniform polylogarithmic length bound.

Mat denotes complex 2 by 2 matrices, with the complex Euclidean L2 operator norm. Words(m) is List(Fin m), including m=0. SU(U) means U is unitary and det(U)=1. Evaluation is ordered: eval(Gamma,[]) is the identity and eval(Gamma,i::w)=Gamma(i)*eval(Gamma,w). Every length below is the actual length of that list.

**Definition 1.1 (Ordered evaluation).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall Gamma \in \operatorname{Fin}\left(m\right) \to \operatorname{Mat}\left(\right),\; \operatorname{evalGamma}\left(Gamma, \operatorname{nil}\left(\right)\right) = 1 \land \left(\forall i \in \operatorname{Fin}\left(m\right),\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \operatorname{evalGamma}\left(Gamma, \operatorname{cons}\left(i, w\right)\right) = Gamma\left(i\right) \cdot \operatorname{evalGamma}\left(Gamma, w\right)\right)$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.evalGamma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The head letter multiplies the evaluation of the tail on the left. Appending lists multiplies their evaluations in the same order.

**Definition 1.2 (A chosen inverse letter).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall sigma \in \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(m\right),\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \operatorname{inverseWord}\left(sigma, w\right) = \operatorname{map}\left(sigma, \operatorname{reverse}\left(w\right)\right)$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.inverseWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inv(sigma,w)=map(sigma,reverse(w)). The inverse selector need only satisfy Gamma(sigma(i))=star(Gamma(i)); it need not be involutive and letters need not be distinct.

**Definition 1.3 (The five-piece successor).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall sigma \in \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(m\right),\; \forall v \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \forall u \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \operatorname{successorWord}\left(sigma, v, w, u\right) = \operatorname{concat}\left(v, w, \operatorname{inverseWord}\left(sigma, v\right), \operatorname{inverseWord}\left(sigma, w\right), u\right)$$

*Formalization.* `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.successorWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The successor is the literal concatenation v ++ w ++ inv(v) ++ inv(w) ++ u. Its length is twice length(v), twice length(w), plus length(u). Its evaluation is the commutator of eval(v),eval(w), followed by eval(u).

**Theorem 1.4 (A finite net made of actual words).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall Gamma \in \operatorname{Fin}\left(m\right) \to \operatorname{Mat}\left(\right),\; \left(\forall A \in \operatorname{Mat}\left(\right),\; \left(A \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(A\right) = 1\right) \Rightarrow \left(\forall eta \in \operatorname{Real}\left(\right),\; 0 < eta \Rightarrow \left(\exists v \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \left\lVert A - \operatorname{evalGamma}\left(Gamma, v\right) \right\rVert < eta\right)\right)\right) \Rightarrow \left(\forall eta \in \operatorname{Real}\left(\right),\; 0 < eta \Rightarrow \left(\exists F \in \operatorname{Finset}\left(\operatorname{List}\left(\operatorname{Fin}\left(m\right)\right)\right),\; \exists L \in \operatorname{Nat}\left(\right),\; \left(\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; w \in F \Rightarrow \operatorname{length}\left(w\right) \le L\right) \land \left(\forall U \in \operatorname{Mat}\left(\right),\; \left(U \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(U\right) = 1\right) \Rightarrow \left(\exists w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; w \in F \land \left\lVert U - \operatorname{evalGamma}\left(Gamma, w\right) \right\rVert < eta\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.exists_finite_word_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compactness of the determinant-one closed subset of the unitary group and density give finitely many actual word values. Choose one list for each net point and take the maximum of their actual lengths. The compact unitary carrier is reused from HaarTwoCopyTwirl.unitaryCompactSpace. No numerical bound on this maximum or effective net construction is required.

**Theorem 1.5 (Stability gains the small factor).**

$$\forall V \in \operatorname{Mat}\left(\right),\; \forall W \in \operatorname{Mat}\left(\right),\; \forall P \in \operatorname{Mat}\left(\right),\; \forall Q \in \operatorname{Mat}\left(\right),\; \forall a \in \operatorname{Real}\left(\right),\; \forall delta \in \operatorname{Real}\left(\right),\; \left(V \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \left(W \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \left(P \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \left(Q \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \left(\left\lVert V - 1 \right\rVert \le a \land \left(\left\lVert W - 1 \right\rVert \le a \land \left(\left\lVert P - 1 \right\rVert \le a \land \left(\left\lVert Q - 1 \right\rVert \le a \land \left(\left\lVert V - P \right\rVert \le delta \land \left\lVert W - Q \right\rVert \le delta\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left\lVert V \cdot W \cdot \operatorname{star}\left(V\right) \cdot \operatorname{star}\left(W\right) - P \cdot Q \cdot \operatorname{star}\left(P\right) \cdot \operatorname{star}\left(Q\right) \right\rVert \le 4 \cdot a \cdot delta \cdot \left(1 + a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_groupCommutator_sub_le` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

For four unitary factors within a of identity and factor errors at most delta, the commutator error is at most 4*a*delta*(1+a). This is the Apache-2.0 CSD estimate of Zayn Blore, specialized to the matrix carrier. Its factorization pairs a factor difference with a small near-identity factor.

**Theorem 1.6 (One list carries error and length together).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall Gamma \in \operatorname{Fin}\left(m\right) \to \operatorname{Mat}\left(\right),\; \forall sigma \in \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(m\right),\; \forall e \in \operatorname{Real}\left(\right),\; \forall L \in \operatorname{Nat}\left(\right),\; \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; Gamma\left(i\right) \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(Gamma\left(i\right)\right) = 1\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; Gamma\left(sigma\left(i\right)\right) = \operatorname{star}\left(Gamma\left(i\right)\right)\right) \land \left(0 \le e \land \left(\operatorname{sqrt}\left(e\right) \le \frac{1}{33} \land \left(\forall U \in \operatorname{Mat}\left(\right),\; \left(U \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(U\right) = 1\right) \Rightarrow \left(\exists w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \left\lVert U - \operatorname{evalGamma}\left(Gamma, w\right) \right\rVert \le e \land \operatorname{length}\left(w\right) \le L\right)\right)\right)\right)\right)\right) \Rightarrow \left(\forall n \in \operatorname{Nat}\left(\right),\; \forall U \in \operatorname{Mat}\left(\right),\; \left(U \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(U\right) = 1\right) \Rightarrow \left(\exists w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \left\lVert U - \operatorname{evalGamma}\left(Gamma, w\right) \right\rVert \le \operatorname{skErr}\left(e, n\right) \land \operatorname{length}\left(w\right) \le 5^{n} \cdot L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.exists_word_at_level` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with a word u from the preceding level approximating the current U. The residual is U*star(eval(Gamma,u)), whose distance from identity equals the preceding error and whose determinant remains one. BalancedSU2Commutator supplies exact factors V,W at square-root distance. Approximate both at the same preceding level and concatenate their words with inverse words and u. Stability bounds this same list's error by e(n+1)=33*e(n)^(3/2), while its actual length is bounded by 5^(n+1)*L. This alphabet-parametric construction follows the licensed CSD ordinary-word induction; the residual always uses the preceding approximation to this target.

**Theorem 1.7 (The uniform polylogarithmic ordinary-word theorem).**

$$\forall m \in \operatorname{Nat}\left(\right),\; \forall Gamma \in \operatorname{Fin}\left(m\right) \to \operatorname{Mat}\left(\right),\; \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; Gamma\left(i\right) \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(Gamma\left(i\right)\right) = 1\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(m\right),\; \exists j \in \operatorname{Fin}\left(m\right),\; Gamma\left(j\right) = \operatorname{star}\left(Gamma\left(i\right)\right)\right) \land \left(\forall A \in \operatorname{Mat}\left(\right),\; \left(A \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(A\right) = 1\right) \Rightarrow \left(\forall eta \in \operatorname{Real}\left(\right),\; 0 < eta \Rightarrow \left(\exists v \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \left\lVert A - \operatorname{evalGamma}\left(Gamma, v\right) \right\rVert < eta\right)\right)\right)\right)\right) \Rightarrow \left(\exists K \in \operatorname{Real}\left(\right),\; \exists b \in \operatorname{Real}\left(\right),\; 0 < K \land \left(0 < b \land \left(b < 1 \land \left(\forall epsilon \in \operatorname{Real}\left(\right),\; \left(0 < epsilon \land epsilon \le b\right) \Rightarrow \left(\forall U \in \operatorname{Mat}\left(\right),\; \left(U \in \operatorname{unitary}\left(\operatorname{Mat}\left(\right)\right) \land \operatorname{det}\left(U\right) = 1\right) \Rightarrow \left(\exists w \in \operatorname{List}\left(\operatorname{Fin}\left(m\right)\right),\; \left\lVert U - \operatorname{evalGamma}\left(Gamma, w\right) \right\rVert \le epsilon \land \operatorname{real}\left(\operatorname{length}\left(w\right)\right) \le K \cdot \operatorname{log}\left(\frac{1}{epsilon}\right)^{\frac{\operatorname{log}\left(5\right)}{\operatorname{log}\left(\frac{3}{2}\right)}}\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.ordinary_word_solovay_kitaev` (`✓ std3`). ∎

*Citation.* Christopher M. Dawson; Michael A. Nielsen (2006). *The Solovay-Kitaev algorithm*. URL: <https://arxiv.org/abs/quant-ph/0505030>.

*Commentary.*

For every finite alphabet Gamma of determinant-one unitary matrices, assume inverse closure and density of its ordinary finite words in SU(2). Then K>0 and 0<epsilon0<1 can be chosen uniformly for every target U and every 0<epsilon<=epsilon0. One ordinary list w satisfies both the error and real-valued length inequalities. The exponent is exactly log(5)/log(3/2).

A compactness net supplies the alphabet-dependent initial length. The paired word invariant gives the same list at every level; the licensed scalar and logarithmic estimates in SolovayKitaevRate eliminate the level. Zayn Blore's Apache-2.0 CSD proof is the source of the balanced decomposition, stability and rate estimates and of the fixed-alphabet word induction. The full license is docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. This theorem concerns existence and ordinary list length. It asserts no effectiveness, runtime, optimality, numerical constants, physical realization, compressed length or bound uniform in growing dimension.

## References

- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.evalGamma`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.exists_finite_word_net`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.exists_word_at_level`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.inverseWord`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.norm_groupCommutator_sub_le`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.ordinary_word_solovay_kitaev`
- Truth anchor: `D5/S3/Quantum/Approximate/ArbitraryAlphabetSolovayKitaev.successorWord`
- Dependency: [D5/S3/Quantum/Approximate/BalancedSU2Commutator](BalancedSU2Commutator.md)
- Dependency: [D5/S3/Quantum/Approximate/SolovayKitaevRate](SolovayKitaevRate.md)
- Dependency: [D5/S3/Quantum/RandomCircuits/HaarTwoCopyTwirl](../RandomCircuits/HaarTwoCopyTwirl.md)
