# Greatest cuts and finite descent enumeration

## Abstract

Greatest proper cuts give a literal weighted equivalence and exact finite descent recurrences.

Theorem 2.3 of Fu, Lin and Zeng uses the greatest valid cut of an actual 2413/3142-avoiding permutation. Its right factor is a singleton or has the opposite sign. The finite signed identities below are the actual-permutation form of equations (2.4) and (2.5) in the proof of Corollary 2.4. False denotes direct sum and true denotes skew sum. Avoider(n), Cut, blockSum and des denote the literal objects and ordinary adjacent descents from the fixed-cut construction. Subtype elements are evaluated through their underlying permutations. Every polynomial has natural coefficients. These classical enumeration statements do not resolve the real-rootedness assertion of Conjecture 5.2.

**Definition 1.1 (Proper oriented cuts).**

$$\forall n \in \mathbb{N},\; \forall s \in Bool,\; \forall p \in \operatorname{Perm}\left(n\right),\; \operatorname{HasProperCut}\left(s, p\right) \Leftrightarrow \left(\exists m \in \mathbb{N},\; \left(0 < m \land m < n\right) \land \operatorname{Cut}\left(s, p, m\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.HasProperCut` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

The cut position is strictly between zero and the length. Both factors are nonempty.

**Definition 1.2 (Positive position splits).**

$$\forall n \in \mathbb{N},\; \operatorname{PositiveSplit}\left(n\right) = \{m\in\operatorname{Fin}\left(n\right)\mid 0<m\}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.PositiveSplit` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

A split is a natural position m with 0<m<n. Its right length is n-m. In the formulas a split is identified with its natural value; this identification does not add or duplicate any objects.

**Definition 1.3 (The two proper signed classes).**

$$\forall s \in Bool,\; \forall n \in \mathbb{N},\; \operatorname{SignedAvoider}\left(s, n\right) = \{p\in\operatorname{Avoider}\left(n\right)\mid \operatorname{HasProperCut}\left(s, p\right)\}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.SignedAvoider` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

Membership carries a proof of a proper cut, rather than a chosen cut. Proof fields do not multiply the number of permutations.

**Definition 1.4 (The permitted right factors).**

$$\forall s \in Bool,\; \forall k \in \mathbb{N},\; \operatorname{RightFactor}\left(s, k\right) = \{b\in\operatorname{Avoider}\left(k\right)\mid k = 1 \lor \operatorname{HasProperCut}\left(\operatorname{not}\left(s\right), b\right)\}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.RightFactor` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

The left factor is unrestricted within the actual avoidance class. The right factor is a singleton or is properly decomposable in the opposite orientation. Neither orientation reverses positions or values inside either factor.

**Definition 1.5 (Dependent pairs of actual factors).**

$$\forall s \in Bool,\; \forall n \in \mathbb{N},\; \operatorname{Factors}\left(s, n\right) = \Sigma_{m\in\operatorname{PositiveSplit}\left(n\right)}\operatorname{Avoider}\left(m\right)\times\operatorname{RightFactor}\left(s, n - m\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.Factors` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

An element is a triple (m,a,b), with a of length m and b of length n-m. The dependent index fixes the factor lengths before their values are compared.

**Definition 1.6 (The ordinary descent polynomial).**

$$\forall n \in \mathbb{N},\; \operatorname{S}\left(n\right) = \operatorname{ite}\left(n = 0, 0, \sum_{p\in\operatorname{Avoider}\left(n\right)}X^{\operatorname{des}\left(p\right)}\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.S` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

The unique empty permutation is still an actual avoider. The definition of S assigns length zero the polynomial zero; it does not change that avoidance class.

**Definition 1.7 (Unpadded signed descent polynomials).**

$$\forall s \in Bool,\; \forall n \in \mathbb{N},\; \operatorname{P}\left(s, n\right) = \sum_{p\in\operatorname{SignedAvoider}\left(s, n\right)}X^{\operatorname{des}\left(p\right)}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.P` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

P(false,n) and P(true,n) count the proper direct and skew classes. Both vanish at lengths zero and one. The source pads each signed sequence by one at length one; its padded sequences are delta(n)+P(false,n) and delta(n)+P(true,n), where delta(n)=ite(n=1,1,0). The source's derangement polynomial is a different object.

For x=(m,a,b), write m(x), a(x), b(x) for its three projections. In the next formula cast(n,q) transports a permutation of length m+(n-m) to length n along that natural-number equality alone. Equiv(A,B) is the type of mutually inverse maps between A and B. The notation not(s) is Boolean negation. Each finite sum over PositiveSplit(n) uses k=n-m; antidiagonal(r) consists of ordered pairs (a,b) of natural numbers satisfying a+b=r. All clauses of the following statement hold together.

**Theorem 1.8 (The weighted equivalence and exact recurrences).**

$$\left(\left(\left(\left(\left(\left(\left(\forall s \in Bool,\; \forall n \in \mathbb{N},\; \exists e \in \operatorname{Equiv}\left(\operatorname{Factors}\left(s, n\right), \operatorname{SignedAvoider}\left(s, n\right)\right),\; \forall x \in \operatorname{Factors}\left(s, n\right),\; \left(\left(\operatorname{e}\left(x\right) = \operatorname{cast}\left(n, \operatorname{blockSum}\left(s, \operatorname{a}\left(x\right), \operatorname{b}\left(x\right)\right)\right) \land \operatorname{Cut}\left(s, \operatorname{e}\left(x\right), \operatorname{m}\left(x\right)\right)\right) \land \left(\forall r \in \mathbb{N},\; \left(\left(0 < r \land r < n\right) \land \operatorname{Cut}\left(s, \operatorname{e}\left(x\right), r\right)\right) \Rightarrow r \le \operatorname{m}\left(x\right)\right)\right) \land \operatorname{des}\left(\operatorname{e}\left(x\right)\right) = \operatorname{des}\left(\operatorname{a}\left(x\right)\right) + \operatorname{des}\left(\operatorname{b}\left(x\right)\right) + \operatorname{ite}\left(s, 1, 0\right)\right) \land \left(\left(\operatorname{S}\left(0\right) = 0 \land \operatorname{S}\left(1\right) = 1\right) \land \left(\forall s \in Bool,\; \operatorname{P}\left(s, 0\right) = 0 \land \operatorname{P}\left(s, 1\right) = 0\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{S}\left(n\right) = \operatorname{ite}\left(n = 1, 1, 0\right) + \operatorname{P}\left(false, n\right) + \operatorname{P}\left(true, n\right)\right)\right) \land \left(\forall s \in Bool,\; \forall n \in \mathbb{N},\; \operatorname{P}\left(s, n\right) = X^{\operatorname{ite}\left(s, 1, 0\right)} \cdot \sum_{m\in\operatorname{PositiveSplit}\left(n\right)}\operatorname{S}\left(m\right) \cdot \left(\operatorname{ite}\left(n - m = 1, 1, 0\right) + \operatorname{P}\left(\operatorname{not}\left(s\right), n - m\right)\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{S}\left(n\right), r\right) = \operatorname{ite}\left(n = 1 \land r = 0, 1, 0\right) + \operatorname{coeff}\left(\operatorname{P}\left(false, n\right), r\right) + \operatorname{coeff}\left(\operatorname{P}\left(true, n\right), r\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{P}\left(false, n\right), r\right) = \sum_{m\in\operatorname{PositiveSplit}\left(n\right)}\sum_{ab\in\operatorname{antidiagonal}\left(r\right)}\operatorname{coeff}\left(\operatorname{S}\left(m\right), \operatorname{fst}\left(ab\right)\right) \cdot \left(\operatorname{ite}\left(n - m = 1 \land \operatorname{snd}\left(ab\right) = 0, 1, 0\right) + \operatorname{coeff}\left(\operatorname{P}\left(true, n - m\right), \operatorname{snd}\left(ab\right)\right)\right)\right)\right) \land \left(\forall n \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{P}\left(true, n\right), 0\right) = 0\right)\right) \land \left(\forall n \in \mathbb{N},\; \forall r \in \mathbb{N},\; \operatorname{coeff}\left(\operatorname{P}\left(true, n\right), r + 1\right) = \sum_{m\in\operatorname{PositiveSplit}\left(n\right)}\sum_{ab\in\operatorname{antidiagonal}\left(r\right)}\operatorname{coeff}\left(\operatorname{S}\left(m\right), \operatorname{fst}\left(ab\right)\right) \cdot \left(\operatorname{ite}\left(n - m = 1 \land \operatorname{snd}\left(ab\right) = 0, 1, 0\right) + \operatorname{coeff}\left(\operatorname{P}\left(false, n - m\right), \operatorname{snd}\left(ab\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.result` (`✓ std3`). ∎

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

At the first and last positions, opposite proper cuts would give contradictory strict inequalities. A cut at m+r in blockSum(s,a,b) is exactly a cut at r in b, including r=0. Consequently a greatest proper cut leaves no same-sign proper cut in its right factor. Proper-cut existence then gives precisely the singleton-or-opposite condition. Conversely that condition excludes every larger cut of the assembled permutation. Equality of two assemblies forces equality of their greatest split positions; only after identifying these dependent indices does fixed-cut uniqueness identify the factors. Inside this proof, the ordinary descent sum is normalized by splitting adjacent positions into left interior, boundary, and right interior. The boundary contributes one exactly for skew sum, including when either factor is a singleton. This gives the weight; the literal equivalence reindexes the finite sums. The coefficient identities follow from polynomial multiplication and the shift by X. In particular the skew constant coefficient is zero; its remaining coefficients use r+1, without truncated subtraction.

The finite factor equivalence is not a formal construction of the full di-sk-tree bijection. Generating-function equations, gamma identities, and the analytic real-rootedness argument are separate statements.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.Factors`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.HasProperCut`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.P`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.PositiveSplit`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.RightFactor`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.S`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.SignedAvoider`
- Truth anchor: `D5/S1/Words/Patterns/Separable/GreatestCutEnumeration.result`
- Dependency: [D5/S1/Words/Patterns/Separable/CutFactorization](CutFactorization.md)
