# Actual fixed-cut factorization

## Abstract

Actual direct and skew fixed-cut factors preserve classical avoidance and ordinary descents.

These are source-attested supporting contracts for the classical separable permutation decomposition in Proposition 2.1 and the descent correspondence in Theorem 2.3 of the cited source. They do not resolve Conjecture 5.2. All permutations are bijections of Fin(n); Contains uses increasing position embeddings and exact relative value comparisons. In the formulas, Perm(n) means Equiv.Perm(Fin(n)); Bool has the values false and true; ite(e,x,y) selects x when e is true and y otherwise. Permutations are evaluated at zero-based positions, and subtype factors are evaluated through their underlying permutations.

**Definition 1.1 (The literal avoidance class).**

$$\forall n\in\mathbb{N},\forall p\in\operatorname{Perm}\left(n\right),\operatorname{Avoids}\left(p\right)\iff\neg \operatorname{Contains}\left(pattern2413, p\right)\land\neg \operatorname{Contains}\left(pattern3142, p\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/CutFactorization.Avoids` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

Avoids(p) is the conjunction of the two original negated containment predicates. Avoider(n) is the subtype of actual permutations satisfying it.

**Definition 1.2 (Actual avoiding permutations).**

$$\forall n\in\mathbb{N},\operatorname{Avoider}\left(n\right)=\{p\in\operatorname{Perm}\left(n\right)\mid\operatorname{Avoids}\left(p\right)\}$$

*Formalization.* `D5/S1/Words/Patterns/Separable/CutFactorization.Avoider` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

This subtype retains each actual permutation and a proof that it avoids the two literal patterns. It does not replace the class by a recurrence.

**Definition 1.3 (Two actual block sums).**

$$\forall m,k\in\mathbb{N},\forall e\in Bool,\forall a\in\operatorname{Perm}\left(m\right),\forall b\in\operatorname{Perm}\left(k\right),\operatorname{blockSum}\left(e, a, b\right)\in\operatorname{Perm}\left(m+k\right)\land(\forall i\in\operatorname{Fin}\left(m\right),\operatorname{blockSum}\left(e, a, b\right)(i)=\operatorname{ite}\left(e, k, 0\right)+\operatorname{a}\left(i\right))\land(\forall j\in\operatorname{Fin}\left(k\right),\operatorname{blockSum}\left(e, a, b\right)(m+j)=\operatorname{ite}\left(e, 0, m\right)+\operatorname{b}\left(j\right))$$

*Formalization.* `D5/S1/Words/Patterns/Separable/CutFactorization.blockSum` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

For a in Perm(m) and b in Perm(k), false selects direct sum and true selects skew sum. At a left position i<m, the values are a(i) and k+a(i), respectively. At position m+j, they are m+b(j) and b(j). Neither orientation reverses either factor. The constructor uses finSumFinEquiv and Equiv.sumCongr, with a swap of value blocks for skew sum.

**Definition 1.4 (An oriented fixed cut).**

$$\forall n,m\in\mathbb{N},\forall e\in Bool,\forall p\in\operatorname{Perm}\left(n\right),\operatorname{Cut}\left(e, p, m\right)\iff\forall i,j\in\operatorname{Fin}\left(n\right),(i<m\land m\le j)\Rightarrow\operatorname{ite}\left(e, \operatorname{p}\left(j\right)<\operatorname{p}\left(i\right), \operatorname{p}\left(i\right)<\operatorname{p}\left(j\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/CutFactorization.Cut` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

The cut compares every prefix value with every suffix value. The factorization theorem requires m,k>0.

**Theorem 1.5 (Exact avoidance in both directions).**

$$\forall m,k\in\mathbb{N},\forall e\in Bool,\forall a\in\operatorname{Perm}\left(m\right),\forall b\in\operatorname{Perm}\left(k\right),\operatorname{Avoids}\left(\operatorname{blockSum}\left(e, a, b\right)\right)\iff\operatorname{Avoids}\left(a\right)\land\operatorname{Avoids}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/CutFactorization.avoids_block_sum_iff` (`✓ std3`). ∎

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

For all natural m,k, both orientations, and arbitrary factors a,b, the block sum avoids both literal patterns exactly when both factors do. An occurrence crossing the boundary would force a forbidden comparison at one of the three proper splits of 2413 or 3142. Whole-factor occurrences transfer through increasing position embeddings.

**Theorem 1.6 (Unique actual inverse factors).**

$$\forall m,k\in\mathbb{N},(0<m\land0<k)\Rightarrow\forall e\in Bool,\forall p\in\operatorname{Avoider}\left(m+k\right),\operatorname{Cut}\left(e, p, m\right)\iff\exists! q\in\operatorname{Avoider}\left(m\right)\times\operatorname{Avoider}\left(k\right),\operatorname{blockSum}\left(e, \operatorname{fst}\left(q\right), \operatorname{snd}\left(q\right)\right)=p$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/CutFactorization.fixed_cut_factorization` (`✓ std3`). ∎

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

For every positive m,k, each orientation e, and p in Avoider(m+k), Cut(e,p,m) holds exactly when there is a unique pair q in Avoider(m) times Avoider(k) whose literal block sum is p. Tuple.sort constructs the factor ranks. Internal comparisons together with the actual crossing inequalities make the reconstructed permutation have the same full value order as p. A monotone permutation is the identity, proving equality of actual values, not just their ranks. The two block evaluation formulas give uniqueness.

**Definition 1.7 (An adjacent-descent indicator).**

$$\forall n\in\mathbb{N},\forall p\in\operatorname{Perm}\left(n\right),\forall i\in\operatorname{Fin}\left(n\right),\operatorname{descentAt}\left(p, i\right)=\operatorname{ite}\left(i+1<n, \operatorname{ite}\left(\operatorname{p}\left(i+1\right)<\operatorname{p}\left(i\right), 1, 0\right), 0\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/CutFactorization.descentAt` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

At position i this is one exactly when i+1<n and p(i+1)<p(i). The inner comparison is evaluated only when i+1<n, so its successor index belongs to Fin(n). It is zero otherwise, including at the final position.

**Definition 1.8 (Ordinary adjacent descents).**

$$\forall n\in\mathbb{N},\forall p\in\operatorname{Perm}\left(n\right),\operatorname{descents}\left(p\right)=\sum_{i\in\operatorname{Fin}\left(n\right)}\operatorname{descentAt}\left(p, i\right)$$

*Formalization.* `D5/S1/Words/Patterns/Separable/CutFactorization.descents` (`✓ std3`).

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

The sum runs over every position in Fin(n). Thus descents counts ordinary adjacent descents; in particular a singleton has zero descents.

**Theorem 1.9 (The exact boundary weight).**

$$\forall m,k\in\mathbb{N},(0<m\land0<k)\Rightarrow\forall e\in Bool,\forall a\in\operatorname{Perm}\left(m\right),\forall b\in\operatorname{Perm}\left(k\right),\operatorname{descents}\left(\operatorname{blockSum}\left(e, a, b\right)\right)=\operatorname{descents}\left(a\right)+\operatorname{descents}\left(b\right)+\operatorname{ite}\left(e, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/CutFactorization.descents_block_sum` (`✓ std3`). ∎

*Citation.* Shishuo Fu, Zhicong Lin, and Jiang Zeng (2019). *On two unimodal descent polynomials*. DOI: [10.48550/arXiv.1507.05184](https://doi.org/10.48550/arXiv.1507.05184). URL: <https://arxiv.org/abs/1507.05184v2>.

*Commentary.*

For arbitrary positive m,k and factors a,b, the number of descents is des(a)+des(b)+boundary(e), where boundary(false)=0 and boundary(true)=1. The proof partitions adjacent positions into left interior, boundary, and right interior. It applies when either factor is a singleton and when the factor lengths differ.

The greatest-cut choice, its right-factor sign condition, weighted enumeration, generating-function equations, and real-rootedness remain separate obligations. No FirstFreeze or open-problem resolution claim is made by this support unit.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.Avoider`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.Avoids`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.Cut`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.avoids_block_sum_iff`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.blockSum`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.descentAt`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.descents`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.descents_block_sum`
- Truth anchor: `D5/S1/Words/Patterns/Separable/CutFactorization.fixed_cut_factorization`
- Dependency: [D5/S1/Words/Patterns/Separable/ProperCut](ProperCut.md)
