# Sharp plastic-power sumsets from lossless finite memory

## Abstract

The sharp minimum of a sumset inside the integer powers of a plastic root, with the least uniform size threshold ten.

Fix r > 1 with r³ = r + 1. For a finite integer set E, write A(r,E) = {rᵉ : e ∈ E}. C(E) counts all translates contained in E of T₄={0,2,3,4}, T₆={0,3,5,6}, T₇={0,5,7}, and T₉={0,5,8,9}. N_d(E) is the number of integer starting points t with t+T_d contained in E. M(n) = n(n+1)/2, L(n) = M(n)−4n+26, and I(a,n) = [a,a+n−1] over the integers. The Lean count is proved equal to the four literal filters in the frozen collision theorem, via the bijection from each starting exponent to its unique right endpoint. Natural n ≥ 10 covers exactly the original integer size range. Exponents and the translation a may be negative; no bound on the diameter, gap lengths or product set is imposed. MinimumSumsetInPowerGroup(r,n) means the least element of the set of |A+A| for finite real A with A contained in {rᶻ : z an integer} and |A|=n. LeastUniformCopyCountThreshold means the least integer N such that for every finite integer E, N ≤ |E| implies C(E) ≤ 4|E|−26, with the latter inequality interpreted in the integers.

**Definition 1.1 (Four literal translated templates).**

$$\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), \operatorname{C}\left(E\right) = \operatorname{N}\left(4, E\right) + \operatorname{N}\left(6, E\right) + \operatorname{N}\left(7, E\right) + \operatorname{N}\left(9, E\right)$$

*Formalization.* `D5/S3/Arith/Additive/PlasticExtremal.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Lean counts the unique right endpoints of these copies. The source-count bridge translates each starting point by its template span, proving equality with the four original filters before using the frozen sumset identity.

**Theorem 1.2 (Theorem 3.1: sharp extremum and smallest uniform threshold).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (n : \mathbb{N}), (10 \le n) \Rightarrow ((\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), (\lvert E\rvert  = n) \Rightarrow ((\operatorname{C}\left(E\right) \le 4 \cdot n - 26) \land (\operatorname{L}\left(n\right) \le \lvert \operatorname{A}\left(r, E\right) + \operatorname{A}\left(r, E\right)\rvert ))) \land ((\forall (a : \mathbb{Z}), (\lvert \operatorname{I}\left(a, n\right)\rvert  = n) \land ((\operatorname{C}\left(\operatorname{I}\left(a, n\right)\right) = 4 \cdot n - 26) \land (\lvert \operatorname{A}\left(r, \operatorname{I}\left(a, n\right)\right) + \operatorname{A}\left(r, \operatorname{I}\left(a, n\right)\right)\rvert  = \operatorname{L}\left(n\right)))) \land ((\operatorname{MinimumSumsetInPowerGroup}\left(r, n\right) = \operatorname{L}\left(n\right)) \land (\operatorname{LeastUniformCopyCountThreshold}\left(\right) = 10))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticExtremal.whole_theorem_three_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Insert the exponent points in increasing order. The current state records exactly those distances 0 through 8 occupied behind the current maximum. The four rewards are evaluated in the full shifted state before truncation, so a required distance of 9 is counted correctly. A gap at least 9 resets the state and has reward zero. Actual prefix induction carries both the table bound and the fact that its potential entry is non-sentinel (less than 15): the sentinel 15 never serves as a legitimate bound. Every allowed transition of the source's ten-layer table is checked by Lean's kernel. This is an upper-bound certificate, not a claim that the table computes exact optima. It gives at most 14 copies on ten points; each later actual maximum creates at most four copies. Every translated interval has counts n−4, n−6, n−7 and n−9, attaining the bound. The frozen plastic collision identity transfers the result to actual real sumsets. The Bérczes reference attests the collision classification, not the finite-memory extremal theorem proved here. For any finite A inside the full group r^ℤ, the injective power map supplies an equal-cardinality finite exponent preimage. Thus the minimum is taken over all such A, not just consecutive powers. The actual nine-point set {0} ∪ [2,9] has eleven copies, excluding every integer threshold below ten. This does not classify all equality cases or prove the later stability and deletion theorems.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticExtremal.count`
- Truth anchor: `D5/S3/Arith/Additive/PlasticExtremal.whole_theorem_three_one`
- Dependency: [D5/S3/Arith/Additive/PlasticPowerCollisions](PlasticPowerCollisions.md)
