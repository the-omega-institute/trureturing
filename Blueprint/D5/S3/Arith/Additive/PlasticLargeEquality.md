# Equality patterns from eleven points onward

## Abstract

For every size at least eleven, exactly two translated integer patterns maximize the plastic-template count and minimize the corresponding real-power sumset.

Let E be any finite subset of the integers, and put n=|E|. Write C(E) for the total number of translates contained in E of {0,2,3,4}, {0,3,5,6}, {0,5,7}, and {0,5,8,9}. All intervals below contain integers. For a natural number n, define S₀(n)=[0,n−1] and S₁(n)={0}∪[2,n], with integer endpoints. Write translate(a,S)={a+z : z ∈ S} and A(r,E)={rᶻ : z ∈ E}. The sum A(r,E)+A(r,E) is the actual finite real sumset. Negative exponents, negative translations, and unbounded gaps are allowed. The statement below assumes n≥11; the ten-point case has two additional patterns.

**Theorem 1.1 (The two equality shapes).**

$$\forall (E : \operatorname{Finset}\left(\mathbb{Z}\right)), (11 \le \lvert E\rvert ) \Rightarrow (((\operatorname{C}\left(E\right) = 4 \cdot \lvert E\rvert  - 26) \Leftrightarrow (\exists (a : \mathbb{Z}), (E = \operatorname{translate}\left(a, \left(S_{0}\right)\left(\lvert E\rvert \right)\right)) \lor (E = \operatorname{translate}\left(a, \left(S_{1}\right)\left(\lvert E\rvert \right)\right)))) \land (\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow ((\lvert \operatorname{A}\left(r, E\right) + \operatorname{A}\left(r, E\right)\rvert  = \frac{\lvert E\rvert  \cdot (\lvert E\rvert  + 1)}{2} - 4 \cdot \lvert E\rvert  + 26) \Leftrightarrow (\exists (a : \mathbb{Z}), (E = \operatorname{translate}\left(a, \left(S_{0}\right)\left(\lvert E\rvert \right)\right)) \lor (E = \operatorname{translate}\left(a, \left(S_{1}\right)\left(\lvert E\rvert \right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticLargeEquality.whole_large_equality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

Remove the largest element y from an actual exponent set, and let x be the largest remaining element. The exact insertion identity expresses the change in C as the number of templates completed at y, which is at most four. Together with the preceding prefix bound, equality forces both equality for that prefix and an increment of four. All four templates are completed precisely when y−1, y−2, y−3, y−4, y−6, y−7, and y−9 belong to the prefix. In particular, y−1 belongs to it, so maximality gives y=x+1. At ten points the four possible translated patterns are already known. The pattern {0,1}∪[3,10] cannot extend with increment four: its next point would be 11, but the required point 2 is absent. Similarly, {0,3}∪[5,12] would have to extend by 13 while the required point 4 is absent. The interval and single-gap patterns do extend: adding their maximum plus one supplies all seven required points and preserves the same form. Induction on the actual finite set therefore proves both directions of the classification for every larger size. For r>1 satisfying r³=r+1, the collision identity gives |A(r,E)+A(r,E)|+C(E)=n(n+1)/2. Since n≥11 implies n(n+1)/2≥4n, the natural-number subtraction in the displayed sumset value agrees with ordinary integer subtraction. Thus the same two shapes are exactly the sets attaining n(n+1)/2−4n+26.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticLargeEquality.whole_large_equality`
- Dependency: [D5/S3/Arith/Additive/PlasticTenPointEquality](PlasticTenPointEquality.md)
