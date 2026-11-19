# Arbitrary deletions from a plastic-power interval

## Abstract

After any h deletions leaving n consecutive-interval plastic powers with n at least eight and 11h + 24 at most 3n, their sumset is smaller than the golden-power sumset.

Fix r > 1 with r³ = r + 1. For natural numbers n,h and an integer a, let I(a,n,h) = [a,a+n+h−1] be an integer interval. For any H contained in I(a,n,h) with |H| = h, put E = I(a,n,h) ∖ H and A(r,a,n,h,H) = {rᵉ : e ∈ E}. Let φ = (1+√5)/2, G(n) = {φᵉ : e an integer, 0 ≤ e ≤ n−1}, and M(n) = n(n+1)/2. All sums and products below are those of actual finite sets of real numbers. The conditions n ≥ 8 and 11h+24 ≤ 3n express exactly the integer range 0 ≤ h ≤ floor((3n−24)/11). Natural-number subtraction in the conclusion agrees with integer subtraction throughout this range.

**Theorem 1.1 (No restriction on the deleted positions).**

$$\forall (r : \mathbb{R}), (1 < r) \Rightarrow ((r^{3} = r + 1) \Rightarrow (\forall (n : \mathbb{N}), \forall (h : \mathbb{N}), (8 \le n) \Rightarrow ((11 \cdot h + 24 \le 3 \cdot n) \Rightarrow (\forall (a : \mathbb{Z}), \forall (H : \operatorname{Finset}\left(\mathbb{Z}\right)), (H \subseteq \operatorname{I}\left(a, n, h\right)) \Rightarrow ((\lvert H\rvert  = h) \Rightarrow (((((\lvert \operatorname{A}\left(r, a, n, h, H\right)\rvert  = n) \land (\lvert \operatorname{A}\left(r, a, n, h, H\right) \cdot \operatorname{A}\left(r, a, n, h, H\right)\rvert  \le 2 \cdot (n + h) - 1)) \land (2 \cdot (n + h) - 1 \le 3 \cdot n - 4)) \land (\lvert \operatorname{A}\left(r, a, n, h, H\right) + \operatorname{A}\left(r, a, n, h, H\right)\rvert  \le \operatorname{M}\left(n\right) - 4 \cdot n + 26 + 11 \cdot h)) \land (\operatorname{M}\left(n\right) - 4 \cdot n + 26 + 11 \cdot h \le \lvert \operatorname{G}\left(n\right) + \operatorname{G}\left(n\right)\rvert  - 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/PlasticDeletionBound.whole_theorem_four_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Attila Bérczes (2010). *On the sumset of geometric progressions*. DOI: [10.5486/PMD.2010.4683](https://doi.org/10.5486/PMD.2010.4683). URL: <https://doi.org/10.5486/PMD.2010.4683>.

*Commentary.*

For a finite offset template T containing zero, each missing point destroys at most |T| translated copies. Indeed every destroyed start has the form x−u for a deleted point x and an offset u in T. The four plastic collision templates have spans 4,6,7,9 and cardinalities 4,4,3,4. In an interval of length m their surviving counts are at least (m−4)₊−4h, (m−6)₊−4h, (m−7)₊−3h, and (m−9)₊−4h, respectively. Summing yields C(E)+26+15h ≥ 4m, also at m=8 where the last template has no copies. With m=n+h, the collision identity |A+A|+C(E)=M(n) gives the stated numerical sumset bound. The golden-power lower bound |G(n)+G(n)| ≥ M(n)−(n−3), together with 11h+24 ≤ 3n, gives the final separation by one. Strict monotonicity of integer powers gives |A|=n. Every product exponent lies in [2a,2a+2(n+h)−2], which gives the product bound, and the same hypothesis implies 2(n+h)−1 ≤ 3n−4.

## References

- Truth anchor: `D5/S3/Arith/Additive/PlasticDeletionBound.whole_theorem_four_one`
- Dependency: [D5/S3/Arith/Additive/PlasticNestedFamily](PlasticNestedFamily.md)
