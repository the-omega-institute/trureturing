# A thirty-point lower bound for unit positive-three eigenvectors

## Abstract

Nonzero unit-valued positive-three Huang eigenvectors have support at least thirty.

Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether f₂(Q₉)=3 or 4. The original 258-vertex question and literature novelty remain unresolved. Throughout, intA and intCoeff are the original signed FALSE-prefix Huang integer operator and coefficients from HuangIntegralNormGap, with L = 3I − A.

**Theorem 1.1 (Every nonzero unit positive-three eigenvector has at least thirty support points).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty.thirty_le_support_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty.thirty_le_support_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For h : Q9 → ℤ, assume intA h = (fun x => 3 * h x), every h x is 0, 1, or −1, and h ≠ 0. Then 30 ≤ (Finset.univ.filter (fun x => h x ≠ 0)).card. There are no induced-degree or IsBalanced assumptions on this support. The claim concerns the +3 eigenspace only, asserts no sharpness, and does not improve the existing 48-vertex balanced-component bound.

The two parity halves have equal squared norms and hence equal support sizes. If total support were at most 24, each half would have at most twelve points. The parity stopping-set theorem CubeTwelveSupport identifies a nonempty half as a nine-point star. Every off-center row meets that star in at most two points, so its unit signed sum, divisible by three, must vanish. The other half would have support at most one, contradicting its equal support size nine. Integer +3 eigennorms are divisible by six, rounding support greater than 24 up to at least thirty.

This general support bound is used by the actual five-cut proof to exclude the P3 residual branch in components with fewer than fifty-four vertices.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty.thirty_le_support_card`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFourCut](BalancedCubeFourCut.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap](HuangUnitSupportGap.md)
