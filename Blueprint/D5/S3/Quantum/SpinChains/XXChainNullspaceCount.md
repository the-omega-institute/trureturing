# The nullspace of the periodic XX chain on 2p sites has dimension 2(6^((p-1)/2) + 1)

## Abstract

For every odd prime p, the number of subsets K of {1, ..., 2p} whose cosines at the angles (2j + (1 + (-1)^|K|)/2) pi/(2p), j in K, sum to zero is 2 (6^((p-1)/2) + 1). By the Jordan-Wigner transformation this count is the dimension of the zero-energy subspace of the periodic spin-1/2 XX Heisenberg chain on 2p sites (OEIS A392387).

**Definition 1.1 (The zero cosine-sum subsets).**

$$\forall n \in \mathbb{N},\; \operatorname{nullspaceCount}\left(n\right) = \operatorname{card}\left(\{K \in \operatorname{powerset}\left(\operatorname{Icc}\left(1, n\right)\right) \mid \sum_{j \in K} \operatorname{cos}\left(\frac{(2 \cdot j + \frac{1 + (-1)^{\operatorname{card}\left(K\right)}}{2}) \cdot \pi}{n}\right) = 0\}\right)$$

*Formalization.* `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.nullspaceCount` (`✓ std3`).

*Citation.* Thore Posske (2026). *OEIS A392387, Nullspace dimension of the periodic XX Heisenberg chain with n > 1 sites*. URL: <https://oeis.org/A392387>.

*Commentary.*

OEIS A392387, COMMENTS: "Also, the number of subsets K of {1,...,n} such that the sum of cosines of the angles in {(2j + (1 + (-1)^|K|)/2 )*Pi/n | j in K} is zero." The entry identifies this number with the dimension of the zero-energy subspace of the periodic spin-1/2 XX Heisenberg chain on n > 1 sites: after the Jordan-Wigner transformation the chain is a system of free fermions whose momenta are 2 j Pi/n for an odd number |K| of fermions and (2 j + 1) Pi/n for an even number, with energy the sum of the cosines. The definition is the subset count; the empty set, whose cosine sum is zero, is counted.

**Definition 1.2 (The conjecture of OEIS A392387).**

$$claim \Leftrightarrow (\forall p \in \mathbb{N},\; (\operatorname{Prime}\left(p\right)) \Rightarrow ((\operatorname{Odd}\left(p\right)) \Rightarrow (\operatorname{nullspaceCount}\left(2 \cdot p\right) = 2 \cdot (6^{\operatorname{NatDiv}\left(p - 1, 2\right)} + 1))))$$

*Formalization.* `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.claim` (`✓ std3`).

*Citation.* Thore Posske (2026). *OEIS A392387, Nullspace dimension of the periodic XX Heisenberg chain with n > 1 sites*. URL: <https://oeis.org/A392387>.

*Commentary.*

OEIS A392387, FORMULA: "Conjecture: a(2*p) = 2*(6^((p-1)/2)+1) for odd prime p." The statement quantifies over every prime p that is odd.

**Theorem 1.3 (The count at twice an odd prime).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.result` (`✓ std3`). ∎

*Resolves.* `Problems/posske-2026-a392387-xx-chain-nullspace-2p` (proved) by `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"posske-2026-a392387-xx-chain-nullspace-2p","declaration_gid":"D5/S3/Quantum/SpinChains/XXChainNullspaceCount.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Thore Posske (2026). *OEIS A392387, Nullspace dimension of the periodic XX Heisenberg chain with n > 1 sites*. URL: <https://oeis.org/A392387>.

*Commentary.*

Write p = 2m + 1, let eta be a primitive p-th root of unity with -eta = exp(i pi/p), and omega = exp(i pi/(2p)), so omega^2 = -eta. A subset K of {1, ..., 2p} is determined by its class-state function w on the residues r modulo p: for each r, which of the two elements of {1, ..., 2p} congruent to r modulo p, one even and one odd, lie in K. With z(r) the number of taken even elements minus the number of taken odd elements of the class r, the cosine sum at the odd-parity angles is the real part of Z = sum_r z(r) eta^r and at the even-parity angles the real part of omega Z. Since the only rational linear relation among 1, eta, ..., eta^(p-1) is that their sum vanishes (the cyclotomic polynomial is the minimal polynomial of eta), the real part of Z vanishes exactly when z(r) + z(-r) = 2 z(0) for all r, and that of omega Z exactly when z(-r) - z(r - 1) = z(0) - z(-1) for all r, which, since r -> -1 - r fixes m, is the symmetry z(r) = z(-1 - r). For odd |K| the first relation forces z to be constantly 1 or constantly -1, the even and the odd elements of {1, ..., 2p}: two subsets. For even |K| the symmetric class-state functions are counted over the fundamental domain 0, ..., m - 1 of r -> -1 - r: each pair of classes has 6 states with equal z, and the parity condition forces the fixed class m to be empty or full, 2 states. The total is 2 + 2 6^m.

## References

- Truth anchor: `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.claim`
- Truth anchor: `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.nullspaceCount`
- Truth anchor: `D5/S3/Quantum/SpinChains/XXChainNullspaceCount.result`
