# Shell compression and the oriented triangle

## Abstract

Two on-shell identities for integer quaternion shell maps: two-point compression and the oriented triangle.

For an integer s and quaternions p, a the shell map is P(s, p, a, v) = s v + p v a. Purity of p, q, r and a means that the real coordinate vanishes, and N(x) = x·x is the squared norm. Both identities below assume the shell condition s² = N(p)N(a). The general forms without that condition, each with an explicit defect term proportional to s² − N(p)N(a), are Omega.Quaternion.shell_compress and Omega.Quaternion.shell_triangle in OmegaMath.Algebra.Quaternion.Shell; their proofs rewrite every shell map as a pair action v ↦ c v + (d v) a, compose pair actions using a a = −N(a), and certify the resulting integer polynomial identity in s, N(a) and the coordinates of p, q, r.

Over the real numbers, when s ≠ 0 and s² = N(p)N(a), the map P/(2s) on the quaternions viewed as ℂ² is the rank-one qubit projection (1 + p̂·σ)/2, where p̂ is the unit vector of p. In that reading the compression identity is the integer rescaling of P_a P_b P_a = Tr(P_a P_b) P_a for rank-one projections, and the triangle identity is the integer rescaling of the three-state Bargmann invariant ⟨a|b⟩⟨b|c⟩⟨c|a⟩ = (1 + a·b + b·c + c·a + i det(a, b, c))/4 that defines the Pancharatnam phase. Neither the identification with projections nor these real or complex formulas is formalized in this module. The real and complex Bloch-vector form of the three-state invariant is the separate theorem D5/S3/Quantum/Information/GroupInvariantPsi/C129QubitBargmann.triple_bargmann_bloch; this module states the integer quaternion identity and does not depend on it.

**Theorem 1.1 (Compression on the shell).**

$$\left(\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \land s \cdot s = \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right)\right) \Rightarrow \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, p, a, v\right)\right)\right) = 2 \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, q\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_compress_of_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the shell, P(s, p, a, ·) squares to 2s times itself and the composition through q returns a multiple of the same map; no condition on N(q) is used. The shell condition cannot be dropped: for s = 0, p = i, q = j, a = i and v = 1 the left side is k and the right side is 0. It is also not necessary: the library theorem Omega.Quaternion.shell_compress_iff states that, for pure p, q, a, the identity holds for every v exactly when s² = N(p)N(a), or s = 0 and q = 0. Each purity hypothesis is needed. With s = 1 and the other inputs equal to i, replacing q by 1 gives the difference (0, 0, 0, −4) at v = j, replacing a by 1 gives (−6, −2, 0, 0) at v = 1, and replacing p by 1 gives (−2, −2, 0, 0) at v = 1; coordinates are listed as (w, x, y, z), and each choice satisfies the shell condition. These counterexamples were computed independently and are not checked by compiled Lean.

**Theorem 1.2 (Triangle identity on the shell).**

$$\left(\left(\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \land \operatorname{pure}\left(r\right)\right) \land s \cdot s = \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right)\right) \Rightarrow \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, r, a, \operatorname{P}\left(s, p, a, v\right)\right)\right)\right) = 2 \cdot s \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \left(\operatorname{dot}\left(p, q\right) + \operatorname{dot}\left(q, r\right) + \operatorname{dot}\left(r, p\right)\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right) + 2 \cdot \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, \operatorname{mul}\left(q, r\right)\right) \cdot \operatorname{mul}\left(\operatorname{P}\left(s, p, a, v\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_triangle_of_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Michał Oszmaniec, Daniel J. Brod, Ernesto F. Galvão (2021). *Measuring relational information between quantum states, and applications*. DOI: [10.1088/1367-2630/ad1a27](https://doi.org/10.1088/1367-2630/ad1a27). URL: <https://arxiv.org/abs/2109.10006v1>.

*Acknowledgement.* S. Pancharatnam (1956). *Generalized theory of interference, and its applications*. DOI: [10.1007/BF03046050](https://doi.org/10.1007/BF03046050). URL: <https://doi.org/10.1007/BF03046050>.

*Commentary.*

Here z = P(s, p, a, v), and for pure p, q, r the scalar p·(q r) equals the determinant of the three imaginary coordinate vectors. Only s² = N(p)N(a) is used; N(q) and N(r) are arbitrary. With N(p) = N(q) = N(r) = N(a) = R and s = R it reads P_p P_q P_r z = 2R[R(R + p·q + q·r + r·p) z + det(p, q, r) z a]. The shell condition cannot be dropped: for s = 0, p = i, q = j, r = k, a = i and v = 1 the difference of the two sides is (0, 1, 0, 0). Each purity hypothesis is needed. With s = 1 and the other inputs equal to i, replacing r by 1 or q by 1 gives the difference (0, 0, 0, −4) at v = j, replacing p by 1 gives (−6, −2, 0, 0) at v = 1, and replacing a by 1 gives (−12, −8, 0, 0) at v = 1. These counterexamples were computed independently and are not checked by compiled Lean. The converse direction, for which inputs the triangle identity holds for every v, is not examined. The cited notes give the Bargmann invariant as a cyclic product of overlaps and the Pancharatnam phase of a closed sequence of states; they do not state this integer identity, which is derived here.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_compress_of_eq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_triangle_of_eq`
