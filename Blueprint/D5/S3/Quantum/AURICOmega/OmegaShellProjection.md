# Shell compression and the oriented triangle

## Abstract

Shell maps of integer quaternions: two-point compression and the oriented triangle identity.

For an integer s and quaternions p, a the shell map is P(s, p, a, v) = s v + p v a. Purity of p, q, r and a means that the real coordinate vanishes, and N(x) = x·x is the squared norm. The pair action v ↦ c v + (d v) a composes by the rule obtained from a a = −N(a), which reduces every identity below to an integer polynomial identity in the coordinates of p, q, r, the integer s and the integer N(a).

**Theorem 1.1 (Two-point shell compression).**

$$\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \Rightarrow \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, p, a, v\right)\right)\right) = 2 \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, q\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right) + \left(s \cdot s - \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right)\right) \cdot \operatorname{P}\left(0 - s, q, a, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_compress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

No norm condition is assumed. The last term is (s² − N(p)N(a)) (q v a − s v). Each purity hypothesis is needed: a symbolic expansion with a general real coordinate in p, in q or in a gives a nonzero difference.

**Theorem 1.2 (Compression on the shell).**

$$\left(\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \land s \cdot s = \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right)\right) \Rightarrow \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, p, a, v\right)\right)\right) = 2 \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, q\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_compress_of_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When s² = N(p)N(a) the map P(s, p, a, ·) squares to 2s times itself, and the composition through q returns a multiple of the same map. The coefficient 2(s² + N(a)(p·q)) needs no condition on N(q).

**Theorem 1.3 (Oriented triangle identity).**

$$\left(\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \land \operatorname{pure}\left(r\right)\right) \Rightarrow \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, r, a, \operatorname{P}\left(s, p, a, v\right)\right)\right)\right) = 2 \cdot s \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \left(\operatorname{dot}\left(p, q\right) + \operatorname{dot}\left(q, r\right) + \operatorname{dot}\left(r, p\right)\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right) + 2 \cdot \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, \operatorname{mul}\left(q, r\right)\right) \cdot \operatorname{mul}\left(\operatorname{P}\left(s, p, a, v\right), a\right) + \left(\operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right) - s \cdot s\right) \cdot \operatorname{P}\left(0 - s, r, a, \operatorname{P}\left(0 - s, q, a, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here z = P(s, p, a, v). No norm condition is assumed. For pure p, q, r the scalar p·(q r) equals the determinant of the three imaginary coordinate vectors. The defect is (N(p)N(a) − s²) times the composition (s − r · a)(s − q · a) applied to v. Purity of p, q, r and a is each needed by the same symbolic test.

**Theorem 1.4 (Triangle identity on the shell).**

$$\left(\left(\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \land \operatorname{pure}\left(r\right)\right) \land s \cdot s = \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right)\right) \Rightarrow \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, r, a, \operatorname{P}\left(s, p, a, v\right)\right)\right)\right) = 2 \cdot s \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \left(\operatorname{dot}\left(p, q\right) + \operatorname{dot}\left(q, r\right) + \operatorname{dot}\left(r, p\right)\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right) + 2 \cdot \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, \operatorname{mul}\left(q, r\right)\right) \cdot \operatorname{mul}\left(\operatorname{P}\left(s, p, a, v\right), a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_triangle_of_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Only s² = N(p)N(a) is used; N(q) and N(r) are arbitrary. With N(p) = N(q) = N(r) = N(a) = R and s = R this reads P_p P_q P_r z = 2R[R(R + p·q + q·r + r·p) z + det(p, q, r) z a]. Over the real numbers P/(2s) is then a rank-one projection of the quaternions viewed as a two-dimensional complex space; that identification is not formalized in this module.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_compress`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_compress_of_eq`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_triangle`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellProjection.shell_triangle_of_eq`
