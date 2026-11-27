# Exactness of the shell compression and triangle identities

## Abstract

Exact classifications of the inputs for which the shell compression and triangle identities hold for every v.

For an integer s and integer quaternions p, a the shell map is P(s, p, a, v) = s v + p v a. Purity means that the real coordinate vanishes and N(x) = x·x is the squared norm. On the shell s² = N(p)N(a) the composition P_p P_q P_p is the multiple 2(s² + N(a) p·q) of P_p, and P_p P_q P_r P_p is 2s(s² + N(a)(p·q + q·r + r·p)) P_p plus 2N(a) p·(q r) times the map v ↦ (P_p v) a. The two theorems below state, for pure p, q, r, a, exactly which inputs make these defect-free identities hold for every quaternion v.

The library proofs are Omega.Quaternion.shell_compress_iff and Omega.Quaternion.shell_triangle_iff in OmegaMath.Algebra.Quaternion.Shell. Both start from the exact identities Omega.Quaternion.shell_compress and Omega.Quaternion.shell_triangle, whose defect terms are (s² − N(p)N(a)) P_{−s,q,a} v and (N(p)N(a) − s²) P_{−s,r,a} P_{−s,q,a} v. For the triangle, the composite P_{−s,r,a} P_{−s,q,a} is the pair action v ↦ c v + (d v) a with c = s² − N(a)(r q) and d = −s(q + r). A pair action that vanishes for every v has c = 0, and d = 0 unless a = 0: evaluating at v = 1 gives c = −d a, and then d (u a − a u) = 0 for u = i, j, k; since integer quaternions have no zero divisors (Omega.Quaternion.eq_zero_or_eq_zero_of_mul_eq_zero, from the multiplicativity of the squared norm), either d = 0 or all three commutators vanish, which for pure a forces a = 0. The case analysis on s = 0 and q + r = 0 then gives the three cases of the classification.

**Theorem 1.1 (Exact compression condition).**

$$\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \Rightarrow \left(\left(\forall v \in Quaternion,\; \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, p, a, v\right)\right)\right) = 2 \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, q\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right)\right) \Leftrightarrow \left(s \cdot s = \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right) \lor \left(s = 0 \land q = 0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellExactness.shell_compress_iff_of_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The degenerate case s = 0, q = 0 is the only way off the shell: then both sides vanish. When a = 0 or p = 0 the shell condition reads s = 0; for a = 0 the identity itself reduces to s³ v = 2 s³ v. Each purity hypothesis is needed for the equivalence. With s = 1 and the other inputs equal to i the shell condition holds, yet replacing q by 1 gives the difference (0, 0, 0, −4) of the two sides at v = j, replacing a by 1 gives (−6, −2, 0, 0) at v = 1, and replacing p by 1 gives (−2, −2, 0, 0) at v = 1; coordinates are listed as (w, x, y, z), and each replacement keeps the right-hand case true and the other hypotheses intact. These counterexamples were computed independently and are not checked by compiled Lean.

**Theorem 1.2 (Exact triangle condition).**

$$\left(\left(\operatorname{pure}\left(p\right) \land \left(\operatorname{pure}\left(q\right) \land \operatorname{pure}\left(a\right)\right)\right) \land \operatorname{pure}\left(r\right)\right) \Rightarrow \left(\left(\forall v \in Quaternion,\; \operatorname{P}\left(s, p, a, \operatorname{P}\left(s, q, a, \operatorname{P}\left(s, r, a, \operatorname{P}\left(s, p, a, v\right)\right)\right)\right) = 2 \cdot s \cdot \left(s \cdot s + \operatorname{N}\left(a\right) \cdot \left(\operatorname{dot}\left(p, q\right) + \operatorname{dot}\left(q, r\right) + \operatorname{dot}\left(r, p\right)\right)\right) \cdot \operatorname{P}\left(s, p, a, v\right) + 2 \cdot \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, \operatorname{mul}\left(q, r\right)\right) \cdot \operatorname{mul}\left(\operatorname{P}\left(s, p, a, v\right), a\right)\right) \Leftrightarrow \left(s \cdot s = \operatorname{N}\left(p\right) \cdot \operatorname{N}\left(a\right) \lor \left(\left(s = 0 \land \left(q = 0 \lor r = 0\right)\right) \lor \left(q = -r \land s \cdot s = \operatorname{N}\left(r\right) \cdot \operatorname{N}\left(a\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellExactness.shell_triangle_iff_of_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here z = P(s, p, a, v). Besides the shell there are two families. If s = 0 and q = 0 or r = 0, the composite P_{−s,r,a} P_{−s,q,a} is zero. If q = −r and s² = N(r)N(a), then d = 0 and c = s² − N(a)N(r) = 0 because r r = −N(r); this family is genuinely off the shell, for instance s = 1, p = 2j, q = −i, r = i, a = i, where N(p)N(a) = 4. Degenerate cases: for a = 0 the identity reads s⁴ v = 2 s⁴ v and all three cases reduce to s = 0; for p = 0 the shell condition is s = 0; for q = 0 or r = 0 the third case is contained in the second, so the condition is s² = N(p)N(a) or s = 0; for s = 0 the condition is that one of p, q, r, a is zero. Each purity hypothesis is needed for the equivalence. With s = 1, q = r = 0 and a = i, the shell condition holds for p = 1 but the difference of the two sides at v = 1 is (−2, 0, 0, 0); with s = 1, p = a = i and r = 0, replacing q by 1 gives the difference (0, 0, 0, −4) at v = j, and the same holds with q = 0 and r replaced by 1; with s = 1, p = i, q = r = 0 and a = 1 the difference at v = 1 is (−2, 0, 0, 0). In each example the shell condition holds and the remaining hypotheses are intact, so the right-hand side is true while the identity fails. These counterexamples were computed independently and are not checked by compiled Lean.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellExactness.shell_compress_iff_of_shell`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellExactness.shell_triangle_iff_of_shell`
