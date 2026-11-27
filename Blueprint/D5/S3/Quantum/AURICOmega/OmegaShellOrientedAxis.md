# The oriented axis of three quaternion maps

## Abstract

The oriented axis identity for the integer quaternion maps v ↦ (c v) a with pure c and a.

For integer quaternions c and a write u(c, v) = (c v) a; u(c, ·) is the part v ↦ c v a that the shell map P(s, c, a, v) = s v + c v a adds to the multiple s v. Purity means that the real coordinate vanishes, N(a) = a·a is the squared norm, and for pure p, q, r the scalar p·(q r) is the determinant of their imaginary coordinate vectors. The theorem below takes the three compositions u_p u_q u_r, u_q u_r u_p, u_r u_p u_q in cyclic order and subtracts the three compositions in reverse order; the result is the multiple 6 N(a) (p·(q r)) of the single map x ↦ x a. No shell condition and no integer s enter.

The library proof is Omega.Quaternion.oriented_axis in OmegaMath.Algebra.Quaternion.Shell. Since a is pure, a a = −N(a), so each composition reduces to u_A u_B u_C x = −N(a) (A B C x) a. The alternating sum of the six products A B C of the pure quaternions p, q, r is the scalar −6 p·(q r); this step is certified as an integer polynomial identity in the coordinates of p, q, r and x.

**Theorem 1.1 (Oriented axis identity).**

$$\left(\left(\operatorname{pure}\left(p\right) \land \operatorname{pure}\left(q\right)\right) \land \left(\operatorname{pure}\left(r\right) \land \operatorname{pure}\left(a\right)\right)\right) \Rightarrow \operatorname{u}\left(p, a, \operatorname{u}\left(q, a, \operatorname{u}\left(r, a, x\right)\right)\right) + \operatorname{u}\left(q, a, \operatorname{u}\left(r, a, \operatorname{u}\left(p, a, x\right)\right)\right) + \operatorname{u}\left(r, a, \operatorname{u}\left(p, a, \operatorname{u}\left(q, a, x\right)\right)\right) - \left(\operatorname{u}\left(p, a, \operatorname{u}\left(r, a, \operatorname{u}\left(q, a, x\right)\right)\right) + \operatorname{u}\left(r, a, \operatorname{u}\left(q, a, \operatorname{u}\left(p, a, x\right)\right)\right) + \operatorname{u}\left(q, a, \operatorname{u}\left(p, a, \operatorname{u}\left(r, a, x\right)\right)\right)\right) = 6 \cdot \operatorname{N}\left(a\right) \cdot \operatorname{dot}\left(p, \operatorname{mul}\left(q, r\right)\right) \cdot \operatorname{mul}\left(x, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShellOrientedAxis.oriented_axis_from_shell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity holds for every quaternion x; x need not be pure. With p = i, q = j, r = k and a = i, where N(a) = 1 and p·(q r) = 1, it reads 6 x i. Each of the four purity hypotheses is needed. Keep x = 1 and the other inputs as above, and list the difference of the left side minus the right side in coordinates (w, x, y, z): replacing p by 1 gives (2, 0, 0, 0), replacing q by 1 gives (0, 0, 0, 2), replacing r by 1 gives (0, 0, −2, 0), and replacing a by 1 gives (−12, 0, 0, 0). A symbolic expansion of the difference with all sixteen coordinates free confirms that no proper subset of the four hypotheses suffices. These counterexamples and the expansion were computed independently and are not checked by compiled Lean.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShellOrientedAxis.oriented_axis_from_shell`
