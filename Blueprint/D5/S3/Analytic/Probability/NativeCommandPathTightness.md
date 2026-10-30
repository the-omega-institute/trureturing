# Submesh oscillations of stopped native commands

## Abstract

Joint fourth oscillations of the actual native commands on blocks no longer than one mesh cell.

A raw model B determines the original command triple (a,b,j), with j its ordinary chronological area. Each complete word consists of n cubed independent sign pairs and has mass 4 to the power minus n cubed. Unused suffixes after the first wall contact retain this same mass. Write delta=1/n squared. The final forced upper-wall leg begins at time n if no earlier wall has been reached.

For an anchored block I=[a,min(R,a+h)], blockFourthOscillation is the supremum over s,t in I of the fourth power of the norm of command(t)-command(s). The norm is the maximum coordinate norm on the joint real triple. blockFourthExpectation is the sum of this quantity over all complete words with their original common mass.

**Theorem 1.1 (Fourth oscillations on submesh blocks).**

$$\forall B: Model, \exists C: \mathbb{R}, (0 \le C) \land (\forall R: \mathbb{R}, (0 < R) \Rightarrow (\forall n: \mathbb{N}, (R + 1 < n) \Rightarrow (\forall a: \mathbb{R}, \forall h: \mathbb{R}, (0 \le a) \Rightarrow ((a \le R) \Rightarrow ((0 < h) \Rightarrow ((h \le \operatorname{mesh}\left(n\right)) \Rightarrow ((\operatorname{blockFourthExpectation}\left(B, n, R, a, h\right) \le C \cdot h^{2}) \land (\forall w: \operatorname{Fin}\left(n^{3}\right) \to SignPair, \forall t: \mathbb{R}, (0 \le t) \Rightarrow (\operatorname{commandArea}\left(B, n, w, t\right) = \operatorname{coordinate}\left(\operatorname{command}\left(B, n, w, t\right), 2\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/NativeCommandPathTightness.actual_short_block_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant is common to every horizon and every complete word law satisfying the displayed conditions. The area identity holds at every nonnegative time. The restriction R+1<n places the observed interval before the terminal upper-wall leg.

Periodicity reduces the compact coefficient estimate to a single phase fundamental domain. Smoothness bounds both drift entries and both diagonal covariance entries there. The positive matrix square root identity bounds every noise coefficient by those diagonal entries, yielding a common bound L sqrt(delta) for both horizontal increments from every alive node.

The stopped height lies between the two walls, so the first real control is bounded during each executed chord. The polynomial chord formula then bounds the change of all three coordinates by a constant times sqrt(delta) times the change of its interpolation parameter. Clipping this parameter at the first wall contact preserves its Lipschitz bound.

Induction over the original word joins the chord estimates at the actual surviving nodes. Splitting at a node also covers a block which straddles that node. On the interval before the terminal leg, the resulting path has Lipschitz constant at most K/sqrt(delta). Its fourth oscillation on a block of length h is at most K to the fourth power times h to the fourth power divided by delta squared. For h<=delta this is bounded by K to the fourth power times h squared. Summing the pointwise bound over the complete uniform word law preserves the constant.

This estimate applies only to blocks of length at most delta. Control of larger blocks, and tightness in continuous path space, require a further probabilistic oscillation estimate.

## References

- Truth anchor: `D5/S3/Analytic/Probability/NativeCommandPathTightness.actual_short_block_estimate`
- Dependency: [D5/S3/Analytic/Probability/NativeCommandLifetime](NativeCommandLifetime.md)
