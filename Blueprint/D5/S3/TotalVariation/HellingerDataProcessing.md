# Hellinger Data Processing Through Affinity

## Abstract

A nonnegative row-stochastic finite channel increases Bhattacharyya affinity and contracts squared Hellinger distance.

**Theorem 1.1 (Stochastic channels contract squared Hellinger distance).**

$$\begin{gathered}\forall X, Y\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(Y)],\\\forall p, q: X\to \mathbb{R}, W: X\to Y\to \mathbb{R},\\(((\forall x, 0\le p(x)) \land \sum _{x} p(x)=1) \land\\((\forall x, 0\le q(x)) \land \sum _{x} q(x)=1) \land\\((\forall x, y, 0\le W(x, y)) \land (\forall x, \sum _{y} W(x, y)=1))) \Rightarrow \\H^{2}(\operatorname{channelOutput}(W, p), \operatorname{channelOutput}(W, q))\le H^{2}(p, q).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/HellingerDataProcessing.hellinger_sq_channel_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This module completes a data-processing trilogy at this stratum. The repository already contained data processing for Kullback--Leibler divergence, measured in nats, and contraction of total variation; squared Hellinger distance was the missing third member. In three different coordinate systems, all assert the same statistical principle: processing an observation cannot make two laws easier to distinguish.

The passage through the Bhattacharyya coefficient reverses the inequality direction and must not be skimmed. The coefficient is an affinity: it measures overlap rather than separation. Accordingly, the auxiliary theorem proves BC(p,q) <= BC(Wp,Wq), the opposite direction from the total-variation inequality in the sibling module, while the displayed squared Hellinger distance decreases. This is not a typo: destroying information can only make two laws look more alike, which raises overlap and lowers every distance.

The hypotheses separate into an informative hierarchy. Total-variation data processing assumes nothing about p and q: they may be arbitrary real functions, because absolute values and finite sums supply their own sign control. The affinity bound requires p and q to be pointwise nonnegative but does not require normalization, because its coordinates are square roots of products. Only the squared Hellinger bound requires full normalization, and only because it passes through the frozen identity H^2 = 2(1-BC), whose statement is restricted to probability vectors. Normalization enters exactly where that bridge identity demands it and nowhere earlier.

The affinity proof is a pointwise Cauchy--Schwarz argument. For each output coordinate y, mathlib's Real.sum_sqrt_mul_sqrt_le gives sum_x sqrt(p(x)q(x))W(x,y) <= sqrt((sum_x p(x)W(x,y))(sum_x q(x)W(x,y))). The right-hand side is the overlap of the two mixed output masses at y. Summing over y, interchanging the finite sums, and collapsing every channel row sum to one yields affinity growth. No new definition is introduced.

The Hellinger contraction is then a change of coordinates. The proof establishes nonnegativity and unit mass for both channel outputs, applies the frozen identity H^2 = 2(1-BC) to the input and output pairs, and transfers the affinity inequality by linear arithmetic.

The local treatment of the output probability laws is deliberate. A repository search found no public declaration below D5/S3 stating that a stochastic channel maps probability vectors to probability vectors. Rather than promote a second public declaration in anticipation of use, the proof establishes output nonnegativity and unit mass locally. The repository lifts an abstraction at the second instance or under demonstrated pressure; if a second consumer appears, this is the fact to lift.

No characterization of the channels that preserve affinity exactly is claimed. There is no reverse inequality, measure-theoretic analogue, or Renyi- or f-divergence generalization.

## References

- Truth anchor: `D5/S3/TotalVariation/HellingerDataProcessing.hellinger_sq_channel_le`
- Dependency: [D5/S3/TotalVariation/Hellinger](Hellinger.md)
