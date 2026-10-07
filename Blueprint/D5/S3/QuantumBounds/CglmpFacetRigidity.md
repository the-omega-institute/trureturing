# CGLMP rigidity from short cyclic arcs

## Abstract

A bipartite local functional vanishing on CGLMP saturation is a multiple of the Bell slack.

**Definition 1.1 (Bipartite local functions).**

$$\forall K \in \mathbb{N},\; \forall f \in (\operatorname{Fin}\left(2\right))\to(\operatorname{Fin}\left(2\right))\to(\operatorname{ZMod}\left(K\right))\to(\operatorname{ZMod}\left(K\right))\to\mathbb{R},\; \forall a \in \operatorname{ZMod}\left(K\right),\; \forall A \in \operatorname{ZMod}\left(K\right),\; \forall b \in \operatorname{ZMod}\left(K\right),\; \forall B \in \operatorname{ZMod}\left(K\right),\; \operatorname{BipLocal}\left(f, a, A, b, B\right) = \sum_{x:\operatorname{Fin}\left(2\right)}(\sum_{y:\operatorname{Fin}\left(2\right)}(f(x,y,(\operatorname{if}\left(x = 0\right)\operatorname{then}\left(a\right)\operatorname{else}\left(A\right)),(\operatorname{if}\left(y = 0\right)\operatorname{then}\left(b\right)\operatorname{else}\left(B\right)))))$$

*Formalization.* `D5/S3/QuantumBounds/CglmpFacetRigidity.BipLocal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ll. Masanes (2003). *Tight Bell inequality for d-outcome measurements correlations*. DOI: [10.26421/QIC3.4-4](https://doi.org/10.26421/QIC3.4-4). URL: <https://arxiv.org/abs/quant-ph/0210073v1>.

*Commentary.*

Every linear functional of a deterministic two-party full behaviour is a sum over the four setting pairs of a function of the two outputs selected by that pair. The coefficients f are arbitrary real numbers. The lowercase outputs a,b belong to setting 0 and A,B to setting 1; these are settings 1 and 2 in the source.

**Definition 1.2 (The relabelled CGLMP expression).**

$$\forall K \in \mathbb{N},\; \forall a \in \operatorname{ZMod}\left(K\right),\; \forall A \in \operatorname{ZMod}\left(K\right),\; \forall b \in \operatorname{ZMod}\left(K\right),\; \forall B \in \operatorname{ZMod}\left(K\right),\; \operatorname{J2AB}\left(a, A, b, B\right) = \operatorname{val}\left(A - b\right) + \operatorname{val}\left(a + B\right) + \operatorname{val}\left(-(a) + b\right) + \operatorname{val}\left(-(A) - B - 1\right)$$

*Formalization.* `D5/S3/QuantumBounds/CglmpFacetRigidity.J2AB` (`✓ std3`).

*Citation.* B. Grandjean; Y.-C. Liang; J.-D. Bancal; N. Brunner; N. Gisin (2012). *Bell inequalities for three systems and arbitrarily many measurement outcomes*. DOI: [10.48550/arXiv.1204.3829](https://doi.org/10.48550/arXiv.1204.3829). URL: <https://arxiv.org/abs/1204.3829v2>.

*Commentary.*

Grandjean et al., Section II, PDF p. 2, identify the C_1=C_2=0 restriction of (1) as CGLMP, after relabelling B_2 to its negative residue. J2AB is the four-bracket deterministic restriction before that relabelling. ZMod.val denotes the natural least nonnegative residue when K is nonzero.

**Lemma 1.3 (Complementary residues).**

$$\forall d \in \mathbb{N},\; [\operatorname{NeZero}\left(d\right)] \forall r \in \operatorname{ZMod}\left(d\right),\; \operatorname{val}\left(-(r) - 1\right) = d - 1 - \operatorname{val}\left(r\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CglmpFacetRigidity.val_neg_sub_one` (`✓ std3`). ∎

*Citation.* Zayn Blore (2026). *The CGLMP qudit Bell inequality and its local-hidden-variable bound*. URL: <https://github.com/zblore/csd-lean4/blob/2c99cf483541a808dc8a320ec4213ec3d3614992/CsdLean4/Mathlib/Probability/CGLMP.lean>.

*Commentary.*

The residues of x and −x−1 add to K−1. All subtractions on the displayed right side are natural truncated subtraction. The residue bound makes them equal to ordinary subtraction in this expression.

**Theorem 1.4 (Rigidity on CGLMP saturation).**

$$\forall K \in \mathbb{N},\; [\operatorname{NeZero}\left(K\right)] \forall f \in (\operatorname{Fin}\left(2\right))\to(\operatorname{Fin}\left(2\right))\to(\operatorname{ZMod}\left(K\right))\to(\operatorname{ZMod}\left(K\right))\to\mathbb{R},\; (\forall a \in \operatorname{ZMod}\left(K\right),\; \forall A \in \operatorname{ZMod}\left(K\right),\; \forall b \in \operatorname{ZMod}\left(K\right),\; \forall B \in \operatorname{ZMod}\left(K\right),\; (\operatorname{J2AB}\left(a, A, b, B\right) = K - 1) \Rightarrow (\operatorname{BipLocal}\left(f, a, A, b, B\right) = 0)) \Rightarrow (\exists lam \in \mathbb{R},\; \forall a \in \operatorname{ZMod}\left(K\right),\; \forall A \in \operatorname{ZMod}\left(K\right),\; \forall b \in \operatorname{ZMod}\left(K\right),\; \forall B \in \operatorname{ZMod}\left(K\right),\; \operatorname{BipLocal}\left(f, a, A, b, B\right) = lam \cdot ((\operatorname{J2AB}\left(a, A, b, B\right):\mathbb{R}) - ((K:\mathbb{R}) - 1)))$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/CglmpFacetRigidity.bipartite_rigidity` (`✓ std3`). ∎

*Citation.* Ll. Masanes (2003). *Tight Bell inequality for d-outcome measurements correlations*. DOI: [10.26421/QIC3.4-4](https://doi.org/10.26421/QIC3.4-4). URL: <https://arxiv.org/abs/quant-ph/0210073v1>.

*Commentary.*

Masanes, abstract, PDF p. 1, states: “In this paper we prove that the inequality introduced by Collins, Gisin, Linden, Massar and Popescu [11] is tight, or in other words, it is a facet of the convex polytope generated by all local-realistic joint probabilities of d outcomes.” The statement below is the dual-functional formulation of that facet conclusion. The conclusion is literature-attested; the short-arc proof here is a different argument. Saturating quadruples reduce every four-edge local function to H(a,b)+H(b,c)+H(c,d)−H(a,d). On arcs of total length less than K, H is additive. A potential P and a single wrap coefficient describe every H, and the potential telescopes. This yields one common multiplier for every quadruple, including K=1; the nontrivial facet interpretation concerns K >= 2.

## References

- Truth anchor: `D5/S3/QuantumBounds/CglmpFacetRigidity.BipLocal`
- Truth anchor: `D5/S3/QuantumBounds/CglmpFacetRigidity.J2AB`
- Truth anchor: `D5/S3/QuantumBounds/CglmpFacetRigidity.bipartite_rigidity`
- Truth anchor: `D5/S3/QuantumBounds/CglmpFacetRigidity.val_neg_sub_one`
