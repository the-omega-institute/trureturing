# A Boolean Bruhat interval with no magic word

## Abstract

A crystallographic type B₂ Boolean Bruhat interval has no magic word.

**Definition 1.1 (Elek’s Conjecture 3.3).**

$$claim \Leftrightarrow (\forall S \in Type,\; \forall M \in \operatorname{CoxeterMatrix}\left(S\right),\; \forall W \in Type,\; [\operatorname{Group}\left(W\right)] \forall cs \in \operatorname{CoxeterSystem}\left(M, W\right),\; \forall v \in W,\; \forall w \in W,\; \operatorname{CartanOrigin}\left(M\right) \Rightarrow \left(\operatorname{BruhatLE}\left(cs, v, w\right) \Rightarrow (\operatorname{IsHypercube}\left(cs, v, w\right) \Leftrightarrow \left(\exists Q \in \operatorname{List}\left(S\right),\; \operatorname{MagicFor}\left(cs, v, w, Q\right)\right))\right))$$

*Formalization.* `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.claim` (`✓ std3`).

*Citation.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Commentary.*

“A Bruhat interval [v,w] is a hypercube if and only if there exists a magic word Q for [v,w].”

The Kac–Moody Weyl-group setting is represented by a finite node set and an integral generalized Cartan matrix inducing the Coxeter matrix. The group itself may be infinite. The hypercube predicate asks for a bijection of the full interval with the subsets of a finite set, preserving and reflecting order.

For Bruhat comparison, a reduced word for the upper element must have a positional subword with the lower product. Björner and Brenti’s subword criterion uses a reduced subword. The deletion condition shortens any retained word to a reduced subword with the same product, so the existence tests coincide. For magicness, Elek counts every positional subword. In sts the masks 000 and 101 both give the identity, and 101 retains the nonreduced word ss. Deletion preserves the existence of a product and can change the number of masks.

**Theorem 1.2 (The type B₂ counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Balázs Elek (2026). *Hypercube Richardson varieties from magic words*. DOI: [10.48550/arXiv.2610.22730](https://doi.org/10.48550/arXiv.2610.22730). URL: <https://arxiv.org/abs/2610.22730v1>.

*Acknowledgement.* Anders Björner and Francesco Brenti (2005). *The Bruhat Order*. DOI: [10.1007/3-540-27596-7_2](https://doi.org/10.1007/3-540-27596-7_2). URL: <https://doi.org/10.1007/3-540-27596-7_2>.

*Acknowledgement.* Vincent Umutabazi (2022). *Zircons and smooth Bruhat intervals in symmetric groups*. DOI: [10.48550/arXiv.2206.06538](https://doi.org/10.48550/arXiv.2206.06538). URL: <https://arxiv.org/abs/2206.06538v1>.

*Commentary.*

Use the canonical presentation with simple reflections s,t and braid exponent four, induced by the type B₂ Cartan matrix. The homomorphism to the dihedral group of order eight sends s and t to two adjacent reflections. Testing words through length three under this map and using a shortest word in the presentation gives length(sts) = 3 and forces sts as its only reduced expression.

The subword products below sts are e, s, t, st, ts and sts. Exactly s, st, ts and sts are above s. The Bruhat comparisons on these four elements agree in both directions with subset inclusion under the map to the empty set, {0}, {1} and {0,1}, respectively.

The masks 100 and 001 retain different positions of the only reduced word sts and both give s. The Boolean-to-magic implication therefore fails. Umutabazi uses the same interval for a left-descent criterion. Elek’s Lemma 2.17 gives the related last-letter obstruction to uniqueness even among reduced subwords.

## References

- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.claim`
- Truth anchor: `D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.result`
