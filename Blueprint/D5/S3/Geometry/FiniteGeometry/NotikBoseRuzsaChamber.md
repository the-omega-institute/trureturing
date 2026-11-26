# The Bose and Ruzsa chamber assertions

## Abstract

Shorter real rulers refute both of Notik's chamber analogues.

**Definition 1.1 (Increasing pairs of mark indices).**

$$\forall n: \mathbb{N}, \operatorname{Label}\left(n\right)=\{(i,j): \operatorname{Fin}\left(n+1\right)\times \operatorname{Fin}\left(n+1\right)\mid i<j\}$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.Label` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

There are n kept gaps and n + 1 marks.

**Definition 1.2 (Interval sum of kept gaps).**

$$\forall A: \operatorname{Type}, [\operatorname{AddCommMonoid}\left(A\right)] \forall n: \mathbb{N}, \forall g: \operatorname{Fin}\left(n\right) \to A, \forall i: \mathbb{N}, \forall j: \mathbb{N}, \operatorname{intervalSum}\left(g, i, j\right)=\sum_{k: \operatorname{Fin}\left(n\right), i\leq k.\operatorname{val}<j}g\left(k\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.intervalSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The finite sum includes a gap exactly when its index lies between i inclusive and j exclusive.

**Definition 1.3 (Labelled distance).**

$$\forall A: \operatorname{Type}, [\operatorname{AddCommMonoid}\left(A\right)] \forall n: \mathbb{N}, \forall g: \operatorname{Fin}\left(n\right) \to A, \forall p: \operatorname{Label}\left(n\right), \operatorname{distance}\left(g, p\right)=\operatorname{intervalSum}\left(g, p_{1}.\operatorname{val}, p_{2}.\operatorname{val}\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.distance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The first and second components of the pair p are the endpoints of the interval.

**Definition 1.4 (Unit separation in reference order).**

$$\forall A: \operatorname{Type}, [\operatorname{AddCommMonoid}\left(A\right)] [\operatorname{One}\left(A\right)] [\operatorname{LE}\left(A\right)] \forall n: \mathbb{N}, \forall g: \operatorname{Fin}\left(n\right) \to \mathbb{N}, \forall x: \operatorname{Fin}\left(n\right) \to A, \operatorname{ChamberOrder}\left(g, x\right)\iff (\forall p: \operatorname{Label}\left(n\right), \forall q: \operatorname{Label}\left(n\right), \operatorname{distance}\left(g, p\right)=\operatorname{distance}\left(g, q\right) \implies p=q) \land ((\forall p: \operatorname{Label}\left(n\right), 1\leq \operatorname{distance}\left(x, p\right)) \land (\forall p: \operatorname{Label}\left(n\right), \forall q: \operatorname{Label}\left(n\right), \operatorname{distance}\left(g, p\right)<\operatorname{distance}\left(g, q\right) \implies \operatorname{distance}\left(x, p\right)+1\leq \operatorname{distance}\left(x, q\right)))$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.ChamberOrder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Distinct labels have distinct reference distances. Every candidate distance is at least one, and the ordered inequalities separate each pair of labelled distances by at least one. The consecutive rows give all these inequalities by adding along the ordered list.

**Definition 1.5 (Unique shortest point of the chamber).**

$$\forall n: \mathbb{N}, \forall g: \operatorname{Fin}\left(n\right) \to \mathbb{N}, \operatorname{UniqueShortest}\left(g\right)\iff (\operatorname{ChamberOrder}\left(g, (i\mapsto (g\left(i\right): \mathbb{R}))\right)) \land (\forall x: \operatorname{Fin}\left(n\right) \to \mathbb{R}, \operatorname{ChamberOrder}\left(g, x\right) \implies \operatorname{intervalSum}\left(x, 0, n\right)\leq (\operatorname{intervalSum}\left(g, 0, n\right): \mathbb{R}) \implies x=(i\mapsto (g\left(i\right): \mathbb{R})))$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.UniqueShortest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The reference itself lies in the real chamber. Every point of the chamber of at most its total length has the same gap vector.

**Definition 1.6 (Cut at a largest cyclic gap).**

$$\forall M: \mathbb{N}, \forall n: \mathbb{N}, \forall S: \operatorname{Fin}\left(M\right) \to \operatorname{Prop}, \forall b: \operatorname{Fin}\left(M\right), \forall g: \operatorname{Fin}\left(n\right) \to \mathbb{N}, \operatorname{LargestGapCut}\left(S, b, g\right)\iff (\forall i: \operatorname{Fin}\left(n\right), 0<g\left(i\right)) \land ((\operatorname{intervalSum}\left(g, 0, n\right)<M) \land ((\forall i: \operatorname{Fin}\left(n\right), g\left(i\right)\leq M-\operatorname{intervalSum}\left(g, 0, n\right)) \land (\forall r: \operatorname{Fin}\left(M\right), S\left(r\right)\iff \exists i: \operatorname{Fin}\left(n+1\right), r.\operatorname{val}=\operatorname{mod}\left(b.\operatorname{val}+\operatorname{intervalSum}\left(g, 0, i.\operatorname{val}\right), M\right))))$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.LargestGapCut` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Increasing offsets from the starting residue exhaust the cyclic set. Their total length is below the modulus, and the wraparound gap is at least every kept gap.

**Definition 1.7 (Scaled affine-line exponent).**

$$\forall F: \operatorname{Type}, \forall K: \operatorname{Type}, [\operatorname{Field}\left(F\right)] [\operatorname{Field}\left(K\right)] [\alpha: \operatorname{Algebra}\left(F, K\right)] \forall M: \mathbb{N}, \forall \theta: K, \forall u: \mathbb{N}, \forall r: \operatorname{Fin}\left(M\right), \left(\operatorname{BoseResidue}_{F, K, \alpha}\right)\left(\theta, u, r\right)\iff \exists e: \operatorname{Fin}\left(M\right), (r.\operatorname{val}=\operatorname{mod}\left(u\cdot e.\operatorname{val}, M\right)) \land (\exists a: F, \theta^{e.\operatorname{val}}=\theta+\operatorname{algebraMap}\left(F, K, a\right))$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.BoseResidue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The map from F to K is the given field embedding. The exponent ranges over the entire cyclic modulus.

**Definition 1.8 (Scaled CRT residue).**

$$\forall p: \mathbb{N}, \forall h: \operatorname{ZMod}\left(p\right), \forall u: \mathbb{N}, \forall r: \operatorname{Fin}\left(p\cdot (p-1)\right), \operatorname{RuzsaResidue}\left(h, u, r\right)\iff \exists s: \operatorname{Fin}\left(p\cdot (p-1)\right), \exists i: \operatorname{Fin}\left(p-1\right), (r.\operatorname{val}=\operatorname{mod}\left(u\cdot s.\operatorname{val}, p\cdot (p-1)\right)) \land ((\operatorname{mod}\left(s.\operatorname{val}, p-1\right)=i.\operatorname{val}) \land ((s.\operatorname{val}: \operatorname{ZMod}\left(p\right))=h^{i.\operatorname{val}}))$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.RuzsaResidue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The cast to ZMod p and the remainder modulo p minus one specify the two congruences of the unscaled residue.

**Definition 1.9 (Bose universal assertion).**

$$\operatorname{Bose}\iff \forall q: \mathbb{N}, \forall F: \operatorname{Type}, \forall K: \operatorname{Type}, [\operatorname{Field}\left(F\right)] [\operatorname{Field}\left(K\right)] [\alpha: \operatorname{Algebra}\left(F, K\right)] [\operatorname{Finite}\left(F\right)] \operatorname{card}\left(F\right)=q \implies \operatorname{card}\left(K\right)=q^{2} \implies \forall \theta: K, \forall u: \mathbb{N}, \operatorname{orderOf}\left(\theta\right)=q^{2}-1 \implies \operatorname{Coprime}\left(u, q^{2}-1\right) \implies \forall b: \operatorname{Fin}\left(q^{2}-1\right), \forall g: \operatorname{Fin}\left(q-1\right) \to \mathbb{N}, \operatorname{LargestGapCut}\left((\left(\operatorname{BoseResidue}_{F, K, \alpha}\right)\left(\theta, u\right)), b, g\right) \implies \operatorname{UniqueShortest}\left(g\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.Bose` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The finite base field has size q, and its extension has size q squared. The multiplicative generator, coprime multiplier, and largest-gap cut are all universally quantified.

**Definition 1.10 (Ruzsa universal assertion).**

$$\operatorname{Ruzsa}\iff \forall p: \mathbb{N}, \operatorname{Prime}\left(p\right) \implies \forall h: \operatorname{ZMod}\left(p\right), \forall u: \mathbb{N}, \operatorname{orderOf}\left(h\right)=p-1 \implies \operatorname{Coprime}\left(u, p\cdot (p-1)\right) \implies \forall b: \operatorname{Fin}\left(p\cdot (p-1)\right), \forall g: \operatorname{Fin}\left(p-2\right) \to \mathbb{N}, \operatorname{LargestGapCut}\left((\operatorname{RuzsaResidue}\left(h, u\right)), b, g\right) \implies \operatorname{UniqueShortest}\left(g\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.Ruzsa` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

The prime, primitive root, coprime multiplier, and largest-gap cut are all universally quantified.

**Definition 1.11 (The two questions in Section 10).**

$$\operatorname{claim}\iff (\operatorname{Bose} \lor \operatorname{Ruzsa})$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.claim` (`✓ std3`).

*Citation.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

Section 10 asks the two analogues of the Section 7 conjecture. The disjunction asks whether either universal assertion holds.

**Theorem 1.12 (Both universal assertions are false).**

$$\neg (\operatorname{Bose} \lor \operatorname{Ruzsa})$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result` (`✓ std3`). ∎

*Resolves.* `Problems/notik-bose-ruzsa-chambers` (refuted) by `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"notik-bose-ruzsa-chambers","declaration_gid":"D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Esther Notik (2026). *Golomb rulers with real marks: the real and integer optima agree up to ten marks*. DOI: [10.48550/arXiv.2611.22656](https://doi.org/10.48550/arXiv.2611.22656). URL: <https://arxiv.org/abs/2611.22656v1>.

*Commentary.*

For Bose, use the field adjoining a root of X squared plus four over F seven. The generator is one plus that root and has order 48. Multiplication by five gives residues 4, 5, 9, 11, 30, 39, 42. Cutting between 11 and 30 gives gaps (9, 3, 10, 1, 4, 2). The rational gaps (17/2, 3, 19/2, 1, 4, 2) preserve the chamber and shorten the total from 29 to 28. For Ruzsa, the prime is five, the primitive root is two, and the multiplier is one. The residues 3, 14, 16, 17 give the cut between 3 and 14. The gaps (2, 1, 5) lie in the chamber of (2, 1, 6) and shorten the total from 9 to 8. The exact rational inequalities transfer to real gaps.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.Bose`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.BoseResidue`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.ChamberOrder`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.Label`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.LargestGapCut`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.Ruzsa`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.RuzsaResidue`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.UniqueShortest`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.claim`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.distance`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.intervalSum`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/NotikBoseRuzsaChamber.result`
