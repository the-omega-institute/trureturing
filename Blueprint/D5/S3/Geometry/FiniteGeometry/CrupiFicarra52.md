# The maximum size of a projective blocking set with the r∞-property

## Abstract

The sharp maximum in Crupi–Ficarra Open Question 5.2 is q²−q+1 for every finite field of order q≥5.

**Definition 1.1 (Projective blocking set).**

$$\forall \left(F : \operatorname{Type}\right), [\operatorname{Field}\left(F\right)] \forall \left(B : \operatorname{Finset}\left(\left(\mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right)\right)\right), \operatorname{BlockingSet}\left(B\right) = \left(\left(\forall \left(l : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), \exists p \in B, p \in l\right) \land \left(\forall \left(l : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), \neg\left(\forall \left(p : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), p \in l \Rightarrow p \in B\right)\right)\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.BlockingSet` (`✓ std3`).

*Citation.* Marilena Crupi and Antonino Ficarra (2025). *Generalizing blocking semiovals in finite projective planes*. DOI: [10.48550/arXiv.2507.05037](https://doi.org/10.48550/arXiv.2507.05037). URL: <https://arxiv.org/abs/2507.05037v2>.

*Commentary.*

Definition 2.1, arXiv:2507.05037v2, p. 4. “A blocking set of PG(2, q) is a set of points B which meets every line but does not contain any line.”

The first conjunct requires a point of B on every line. The second says no line is contained in B. Points and line covectors are Mathlib projectivizations of triples, with incidence given by a vanishing dot product.

Definition 2.1, p. 4, defines minimality separately. “A blocking set B of PG(2, q) (AG(2, q), respectively) is called minimal if no proper subset of B is a blocking set of PG(2, q) (AG(2, q), respectively).”

**Definition 1.2 (Tangent at a point of the set).**

$$\forall \left(F : \operatorname{Type}\right), [\operatorname{Field}\left(F\right)] \forall \left(B : \operatorname{Finset}\left(\left(\mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right)\right)\right), \forall \left(p : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), \forall \left(l : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), \operatorname{TangentAt}\left(B, p, l\right) = \left(p \in l \land \left(\forall x \in B, x \in l \Rightarrow x = p\right)\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.TangentAt` (`✓ std3`).

*Citation.* Marilena Crupi and Antonino Ficarra (2025). *Generalizing blocking semiovals in finite projective planes*. DOI: [10.48550/arXiv.2507.05037](https://doi.org/10.48550/arXiv.2507.05037). URL: <https://arxiv.org/abs/2507.05037v2>.

*Commentary.*

ArXiv:2507.05037v2, p. 4. “A tangent to K is a line which intersects K in only one point. A secant to K is a line which intersects K in more than one point.”

The line contains p and any point of B on it equals p. The enclosing RInfinity predicate supplies p ∈ B.

**Definition 1.3 (The r∞-property).**

$$\forall \left(F : \operatorname{Type}\right), [\operatorname{Field}\left(F\right)] \forall \left(B : \operatorname{Finset}\left(\left(\mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right)\right)\right), \operatorname{RInfinity}\left(B\right) = \left(\exists p \in B, \exists \left(t : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), \operatorname{TangentAt}\left(B, p, t\right) \land \left(\forall \left(l : \mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right), p \in l \Rightarrow l \neq t \Rightarrow \exists x \in B, x \in l \land x \neq p\right)\right)$$

*Formalization.* `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.RInfinity` (`✓ std3`).

*Citation.* Marilena Crupi and Antonino Ficarra (2025). *Generalizing blocking semiovals in finite projective planes*. DOI: [10.48550/arXiv.2507.05037](https://doi.org/10.48550/arXiv.2507.05037). URL: <https://arxiv.org/abs/2507.05037v2>.

*Commentary.*

Definition 3.1, arXiv:2507.05037v2, p. 5. “Let B be a blocking set in PG(2, q). We say that B has the r∞-property with respect to P ∈ B if there exists through P only one tangent to B, called r∞, and the other lines through P are secants to B. If it is not necessary to specify the point P, we say that B has the r∞-property.”

The predicate gives p ∈ B, a tangent t and a second point x ≠ p of B on every other line through p. The theorem also requires BlockingSet B.

**Theorem 1.4 (The sharp maximum exceeds the proposed threshold).**

$$\forall \left(F : \operatorname{Type}\right), [\operatorname{Field}\left(F\right)] [\operatorname{Fintype}\left(F\right)] 5 \le \operatorname{Fintype}.\operatorname{card}\left(F\right) \Rightarrow \left(\operatorname{IsGreatest}\left(\{n : \mathbb{N} \mid \exists \left(B : \operatorname{Finset}\left(\left(\mathbb{P} F \left(\operatorname{Fin}\left(3\right) \to F\right)\right)\right)\right), \operatorname{BlockingSet}\left(B\right) \land \operatorname{RInfinity}\left(B\right) \land B.\operatorname{card} = n\}, \left(\left(\operatorname{Fintype}.\operatorname{card}\left(F\right)\right)^{2} - \operatorname{Fintype}.\operatorname{card}\left(F\right) + 1\right)\right) \land \left(3 \cdot \left(\operatorname{Fintype}.\operatorname{card}\left(F\right) - 1\right) < \left(\operatorname{Fintype}.\operatorname{card}\left(F\right)\right)^{2} - \operatorname{Fintype}.\operatorname{card}\left(F\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.result` (`✓ std3`). ∎

*Resolves.* `Problems/crupi-ficarra-2025-question-5-2` (proved) by `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"crupi-ficarra-2025-question-5-2","declaration_gid":"D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Marilena Crupi and Antonino Ficarra (2025). *Generalizing blocking semiovals in finite projective planes*. DOI: [10.48550/arXiv.2507.05037](https://doi.org/10.48550/arXiv.2507.05037). URL: <https://arxiv.org/abs/2507.05037v2>.

*Commentary.*

Crupi and Ficarra, Open Question 5.2, arXiv:2507.05037v2, p. 12. “Are there blocking sets with the r∞-property of size k > 3(q−1) in PG(2, q) with q ≥ 5?”

For any field F with Fintype F and q = Fintype.card F ≥ 5, IsGreatest supplies the attaining set and bounds every qualifying set. The maximum exceeds the threshold by (q−2)².

In the affine chart z=1, omit the q points (x:x²:1) and keep every other affine point. Include just the vertical direction P=(0:1:0) at infinity. Each vertical line keeps P and q−1 affine points. A nonvertical line y=mx+b keeps at least q−2 points by the root bound for X²−mX−b and omits its point at infinity. The line at infinity keeps just P. These incidences give both blocking conditions and the unique tangent at P in every characteristic.

For an arbitrary qualifying set, its tangent at p omits q points. Each other line through p omits at least one point, and these q omissions are distinct and off the tangent by uniqueness of the line through two points. The total q²+q+1 points therefore leave room for at most q²−q+1 in the set.

The witness has a proper blocking subset. Deleting one retained affine point leaves P on the line at infinity and a hit on each of the other lines, which had at least two hits. The paper gives a separate definition for inclusion-minimal blocking sets.

## References

- Truth anchor: `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.BlockingSet`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.RInfinity`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.TangentAt`
- Truth anchor: `D5/S3/Geometry/FiniteGeometry/CrupiFicarra52.result`
- Dependency: [D5/S3/Geometry/FiniteGeometry/AffinePlaneLines](AffinePlaneLines.md)
