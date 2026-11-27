# Strict local quaternion sharpness

## Abstract

A phase-normalized potential gives a quantitative fit gap near the quarter turn. Weighted variance identifies an angular region in which this estimate applies.

Write S for the group of unit real quaternions. The gain assignment G has identity on the diagonal and on all spokes at vertex zero. The three cyclic rim gains are the entries of A and all reverse gains are inverses. The radius e is the maximum of the round angles of the three spokes' triangles and the cyclic rim triangle. The predicate Fits bounds the round distance from a gain to the transported vertex potential on each directed edge.

Write QPair for the complex-pair coordinates of a real quaternion in the basis 1, I, J, IJ. The transverse field W consists of the two nonconstant Fourier modes of the cyclic rim. Write E for the maximum absolute scalar perturbation and Rho for three fiftieths. The coefficient C is twice the quarter-turn radius divided by pi. The potential P first rotates the transverse phase to make the product of the second Fourier coefficient and the root-of-unity difference real and nonnegative, uses the prescribed rim potentials, and transports them back.

**Theorem 1.1 (Strict quantitative local fit).**

$$\forall A \in \operatorname{Fin}\left(3\right) \to S,\; \forall p \in \mathbb{C},\; \forall q \in \mathbb{C},\; \forall eta \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall gamma \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{gain}\left(A, j\right) = \operatorname{QPair}\left((-\operatorname{val}\left(eta, j\right),\operatorname{val}\left(gamma, j\right)), \operatorname{W}\left(p, q, j\right)\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{val}\left(gamma, j\right) = \sqrt{1-(\operatorname{val}\left(eta, j\right))^{2}-(\lvert \operatorname{W}\left(p, q, j\right) \rvert)^{2}}) \Rightarrow ((\forall j \in \operatorname{Fin}\left(3\right),\; 0 < \operatorname{val}\left(gamma, j\right)) \Rightarrow (((\lvert p \rvert \leq Rho) \land ((\lvert q \rvert \leq Rho) \land (\operatorname{E}\left(eta\right) \leq Rho))) \Rightarrow ((\operatorname{DefectLE}\left(\operatorname{G}\left(A\right), \operatorname{e}\left(A\right)\right)) \land ((\exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; (i \neq j) \land ((j \neq k) \land ((i \neq k) \land (\operatorname{roundDist}\left(\operatorname{edge}\left(\operatorname{G}\left(A\right), i, j\right) \cdot \operatorname{edge}\left(\operatorname{G}\left(A\right), j, k\right), \operatorname{edge}\left(\operatorname{G}\left(A\right), i, k\right)\right) = \operatorname{e}\left(A\right))))) \land ((\forall i \in \operatorname{Fin}\left(4\right),\; \forall j \in \operatorname{Fin}\left(4\right),\; (i \neq j) \Rightarrow (\operatorname{cos}\left(C \cdot \operatorname{e}\left(A\right)\right)+\frac{\lvert q \rvert}{200}+\frac{3}{100} \cdot ((\lvert p \rvert)^{2}+\operatorname{E}\left(eta\right)) \leq \langle \operatorname{edge}\left(\operatorname{G}\left(A\right), i, j\right), (\operatorname{val}\left(\operatorname{P}\left(p, q\right), i\right))^{-1} \cdot \operatorname{val}\left(\operatorname{P}\left(p, q\right), j\right) \rangle)) \land ((\operatorname{Fits}\left(\operatorname{G}\left(A\right), \operatorname{P}\left(p, q\right), C \cdot \operatorname{e}\left(A\right)\right)) \land (((\neg ((p = 0) \land ((q = 0) \land (eta = 0)))) \Rightarrow (\exists R \in \mathbb{R},\; (R < C \cdot \operatorname{e}\left(A\right)) \land (\operatorname{Fits}\left(\operatorname{G}\left(A\right), \operatorname{P}\left(p, q\right), R\right)))) \land (((p = 0) \land ((q = 0) \land (eta = 0))) \Rightarrow (\forall z \in \operatorname{Fin}\left(4\right) \to S,\; \forall R \in \mathbb{R},\; (R < C \cdot \operatorname{e}\left(A\right)) \Rightarrow (\neg (\operatorname{Fits}\left(\operatorname{G}\left(A\right), z, R\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness.quarterLocal_strictFit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rim scores have a common quadratic term and controlled cubic and higher-degree terms. The largest triangle defect bounds a scalar combination of the axial and transverse perturbations. A supporting tangent for the cosine of the scaled defect converts these bounds into the displayed score gap. At the center the cyclic quarter-turn obstruction attains its sharp radius.

In the chart the three axial angles are a, b, and c. The second and third imaginary directions are separated from the first by u and v, with relative azimuth w. The functions Chart and Defect denote the resulting gains and their exact triangle defect.

**Theorem 1.2 (Weighted-variance angular neighborhood).**

$$\forall a \in \mathbb{R},\; \forall b \in \mathbb{R},\; \forall c \in \mathbb{R},\; \forall u \in \mathbb{R},\; \forall v \in \mathbb{R},\; \forall w \in \mathbb{R},\; ((\lvert a-\frac{\pi}{2} \rvert \leq \frac{17}{900} \cdot \pi) \land ((\lvert b-\frac{\pi}{2} \rvert \leq \frac{17}{900} \cdot \pi) \land ((\lvert c-\frac{\pi}{2} \rvert \leq \frac{17}{900} \cdot \pi) \land ((0 \leq u) \land ((0 \leq v) \land ((u+v < \frac{\pi}{2}) \land ((u)^{2}+(v)^{2}+(u+v)^{2} \leq \frac{4497}{500} \cdot (\frac{3}{50})^{2}))))))) \Rightarrow ((\operatorname{DefectLE}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), \operatorname{Defect}\left(a, b, c, u, v, w\right)\right)) \land ((\exists i \in \operatorname{Fin}\left(4\right),\; \exists j \in \operatorname{Fin}\left(4\right),\; \exists k \in \operatorname{Fin}\left(4\right),\; (i \neq j) \land ((j \neq k) \land ((i \neq k) \land (\operatorname{roundDist}\left(\operatorname{edge}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), i, j\right) \cdot \operatorname{edge}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), j, k\right), \operatorname{edge}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), i, k\right)\right) = \operatorname{Defect}\left(a, b, c, u, v, w\right))))) \land ((\exists p \in \operatorname{Fin}\left(4\right) \to S,\; (\operatorname{Fits}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), p, C \cdot \operatorname{Defect}\left(a, b, c, u, v, w\right)\right)) \land ((\neg ((a = \frac{\pi}{2}) \land ((b = \frac{\pi}{2}) \land ((c = \frac{\pi}{2}) \land ((u = 0) \land (v = 0)))))) \Rightarrow (\exists R \in \mathbb{R},\; (R < C \cdot \operatorname{Defect}\left(a, b, c, u, v, w\right)) \land (\operatorname{Fits}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), p, R\right))))) \land (((a = \frac{\pi}{2}) \land ((b = \frac{\pi}{2}) \land ((c = \frac{\pi}{2}) \land ((u = 0) \land (v = 0))))) \Rightarrow (\forall z \in \operatorname{Fin}\left(4\right) \to S,\; \forall R \in \mathbb{R},\; (R < C \cdot \operatorname{Defect}\left(a, b, c, u, v, w\right)) \Rightarrow (\neg (\operatorname{Fits}\left(\operatorname{Chart}\left(a, b, c, u, v, w\right), z, R\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness.quarterLocal_angularRegion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Align the positive imaginary-part sum with I. Orthogonal projection onto its transverse plane has weighted mean zero. The pairwise weighted variance and the three-mode Parseval identity give the bound on the two transverse Fourier amplitudes. Conjugation transports the fit back to the original chart. Zero perturbation forces the three axial angles to equal pi over two and the two separations to vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness.quarterLocal_angularRegion`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionLocalSharpness.quarterLocal_strictFit`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalScorePerturbation](Reconstruction/RoundQuaternionLocalScorePerturbation.md)
