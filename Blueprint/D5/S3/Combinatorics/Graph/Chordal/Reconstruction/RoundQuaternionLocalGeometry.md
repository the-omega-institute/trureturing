# Quarter-turn defect and score comparison

## Abstract

The triangle defect and the cyclic rim trace control the scaled cosine threshold near the quarter turn.

Let S denote the group of unit real quaternions. The map W is the transverse Fourier field of the three cyclic rim gains A, and QPair denotes the complex-pair quaternion embedding. The maximum absolute scalar perturbation is E. The quantity h is the maximum of the three scalar perturbations and the negative real part of the cyclic rim product. The radius e is the largest triangle defect of the hub-gauged assignment. The coefficient cStar is twice the sharp quarter-turn radius divided by pi.

**Theorem 1.1 (Exact face geometry in the hub gauge).**

$$\operatorname{GeometryLaws}\left(\operatorname{hubMaxDefect}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry.local_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The geometric laws use the coordinate identities for the complex pair and the cyclic phase, and the preservation of distances and scores by unitary conjugation. The maximum angle is the largest over the four faces. Cyclic rotation and reversal preserve each oriented triangle's angle, so a face realizing this maximum attains the defect in the directed definition.

**Theorem 1.2 (Exact triangle defect and its quantitative comparison).**

$$\forall A \in \operatorname{Fin}\left(3\right) \to S,\; \forall p \in \mathbb{C},\; \forall q \in \mathbb{C},\; \forall eta \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; \forall gamma \in \operatorname{Fin}\left(3\right) \to \mathbb{R},\; (\forall j \in \operatorname{Fin}\left(3\right),\; \operatorname{gain}\left(A, j\right) = \operatorname{QPair}\left((-\operatorname{val}\left(eta, j\right),\operatorname{val}\left(gamma, j\right)), \operatorname{W}\left(p, q, j\right)\right)) \Rightarrow ((\forall j \in \operatorname{Fin}\left(3\right),\; 0 < \operatorname{val}\left(gamma, j\right)) \Rightarrow ((\lvert p \rvert \leq \frac{3}{50}) \Rightarrow ((\lvert q \rvert \leq \frac{3}{50}) \Rightarrow ((\operatorname{E}\left(eta\right) \leq \frac{3}{50}) \Rightarrow ((\operatorname{e}\left(A\right) = \frac{\pi}{2}+\operatorname{arcsin}\left(\operatorname{h}\left(A, eta\right)\right)) \land ((\lvert \operatorname{h}\left(A, eta\right) \rvert < \frac{1}{5}) \land ((\frac{\operatorname{E}\left(eta\right)}{3}+\frac{\frac{51}{20} \cdot (\lvert p \rvert)^{2}}{6}-\frac{\frac{13}{5} \cdot (\lvert q \rvert)^{2}+25 \cdot (\frac{3}{50})^{2} \cdot \operatorname{E}\left(eta\right)}{3} \leq \operatorname{h}\left(A, eta\right)) \land (((0 \leq \operatorname{cStar} \cdot \operatorname{e}\left(A\right)) \land (\operatorname{cStar} \cdot \operatorname{e}\left(A\right) \leq \pi)) \land (\forall s \in \mathbb{R},\; (\frac{1}{\sqrt{3}}+\frac{\lvert q \rvert}{\sqrt{6}}-\frac{\sqrt{3}}{12} \cdot (\lvert p \rvert)^{2}-\frac{2}{5} \cdot (\lvert p \rvert)^{3}-3 \cdot (\lvert p \rvert)^{4}-\frac{627}{100} \cdot \frac{3}{50} \cdot \lvert q \rvert-2 \cdot \frac{3}{50} \cdot \operatorname{E}\left(eta\right) \leq s) \Rightarrow (\operatorname{cos}\left(\operatorname{cStar} \cdot \operatorname{e}\left(A\right)\right)+\frac{\lvert q \rvert}{200}+\frac{3}{100} \cdot ((\lvert p \rvert)^{2}+\operatorname{E}\left(eta\right)) \leq s))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry.local_defect_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three cyclic transverse areas equal the same constant times the difference of the squared Fourier amplitudes. Substituting those areas into the scalar part of the triple quaternion product gives the fourth face bound. Averaging that bound with the three spoke inequalities and using the scalar perturbation of largest absolute value gives the stated estimate for h. The strict concavity of the scaled cosine as a function of h bounds it by its tangent at zero. The rational Taylor bounds for the quarter-turn coefficient leave the displayed score margin.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry.local_defect_estimates`
- Truth anchor: `D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalGeometry.local_geometry`
- Dependency: [D5/S3/Combinatorics/Graph/Chordal/RoundQuaternionK4Bounds](../RoundQuaternionK4Bounds.md)
