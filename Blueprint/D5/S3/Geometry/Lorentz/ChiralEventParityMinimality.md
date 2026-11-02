# A lower bound of three chiral-event variables

## Abstract

Any two continuous invariant parity-odd real variables vanish together on a chiral four-particle event in each of the two event classes.

**Definition 1.1 (Ordered four-particle events).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event} = \left((\operatorname{Fin}\left(4\right)) \to ((\operatorname{Fin}\left(4\right)) \to (\mathbb{R}))\right)$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.event` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

An event is an ordered quadruple of four-vectors, indexed in the order p, q, a, b. Each four-vector has type Fin 4 → ℝ, with coordinate zero the energy and coordinates one, two and three the spatial momentum, as in prelims.tex:21–23 of arXiv:2008.05206v6. The two interchangeable pairs are the first two and last two entries. The source's two event classes and their common symmetry group are specified in prelims.tex:656–666. The ambient type itself imposes no forward-cone or collision condition.

**Definition 1.2 (The Minkowski metric matrix).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.eta} = \operatorname{Matrix.diagonal}\left(![1, -(1), -(1), -(1)]\right)$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.eta` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The diagonal matrix has signature (+,−,−,−), the convention of the source's Minkowski product. It also represents spatial parity on a four-vector.

**Definition 1.3 (A proper spatial rotation).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.rotation} = !![1, 0, 0, 0; 0, 0, -(1), 0; 0, -(1), 0, 0; 0, 0, 0, -(1)]$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.rotation` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The matrix fixes time and sends the spatial coordinates (x,y,z) to (−y,−x,−z). It preserves the Minkowski metric, has determinant one and has time-time entry one. Composing it with parity exchanges the first two spatial coordinates.

**Definition 1.4 (The Minkowski product).**

$$\forall (x: (\operatorname{Fin}\left(4\right)) \to (\mathbb{R})), (\forall (y: (\operatorname{Fin}\left(4\right)) \to (\mathbb{R})), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.minkowski}\left(x, y\right) = ((((x\left(0\right)) \cdot (y\left(0\right))) - ((x\left(1\right)) \cdot (y\left(1\right)))) - ((x\left(2\right)) \cdot (y\left(2\right)))) - ((x\left(3\right)) \cdot (y\left(3\right)))))$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.minkowski` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The bilinear product multiplies the time coordinates and subtracts the three spatial coordinate products. The collision condition in prelims.tex:433–443 uses this product and its associated squared masses.

**Definition 1.5 (Forward nonspacelike four-vectors).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.forwardCone} = \{x: (\operatorname{Fin}\left(4\right)) \to (\mathbb{R}) \mid (0 \le x\left(0\right)) \land ((((x\left(1\right))^{2}) + ((x\left(2\right))^{2})) + ((x\left(3\right))^{2}) \le (x\left(0\right))^{2})\}$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.forwardCone` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The time coordinate is nonnegative and its square bounds the squared spatial norm. Thus the zero vector and future null vectors are included, as in the set of four-vectors defined in prelims.tex:25–27.

**Definition 1.6 (Proper orthochronous Lorentz matrices).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.properOrthochronous} = \{lam: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{R}\right) \mid (((\operatorname{Matrix.transpose}\left(lam\right)) \cdot (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.eta})) \cdot (lam) = \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.eta}) \land ((\operatorname{Matrix.det}\left(lam\right) = 1) \land (0 < lam\left(0, 0\right)))\}$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.properOrthochronous` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The matrix preserves eta, has determinant one and has positive time-time entry. These conditions express the proper orthochronous Lorentz transformations used in the symmetry group of prelims.tex:190–193.

**Definition 1.7 (Parity of a four-vector).**

$$\forall (x: (\operatorname{Fin}\left(4\right)) \to (\mathbb{R})), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parityVector}\left(x\right) = ![x\left(0\right), -(x\left(1\right)), -(x\left(2\right)), -(x\left(3\right))])$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.parityVector` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

Parity fixes energy and negates all three spatial coordinates, as in prelims.tex:228–238.

**Definition 1.8 (Parity of an event).**

$$\forall (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parity}\left(x\right) = ![\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parityVector}\left(x\left(0\right)\right), \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parityVector}\left(x\left(1\right)\right), \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parityVector}\left(x\left(2\right)\right), \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parityVector}\left(x\left(3\right)\right)])$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.parity` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

Apply four-vector parity to each of the four event entries. This is the componentwise event parity of prelims.tex:228–238.

**Definition 1.9 (Lorentz transformations and pair permutations).**

$$\forall (lam: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{R}\right)), (\forall (sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), (\forall (tau: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), (\forall (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.act}\left(lam, sigma, tau, x\right) = ![\operatorname{Matrix.mulVec}\left(lam, x\left(\operatorname{Fin.castAdd}\left(2, sigma\left(0\right)\right)\right)\right), \operatorname{Matrix.mulVec}\left(lam, x\left(\operatorname{Fin.castAdd}\left(2, sigma\left(1\right)\right)\right)\right), \operatorname{Matrix.mulVec}\left(lam, x\left(\operatorname{Fin.natAdd}\left(2, tau\left(0\right)\right)\right)\right), \operatorname{Matrix.mulVec}\left(lam, x\left(\operatorname{Fin.natAdd}\left(2, tau\left(1\right)\right)\right)\right)]))))$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.act` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The permutation sigma selects entries within the p,q pair and tau selects entries within the a,b pair; the same matrix lam then acts on every selected four-vector. Fin.castAdd embeds the first pair's indices into Fin 4, while Fin.natAdd shifts the second pair's indices by two. The formula defines the action for every real matrix; membership in the Lorentz group is required where the symmetry is used. This is the action described in prelims.tex:190–193 and 260–267.

**Definition 1.10 (Chiral events).**

$$\forall (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.chiral}\left(x\right)) \Leftrightarrow (\neg (\exists (lam: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{R}\right)), ((lam \in \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.properOrthochronous}) \land (\exists (sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), (\exists (tau: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.act}\left(lam, sigma, tau, x\right) = \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parity}\left(x\right))))))))$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.chiral` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

An event is chiral if no proper orthochronous Lorentz matrix and no independent pair permutations carry it to its parity image. This is the characterization in prelims.tex:240–243 and 265–268, extended as a predicate on the ambient event type.

**Definition 1.11 (The full forward-cone event class).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.allEvents} = \{x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event} \mid \forall (i: \operatorname{Fin}\left(4\right)), (x\left(i\right) \in \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.forwardCone})\}$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.allEvents` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

Every one of the four entries belongs to the forward cone. With the common pair-permutation and Lorentz symmetries, this is the class of all (pq)(ab) events in prelims.tex:662–666. There is no additional momentum-conservation constraint.

**Definition 1.12 (The collision event class).**

$$\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.collisionEvents} = \{x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event} \mid (x \in \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.allEvents}) \land ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.minkowski}\left(x\left(0\right), x\left(0\right)\right)) \cdot (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.minkowski}\left(x\left(1\right), x\left(1\right)\right)) < (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.minkowski}\left(x\left(0\right), x\left(1\right)\right))^{2})\}$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.collisionEvents` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

A collision event is a forward-cone event for which the product of the squared masses of p and q is strictly less than the square of their Minkowski product. This is the collision condition of prelims.tex:433–443 and the class (pq) to (ab) plus X in prelims.tex:656–660.

**Definition 1.13 (Continuous invariant parity-odd variables).**

$$\forall (om: \operatorname{Set}\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}\right)), (\forall (f: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})), ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.admissible}\left(om, f\right)) \Leftrightarrow ((\operatorname{ContinuousOn}\left(f, om\right)) \land ((\forall (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), ((x \in om) \Rightarrow (\forall (lam: \operatorname{Matrix}\left(\operatorname{Fin}\left(4\right), \operatorname{Fin}\left(4\right), \mathbb{R}\right)), ((lam \in \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.properOrthochronous}) \Rightarrow (\forall (sigma: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), (\forall (tau: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), (f\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.act}\left(lam, sigma, tau, x\right)\right) = f\left(x\right)))))))) \land (\forall (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), ((x \in om) \Rightarrow (f\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parity}\left(x\right)\right) = -(f\left(x\right)))))))))$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.admissible` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

The variable is real-valued, continuous on om, invariant under every allowed Lorentz matrix and both pair permutations at every event in om, and parity odd there. These are the first four requirements in goals.tex:1–10. No continuity or symmetry condition is imposed outside om.

**Definition 1.14 (The two-variable obstruction).**

$$(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.claim}) \Leftrightarrow (\forall (om: \operatorname{Set}\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}\right)), ((om \in \left\{\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.allEvents}, \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.collisionEvents}\right\}) \Rightarrow (\forall (f_{1}: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})), (\forall (f_{2}: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})), ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.admissible}\left(om, f_{1}\right)) \Rightarrow ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.admissible}\left(om, f_{2}\right)) \Rightarrow (\exists (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), ((x \in om) \land ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.chiral}\left(x\right)) \land ((\left(f_{1}\right)\left(x\right) = 0) \land (\left(f_{2}\right)\left(x\right) = 0)))))))))))$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.claim` (`✓ std3`).

*Citation.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

For each of the full and collision event classes, any two admissible real variables vanish together at some chiral event. This expresses the lower-bound assertion of the minimality conjecture in introduction.tex:103–104: neither one nor two such variables can be sufficient. The one-variable case follows by taking both variables equal. The statement supplies no construction or sufficiency proof for a three-variable set.

**Definition 1.15 (A sphere of four-particle events).**

$$\forall (v: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.family}\left(v\right) = \operatorname{let} (s: \mathbb{R}) := v\left(0\right) \operatorname{in} (\operatorname{let} (t: \mathbb{R}) := v\left(1\right) \operatorname{in} (\operatorname{let} (d: \mathbb{R}) := v\left(2\right) \operatorname{in} (\operatorname{let} (aa: \mathbb{R}) := \operatorname{Real.sqrt}\left((4) + (t)\right) \operatorname{in} (\operatorname{let} (bb: \mathbb{R}) := \operatorname{Real.sqrt}\left((4) - (t)\right) \operatorname{in} (![![30, 0, 0, 1], ![20, 0, 0, -(1)], ![(10) + (s), aa, 0, d], ![(10) - (s), 0, bb, -(d)]]))))))$$

*Formalization.* `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.family` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

For v on the unit sphere, write s, t and d for its three real coordinates and aa and bb for the indicated positive square roots. The first two momenta are fixed; the final two encode the sphere coordinates in their energies, transverse lengths and opposite longitudinal coordinates. The formula is defined on all of Euclidean three-space; its collision membership and chirality are used on the unit sphere.

**Theorem 1.16 (A common zero on a chiral event).**

$$\forall (om: \operatorname{Set}\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}\right)), ((om \in \left\{\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.allEvents}, \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.collisionEvents}\right\}) \Rightarrow (\forall (f_{1}: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})), (\forall (f_{2}: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})), ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.admissible}\left(om, f_{1}\right)) \Rightarrow ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.admissible}\left(om, f_{2}\right)) \Rightarrow (\exists (x: \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}), ((x \in om) \land ((\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.chiral}\left(x\right)) \land ((\left(f_{1}\right)\left(x\right) = 0) \land (\left(f_{2}\right)\left(x\right) = 0))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christopher G. Lester; Ward Haddadin; Ben Gripaios (2022). *Lorentz and permutation invariants of particles III: constraining non-standard sources of parity violation*. DOI: [10.1142/S0217751X22500932](https://doi.org/10.1142/S0217751X22500932). URL: <https://arxiv.org/abs/2008.05206v6>.

*Commentary.*

First consider the displayed family on the unit sphere. Its coordinates satisfy s² + t² + d² = 1, so s and t lie between minus one and one. The squared transverse lengths are 4+t and 4−t. Both energies 10+s and 10−s are positive, and the squared masses of the last two momenta are 95+20s+2s²−t+t² and 95−20s+2s²+t+t², each at least 74. All four momenta therefore lie in the forward cone. The first two squared masses are 899 and 399 and their Minkowski product is 601; 899 times 399 is strictly less than 601 squared. Every event of the sphere is consequently a collision event. Each coordinate depends continuously on v, including the square roots, so the family is continuous.

To establish chirality, suppose an allowed matrix lam and pair permutations carry such an event to its parity image. First let sigma fix the first pair and put h = eta times lam. Then h preserves eta, fixes p and q, and has determinant minus one. The two fixed vectors span the time-longitudinal plane. Solving their coordinate equations and using preservation of eta shows that h fixes this plane pointwise and has no mixed entries with the transverse plane. If tau fixes the second pair, h fixes the two nonzero independent transverse vectors (aa,0) and (0,bb). Its remaining block is the identity, so h is the identity, contradicting its determinant. If tau exchanges the second pair, the time and longitudinal coordinates give s = d = 0. Preservation of the Minkowski squared norm gives aa = bb; their squared values then give t = 0, contradicting the unit-sphere equation. Finally, if sigma exchanges p and q, preservation of their squared norms would equate 899 and 399. This rules out every pair of permutations.

Direct coordinate comparison gives the antipodal identity below: rotation, together with exchange of the last pair, carries the parity image of the event at v to the event at −v.

$$
\forall (v: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.family}\left(-(v)\right) = \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.act}\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.rotation}, (1: \operatorname{Equiv.Perm}\left(\operatorname{Fin}\left(2\right)\right)), \operatorname{Equiv.swap}\left((0: \operatorname{Fin}\left(2\right)), (1: \operatorname{Fin}\left(2\right))\right), \operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.parity}\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.family}\left(v\right)\right)\right))
$$

Whenever collisionEvents is contained in om, composing either admissible variable with the family is continuous on the sphere. The closed expression below sends each pair of real variables to its complex-valued pullback. For admissible variables this pullback is continuous on the sphere. Parity preserves the forward cone and the collision inequality, hence preserves both event domains. The displayed rotation preserves eta, has determinant one and has positive time-time entry; its determinant follows by writing it as the spatial coordinate exchange times eta. Invariance applied at the parity image, followed by parity oddness and the antipodal identity, makes each real pullback odd. The same holds after the explicit inclusions into the complex numbers, so their displayed complex combination is odd.

$$
\lambda (f_{1}: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})) \mapsto (\lambda (f_{2}: (\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.event}) \to (\mathbb{R})) \mapsto (\lambda (v: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)) \mapsto ((\operatorname{Complex.ofReal}\left(\left(f_{1}\right)\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.family}\left(v\right)\right)\right)) + ((\operatorname{Complex.ofReal}\left(\left(f_{2}\right)\left(\operatorname{D5.S3.Geometry.Lorentz.ChiralEventParityMinimality.family}\left(v\right)\right)\right)) \cdot (\operatorname{Complex.I})))))
$$

For om equal to allEvents, use the inclusion of collisionEvents into allEvents. Apply the planar odd-map zero theorem, Borsuk's Satz II (1933) for n=2, reviewed in Library note D5/L/Topology/borsuk1933spheres, to the complex combination and obtain a unit vector where it vanishes. The family event there is in om and is chiral; taking real and imaginary parts gives f₁ = f₂ = 0. For om equal to collisionEvents, use the identity inclusion and repeat the same argument. These are the two possibilities for om, which proves the full assertion.

## References

- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.act`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.admissible`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.allEvents`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.chiral`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.claim`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.collisionEvents`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.eta`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.event`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.family`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.forwardCone`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.minkowski`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.parity`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.parityVector`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.properOrthochronous`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.result`
- Truth anchor: `D5/S3/Geometry/Lorentz/ChiralEventParityMinimality.rotation`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/SerialEndpointPairing](../../Combinatorics/PerfectMatchings/SerialEndpointPairing.md)
