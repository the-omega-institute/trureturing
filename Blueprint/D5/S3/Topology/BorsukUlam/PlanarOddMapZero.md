# The planar odd-map zero theorem

## Abstract

A continuous odd complex-valued map on the unit sphere in real three-space has a zero.

**Theorem 1.1 (A zero of an odd map on the two-sphere).**

$$\forall (f: (\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)) \to (\mathbb{C})), ((\operatorname{ContinuousOn}\left(f, \operatorname{Metric.sphere}\left((0: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (1: \mathbb{R})\right)\right)) \Rightarrow ((\forall (v: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), ((v \in \operatorname{Metric.sphere}\left((0: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (1: \mathbb{R})\right)) \Rightarrow (f\left(-(v)\right) = -(f\left(v\right))))) \Rightarrow (\exists (v: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), ((v \in \operatorname{Metric.sphere}\left((0: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(3\right)\right)), (1: \mathbb{R})\right)) \land (f\left(v\right) = (0: \mathbb{C}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BorsukUlam/PlanarOddMapZero.planar_odd_map_zero` (`✓ std3`). ∎

*Citation.* Karol Borsuk (1933). *Drei Sätze über die n-dimensionale euklidische Sphäre*. DOI: [10.4064/fm-20-1-177-190](https://doi.org/10.4064/fm-20-1-177-190). URL: <https://matwbn.icm.edu.pl/ksiazki/fm/fm20/fm20117.pdf>.

*Commentary.*

This is Borsuk's Satz II (1933) for n=2 applied to an odd map, identifying the target plane with the complex numbers, proved here from the covering-space lift. The function f is defined on the whole ambient Euclidean space, but continuity and oddness are required only on its unit sphere. No restriction on f away from the sphere is used.

Suppose f has no zero on the sphere. Let D be the closed unit disk in the complex plane. It is a nonempty convex set, hence contractible and locally path connected. Send a disk point z to the upper half of the sphere by the vector with coordinates Re(z), Im(z) and the nonnegative square root of 1−‖z‖². The disk inequality makes the square root's argument nonnegative, and the sum of the coordinate squares is one. This map is continuous, and on the boundary its values at −z and z are negatives of one another.

Compose f with this map to the sphere to obtain a continuous nonvanishing complex function q on D. Normalize it by q(z) divided by Complex.ofReal(‖q(z)‖), obtaining a continuous circle-valued map g. Choose a real argument for g at the disk's center. The covering map Circle.exp then lifts g to a continuous real-valued map F on the contractible disk, with that chosen central value. On the boundary circle write l(z) = F(z), using the boundary inclusion into D. Then l is continuous and Circle.exp(l(z)) = g(z).

Oddness of f and the antipodal identity on the boundary give g(−z) = −g(z). Thus the continuous real function delta(z) = l(−z)−l(z) has exponential constantly equal to minus one. A continuous map from the connected circle into a single fiber of this covering is constant, so delta(−1) = delta(1). The definition also gives delta(−1) = −delta(1), forcing delta(1) = 0. Its exponential is therefore one as well as minus one, a contradiction. Hence f vanishes at some point of the unit sphere.

## References

- Truth anchor: `D5/S3/Topology/BorsukUlam/PlanarOddMapZero.planar_odd_map_zero`
