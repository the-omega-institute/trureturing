# The Borsuk-Ulam theorem in dimensions at most two

## Abstract

A map from the unit sphere of R^(d+1) to R^d that is continuous on the sphere takes equal values at some pair of antipodal points when d <= 2; consequently, for d <= 2 and d < m, no map from R^m to R^d is continuous and injective on a nonempty open set.

**Theorem 1.1 (Antipodal coincidence in dimensions at most two).**

$$\forall d: \mathbb{N}, d \leq 2 \Rightarrow \forall f: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d + 1\right)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \operatorname{ContinuousOn}\left(f, \operatorname{sphere}\left(0, 1\right)\right) \Rightarrow \exists x \in \operatorname{sphere}\left(0, 1\right), f\left(x\right) = f\left(-x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LowDimensionalBorsukUlam.exists_eq_neg_of_le_two` (`✓ std3`). ∎

*Citation.* Karol Borsuk (1933). *Drei Sätze über die n-dimensionale euklidische Sphäre*. DOI: [10.4064/fm-20-1-177-190](https://doi.org/10.4064/fm-20-1-177-190). URL: <https://matwbn.icm.edu.pl/ksiazki/fm/fm20/fm20117.pdf>.

*Commentary.*

Let d <= 2 and let f be a map from Euclidean space of dimension d + 1 to Euclidean space of dimension d that is continuous on the unit sphere. Then f x = f (-x) for some point x of the unit sphere. This is Borsuk's Satz II, the classical Borsuk-Ulam theorem, in the cases d <= 2 (Satz II for the d-dimensional sphere); the theorem for general d is not stated here, and it is not available in the underlying formal library. For d = 0 the target is a single point. For d = 1 the function g x = f x - f (-x) with values in the real line is continuous on the unit circle and odd, g (-x) = -g x, so it takes a value of each sign at the antipodal points of a fixed point; since the circle is connected, the intermediate value theorem gives a zero of g. For d = 2 the plane is identified isometrically with the complex numbers, and the map x -> f x - f (-x) becomes a continuous odd complex-valued map on the unit sphere of three-space; such a map has a zero, which is the required point.

**Theorem 1.2 (No continuous injection of an open set into a lower dimension at most two).**

$$\forall m, d: \mathbb{N}, d \leq 2 \Rightarrow d < m \Rightarrow \forall U: \operatorname{Set}\left(\operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right)\right), \operatorname{IsOpen}\left(U\right) \Rightarrow \operatorname{Nonempty}\left(U\right) \Rightarrow \forall f: \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(m\right)\right) \to \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(d\right)\right), \operatorname{ContinuousOn}\left(f, U\right) \Rightarrow \neg \operatorname{InjOn}\left(f, U\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/LowDimensionalBorsukUlam.not_injOn_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d <= 2 and d < m, let U be a nonempty open subset of Euclidean space of dimension m, and let f be a map from Euclidean space of dimension m to Euclidean space of dimension d that is continuous on U. Then f is not injective on U. This is the classical consequence of invariance of domain that a nonempty open subset of Euclidean space of dimension m admits no continuous injection into Euclidean space of dimension d < m, here only for d <= 2; invariance of domain itself, the openness of the image of a continuous injection between open subsets of the same Euclidean space, is not stated. Choose a point p of U and a radius r with the ball of radius r about p contained in U. Write m = d + 1 + k and embed Euclidean space of dimension d + 1 isometrically as the first d + 1 coordinates; scaling the unit sphere of dimension d by a positive factor t smaller than r and translating it to p gives a sphere y -> p + t y inside U. The composition of f with this map is continuous on the unit sphere of dimension d, so it takes equal values at some antipodal pair x and -x. Injectivity of f on U would give p + t x = p - t x, hence x = 0, which is not a point of the unit sphere.

## References

- Truth anchor: `D5/S3/Topology/LowDimensionalBorsukUlam.exists_eq_neg_of_le_two`
- Truth anchor: `D5/S3/Topology/LowDimensionalBorsukUlam.not_injOn_of_lt`
- Dependency: [D5/S3/Geometry/Lorentz/ChiralEventParityMinimality](../Geometry/Lorentz/ChiralEventParityMinimality.md)
