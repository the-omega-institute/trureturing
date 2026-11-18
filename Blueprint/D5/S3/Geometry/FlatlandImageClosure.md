# FlatlandImageClosure

## Abstract

Two-camera image equations and their polynomial deformation argument.

**Definition 1.1 (Compatible).**

$$\forall (n : \mathbb{N}) , \forall (F : Matrix (Fin 3) (Fin 3) \mathbb{C}) , \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , (Compatible F p : Prop) = (\forall j , (p j 1) . rep \cdot_{v} (F *_{v} (p j 0) . rep) = 0)$$

*Formalization.* `D5/S3/Geometry/FlatlandImageClosure.Compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Each image pair satisfies the bilinear equation defined by the same matrix.

**Theorem 1.2 (singular_compatible_closure).**

$$\forall (n : \mathbb{N}) , \forall (F : Matrix (Fin 3) (Fin 3) \mathbb{C}) , (F \neq 0) \to (F . det = 0) \to \forall (p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C}))) , (Compatible F p) \to p \in imageClosure n$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageClosure.singular_compatible_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Every configuration compatible with a nonzero singular matrix belongs to the variable-camera closed image.

## References

- Truth anchor: `D5/S3/Geometry/FlatlandImageClosure.Compatible`
- Truth anchor: `D5/S3/Geometry/FlatlandImageClosure.singular_compatible_closure`
- Dependency: [D5/S3/Geometry/FlatlandImageAlgebra](FlatlandImageAlgebra.md)
