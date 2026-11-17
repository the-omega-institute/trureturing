# FlatlandImageEquations

## Abstract

Two-camera image equations and their polynomial deformation argument.

**Definition 1.1 (claim).**

$$claim \iff (\forall n : \mathbb{N} , 9 \leq n \to \forall p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C})) , p \in imageClosure n \iff equations p)$$

*Formalization.* `D5/S3/Geometry/FlatlandImageEquations.claim` (`✓ std3`).

*Citation.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

Example 4.6, page 15: “A natural question arises: for $n>8$, do the $8$-point constraints in Equation (38) and the Segre-determinantal minors suffice to give equations for $\overline{\operatorname{Im}\theta_{3,(2,2),n}}$?”

“To make this more concrete, we may pose the problem of finding the following descriptions of the ideal of the image variety, in increasing order of difficulty: local equations, set-theoretic equations, scheme-theoretic equations, generators of the vanishing ideal, and/or (universal) Gröbner bases.”

The set-theoretic question in Example 4.6, page 15, for every natural number at least nine. The field is complex, both cameras vary, and closed image is expressed by multihomogeneous vanishing.

**Theorem 1.2 (result).**

$$\forall n : \mathbb{N} , 9 \leq n \to \forall p : (Fin n \to Fin 2 \to Projectivization \mathbb{C} (Fin 3 \to \mathbb{C})) , p \in imageClosure n \iff equations p$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FlatlandImageEquations.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-adk2606ex46` (proved) by `D5/S3/Geometry/FlatlandImageEquations.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-adk2606ex46","declaration_gid":"D5/S3/Geometry/FlatlandImageEquations.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Colin Alstad, Timothy Duff, Mordechai Katzman (2026). *Segre-Determinantal Loci and the Image Variety for Three Flatland Cameras*. DOI: [10.48550/arXiv.2606.31965](https://doi.org/10.48550/arXiv.2606.31965). URL: <https://arxiv.org/abs/2606.31965v1>.

*Commentary.*

The nine-row Segre minors and the eight-point constraints cut out exactly the variable-camera closed image for every natural number at least nine.

## References

- Truth anchor: `D5/S3/Geometry/FlatlandImageEquations.claim`
- Truth anchor: `D5/S3/Geometry/FlatlandImageEquations.result`
- Dependency: [D5/S3/Arith/Lattices/CofactorKernel](../Arith/Lattices/CofactorKernel.md)
- Dependency: [D5/S3/Geometry/FlatlandImageAlgebra](FlatlandImageAlgebra.md)
- Dependency: [D5/S3/Geometry/FlatlandImageClosure](FlatlandImageClosure.md)
