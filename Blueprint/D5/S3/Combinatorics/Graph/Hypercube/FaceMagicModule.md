# The face-magic hypercube module

## Abstract

All-ring coordinates classify unrestricted face-magic hypercubes.

**Definition 1.1 (Common face sums).**

$$\forall R \in \operatorname{Type}, [\operatorname{Ring}(R)], \forall n \in Nat, \forall f \in (Finset\left(Fin\left(n\right)\right) \to R),\ (FaceMagic\left(R, n, f\right)) \iff (\exists C \in R,\ \forall S \in Finset\left(Fin\left(n\right)\right), \forall i \in Fin\left(n\right), \forall j \in Fin\left(n\right),\ (\neg(i \in S) \land \neg(j \in S) \land i \neq j) \Rightarrow f\left(S\right) + f\left(insert\left(i, S\right)\right) + f\left(insert\left(j, S\right)\right) + f\left(insert\left(i, insert\left(j, S\right)\right)\right) = C)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.FaceMagic` (`✓ std3`).

*Citation.* Manjul Bhargava (2026). *The existence and uniqueness of magic-faced hypercubes, and applications to Khajuraho most-perfect magic squares, cubes, and hypercubes*. URL: <https://arxiv.org/html/2609.26762v1>.

*Commentary.*

FaceMagic n f means that there is one C in the ring such that every two-coordinate face S, S∪{i}, S∪{j}, S∪{i,j}, with distinct i and j outside S, has sum C. The carrier is the actual function space of arrays admitting such a C; C is not stored in the carrier.

**Definition 1.2 (The face-magic submodule).**

$$\forall R \in \operatorname{Type}, [\operatorname{Ring}(R)], \forall n \in Nat, \forall f \in (Finset\left(Fin\left(n\right)\right) \to R),\ (f \in faceMagicModule\left(R, n\right)) \iff (\exists C \in R,\ \forall S \in Finset\left(Fin\left(n\right)\right), \forall i \in Fin\left(n\right), \forall j \in Fin\left(n\right),\ (\neg(i \in S) \land \neg(j \in S) \land i \neq j) \Rightarrow f\left(S\right) + f\left(insert\left(i, S\right)\right) + f\left(insert\left(j, S\right)\right) + f\left(insert\left(i, insert\left(j, S\right)\right)\right) = C)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.faceMagicModule` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Manjul Bhargava (2026). *The existence and uniqueness of magic-faced hypercubes, and applications to Khajuraho most-perfect magic squares, cubes, and hypercubes*. URL: <https://arxiv.org/html/2609.26762v1>.

*Commentary.*

The arrays satisfying the common-face condition form an R-submodule by adding witnesses and scaling a witness.

**Theorem 1.3 (All-ring coordinate classification).**

$$\forall R \in \operatorname{Type}, [\operatorname{Ring}(R)],\ (Nonempty\left(LinearEquiv\left(R, faceMagicModule\left(R, 0\right), R\right)\right) \land Nonempty\left(LinearEquiv\left(R, faceMagicModule\left(R, 1\right), Prod\left(R, R\right)\right)\right)) \land \forall n \in Nat,\ (2 \leq n \Rightarrow Nonempty\left(LinearEquiv\left(R, faceMagicModule\left(R, n\right), Prod\left(R, Prod\left(Fin\left(n\right) \to R, R\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure` (`✓ std3`). ∎

*Resolves.* `Problems/bhargava-2026-facemagic-module` (proved) by `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bhargava-2026-facemagic-module","declaration_gid":"D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Manjul Bhargava (2026). *The existence and uniqueness of magic-faced hypercubes, and applications to Khajuraho most-perfect magic squares, cubes, and hypercubes*. URL: <https://arxiv.org/html/2609.26762v1>.

*Commentary.*

The source question is: What is the structure of the R-module U_n(R) of face magic hypercubes of dimension n over R when the characteristic is even and positive? The theorem answers it over every unital ring. In dimension zero evaluation at the empty subset is an R-linear equivalence with R. In dimension one the empty and singleton entries give an equivalence with R × R. For n ≥ 2, evaluation at the empty subset, at each singleton, and on the fixed {0,1}-face gives an equivalence with R × (Fin n → R) × R. The inverse is the explicit integer-coordinate formula: for k = |S| it is (-1)^k ((1-k)a − Σ_{i∈S} b_i + floor(k/2) C), interpreted by additive integer coefficients. No division by two is used, so zero divisors and every characteristic are included. The face identity follows by the parity second difference of floor(k/2), and the inverse law follows by strong induction on the subset cardinality. Bhargava Section 2, equations (4), (8), (9) and Theorem 13 supply the face recurrence and induction method. The empty-entry, singleton-entry and common-face-sum coordinates instead give an integral reconstruction, avoiding the invertibility of two required by the source's determinant-two coordinates.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.FaceMagic`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.faceMagicModule`
- Truth anchor: `D5/S3/Combinatorics/Graph/Hypercube/FaceMagicModule.face_magic_module_structure`
