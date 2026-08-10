# Eisenstein Discriminant Representations

## Abstract

Forms in V at discriminant 4k are in bijection with the Eisenstein representations of k.

**Theorem 1.1 (Forms at discriminant 4k biject with Eisenstein representations).**

$$\left\{(A,B,C)\in\mathbb{Z}^{3}\mid B=-2(A+C), B^{2}-4AC=4k\}\right \to \left\{(A,C)\in\mathbb{Z}^{2}\mid A^{2}+AC+C^{2}=k\}\right,\quad(A,B,C)\mapsto(A,C)\quad\text{ is bijective}.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/EisensteinDiscriminant.forms_biject_eisenstein_representations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each integer k, a binary quadratic form with coefficients A, B, C lies in V when B = -2(A + C). Under that constraint its discriminant equals 4k exactly when A^2 + AC + C^2 = k. The coefficient projection sending the form to (A, C) is bijective, with inverse (A, C) |-> (A, -2(A + C), C). Thus the V-form incidence total and the Eisenstein representation number are identified by an explicit bijection, rather than only by a numerical equality.

## References

- Truth anchor: `D5/S3/PrimeForms/EisensteinDiscriminant.forms_biject_eisenstein_representations`
