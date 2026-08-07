# Robertson-Schrodinger Identity

## Abstract

Centered vectors satisfy an exact Robertson-Schrodinger identity with a nonnegative Gram remainder.

**Theorem 1.1 (Centered vectors satisfy the Robertson-Schrodinger identity).**

$$\begin{gathered} \forall E: \operatorname{Type}^{*},\ [\operatorname{NormedAddCommGroup}(E)],\ [\operatorname{InnerProductSpace}(\mathbb{C},E)],\\ \forall A,B: E\to_{\mathbb{C}}E,\ \forall \psi\in E,\ \operatorname{IsSymmetric}(A) \land \operatorname{IsSymmetric}(B) \land \Vert \psi\Vert=1 \Rightarrow \\ (u:=A\psi-\langle \psi, A\psi\rangle_{\mathbb{C}}\cdot \psi) \land (v:=B\psi-\langle \psi, B\psi\rangle_{\mathbb{C}}\cdot \psi) \land \\ (\operatorname{Cov}:=\frac{1}{2}\cdot \operatorname{re}(\langle \psi, (AB+BA)\psi\rangle_{\mathbb{C}})-\operatorname{re}(\langle \psi, A\psi\rangle_{\mathbb{C}})\cdot\operatorname{re}(\langle \psi, B\psi\rangle_{\mathbb{C}})) \land \\ (c:=\frac{1}{2i}\langle \psi, (AB-BA)\psi\rangle_{\mathbb{C}}) \land \\ (G:=\Vert u\Vert^{2}\cdot \Vert v\Vert^{2}-\Vert\langle u, v\rangle_{\mathbb{C}}\Vert^{2}) \Rightarrow \\ \Vert u\Vert^{2}\cdot \Vert v\Vert^{2}=\operatorname{Cov}^{2}+\Vert c\Vert^{2}+G \land G \geq 0 \land \\ \operatorname{re}(\langle u, v\rangle_{\mathbb{C}})=\operatorname{Cov} \land \operatorname{ofReal}(\operatorname{im}(\langle u, v\rangle_{\mathbb{C}}))=c. \end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumBounds/RobertsonSchrodinger.robertson_schrodinger` (`✓ std3`). ∎

*Citation.* H. P. Robertson (1929). *The Uncertainty Principle*. DOI: [10.1103/PhysRev.34.163](https://doi.org/10.1103/PhysRev.34.163).

*Commentary.*

The parent declaration `gram_wedge_identity` applies to arbitrary vectors u and v in any normed additive commutative group with a complex inner-product-space structure. It defines G as the product of the squared norms minus the squared norm of the inner product, states the defining equality, and proves G nonnegative from mathlib's Cauchy-Schwarz theorem. It assumes no operators, symmetricity, distinguished vector, or normalization.

The adapter takes complex-linear symmetric operators A and B and a unit vector psi. Its centered vectors u and v have squared norms equal to the two variances. The real part of their inner product is the symmetric covariance Cov, while the complex coercion of the imaginary part is one over two i times the expectation of AB minus BA. Substitution into the parent identity gives the displayed equality with the same nonnegative G.

Robertson's 1929 relation retains the commutator lower bound, and Schrodinger's 1930 refinement additionally retains the symmetric covariance term. The exact equality here also retains the Gram remainder: discarding G recovers the strengthened lower bound, and discarding both G and the covariance contribution recovers the weaker bound. No finite-dimensional, completeness, spectral, or unbounded-operator domain theory is asserted.

## References

- Truth anchor: `D5/S3/QuantumBounds/RobertsonSchrodinger.robertson_schrodinger`
