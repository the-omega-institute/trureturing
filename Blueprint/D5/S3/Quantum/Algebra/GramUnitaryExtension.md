# Equal Gram Unitary Extension

## Abstract

Equal complex column Gram matrices admit a unitary taking one rectangular matrix to the other.

**Theorem 1.1 (One unitary on the whole common codomain).**

$$\forall A,B: Matrix\left(m, n, Complex\right),\ gram\left(B\right) = gram\left(A\right) \implies\ \exists U: Unitary\left(m, Complex\right), B = U A$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq` (`✓ std3`). ∎

*Citation.* Sirui Lu and TNLean contributors (2026). *Gram equality and unitary extension for rectangular matrices*. URL: <https://github.com/LionSR/QICLean/blob/cdaa636d1f41560f7caca7077c11068229cb9727/QICLean/Algebra/MatrixGramUnitary.lean>.

*Commentary.*

Let m and n be finite types, and A and B complex m-by-n matrices. If their column Gram matrices A* A and B* B agree, with star denoting conjugate transpose, there is a unitary U on the full m-dimensional codomain such that B=UA. Gram equality identifies all linear dependencies among the columns. It defines an isometry between their ranges through the quotient by the kernel, and finite-dimensional isometry extension supplies U. Rank-deficient matrices and empty column types are included.

For continuous matrix fields, this theorem applies separately at each point. Its conclusion does not supply a continuous choice of the unitary. The distinction already has a maximal norm obstruction on the unit sphere S in R cubed. Fix any finite n at least one, write zeta(s,t,r)=s+i t, and set Z=zeta I and W=abs(zeta) I. Both fields have norm one and their column Gram fields agree. Every continuous unitary field u on S nevertheless has an equatorial point p with norm(u(p)Z(p)-W(p))=2.

To see this, parameterize the northern hemisphere by beta(z)=(Re z, Im z, sqrt(1-normSq(z))) on the closed complex unit disk. This map is continuous, including at its boundary. The determinant of u composed with beta gives a disk filling of the determinant loop along the equator; radial contraction gives that loop winding number zero. With a(t)=exp(2 pi i t) and c(t)=(Re a(t), Im a(t),0), the loop V(t)=a(t)u(c(t)) has determinant a(t) to the n-th power times det(u(c(t))). Multiplicativity of winding number therefore gives winding(det V)=n, which is nonzero.

If every V(t) avoided minus one in its spectrum, its principal argument would be a continuous selfadjoint matrix field. The homotopy exp(i(1-s)arg(V(t))) would contract V through unitaries, making its determinant winding number zero. Hence minus one occurs in the spectrum at some t. The unitary spectral norm criterion and the triangle bound then give norm(V(t)-I)=2, which is precisely the equatorial error above. This argument needs neither a continuous choice of eigenvectors or eigenvalues, nor differentiability, nor a restriction on the parity of n.

The spectral criterion and continuity of the principal-argument functional calculus are supplied by Mathlib.Analysis.CStarAlgebra.Unitary.Connected. The integer degree and its free homotopy and product laws are available in TauCetiProject/TauCeti, revision 1e668f5e55bc20f2eb87f4ba49b48833470290d1, TauCeti/Topology/Circle/Degree.lean. These standard results carry the argument; the application introduces no new winding invariant.

For the Alexandroff duplicate of S, pull Z and W back along its projection. A continuous global unitary restricts along the bottom inclusion to the same u, so the equatorial obstruction persists. This transport requires the actual duplicate topology, the continuous projection and bottom inclusion. The full duplicate-space properties, whole-space Gram identities, distances between orbit closures, and dense-top nonextension assertions are separate obligations. The local phase conj(zeta)/abs(zeta) is used only where zeta is nonzero; the two poles and their four duplicate points are never divided by their modulus.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/GramUnitaryExtension.exists_unitary_mul_eq_of_conjTranspose_mul_eq`
