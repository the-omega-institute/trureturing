# The actual defect family on a cycle

## Abstract

The actual Anderson defect family has scalar joint commutant and persistent nodal polynomial factors.

Let r and m be natural numbers, r at least three and m at least two. Put L=rm and q=(m-1)r+1. The sites are Fin L. The actual sign word U(i) is minus one exactly when i modulo r is zero or i=q, and is one otherwise. Delta is the ordinary cycleGraph L graph Laplacian, equal to 2I minus the cycle adjacency matrix. Put V=diag(U) and H(t)=Delta+tV. The pair in the commutant assertion is Delta,V.

Set T(d)=[[d,-1],[1,0]], a=2+t-lambda, b=2-t-lambda, B_r=T(a)^(r-1)T(b), and sigma_r=trace(B_r). The polynomial Psi_m(s) is the product of s-2cos(2 pi k/m) over integers k satisfying 0<k and 2k<m. Thus traceFactors is exactly Psi_m(sigma_r), with the strict inequality retained.

Write p_t for the actual characteristic polynomial of H(t), and q_t for that of its actual principal submatrix deleting site q. With phi:R[t] to R(t) the coefficient inclusion and T=phi(t), let g be the monic normalized gcd of p_T and q_T over R(t)[lambda]. In the display, p and q without coupling subscripts denote the original bivariate polynomials over R[t][lambda]. For any bivariate polynomial F, F_t means coefficientwise evaluation at the real coupling t. The symbol phi(F) denotes coefficientwise inclusion into R(t)[lambda].

**Theorem 1.1 (Scalar joint symmetries and persistent nodal factors).**

$$\forall (r : \mathbb{N}), \forall (m : \mathbb{N}), (3 \le r) \Rightarrow ((2 \le m) \Rightarrow ((\forall (X : \operatorname{Matrix}\left(\operatorname{Fin}\left(r \cdot m\right), \operatorname{Fin}\left(r \cdot m\right), \mathbb{C}\right)), (\operatorname{Commute}\left(X, \operatorname{complexify}\left(Delta\right)\right)) \Rightarrow ((\operatorname{Commute}\left(X, \operatorname{complexify}\left(V\right)\right)) \Rightarrow (\exists (c : \mathbb{C}), X = \operatorname{smul}\left(c, I\right)))) \land ((\forall (O : \operatorname{Matrix}\left(\operatorname{Fin}\left(r \cdot m\right), \operatorname{Fin}\left(r \cdot m\right), \mathbb{R}\right)), (\operatorname{Orthogonal}\left(O\right)) \Rightarrow ((\operatorname{Commute}\left(O, Delta\right)) \Rightarrow ((\operatorname{Commute}\left(O, V\right)) \Rightarrow ((O = I) \lor (O = -I))))) \land ((3 \le m) \Rightarrow ((\operatorname{bad}\left(\operatorname{U}\left(r, m\right)\right)) \land ((\forall (t : \mathbb{R}), \exists (mu : \mathbb{R}), \exists (z : \operatorname{Fin}\left(r \cdot m\right) \to \mathbb{R}), (z \ne 0) \land ((\operatorname{mulVec}\left(\operatorname{H}\left(t\right), z\right) = \operatorname{smul}\left(mu, z\right)) \land ((\operatorname{coordinate}\left(z, q\right) = 0) \land (\operatorname{coordinate}\left(z, q + 1\right) = 1)))) \land ((\operatorname{Monic}\left(g\right)) \land (\exists (G : \operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\mathbb{R}\right)\right)), (\operatorname{Monic}\left(G\right)) \land ((\operatorname{phi}\left(G\right) = g) \land ((\operatorname{Divides}\left(G, p\right)) \land ((\operatorname{Divides}\left(G, q_{q}\right)) \land ((\forall (t : \mathbb{R}), (\operatorname{Monic}\left(\operatorname{specialize}\left(G, t\right)\right)) \land ((\operatorname{Divides}\left(\operatorname{specialize}\left(G, t\right), \operatorname{p}\left(t\right)\right)) \land (\operatorname{Divides}\left(\operatorname{specialize}\left(G, t\right), \operatorname{minor}\left(t\right)\right)))) \land ((\exists (F : \operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\mathbb{R}\right)\right)), (\operatorname{Monic}\left(F\right)) \land ((0 < \operatorname{natDegree}\left(F\right)) \land (\operatorname{Divides}\left(F, G\right)))) \land (\forall (pi : \operatorname{Polynomial}\left(\operatorname{RatFunc}\left(\mathbb{R}\right)\right)), (\operatorname{Monic}\left(pi\right)) \Rightarrow ((\operatorname{Irreducible}\left(pi\right)) \Rightarrow ((\operatorname{Divides}\left(pi, \operatorname{Psi}\left(m, \operatorname{sigma}\left(r, T\right)\right)\right)) \Rightarrow ((\operatorname{Divides}\left(pi, g\right)) \land (\exists (F : \operatorname{Polynomial}\left(\operatorname{Polynomial}\left(\mathbb{R}\right)\right)), (\operatorname{Monic}\left(F\right)) \land ((\operatorname{phi}\left(F\right) = pi) \land ((\operatorname{Divides}\left(F, G\right)) \land (\forall (t : \mathbb{R}), (\operatorname{Monic}\left(\operatorname{specialize}\left(F, t\right)\right)) \land ((\operatorname{Divides}\left(\operatorname{specialize}\left(F, t\right), \operatorname{p}\left(t\right)\right)) \land (\operatorname{Divides}\left(\operatorname{specialize}\left(F, t\right), \operatorname{minor}\left(t\right)\right))))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/AndersonDefectFamily.defect_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two clauses hold for every m at least two. A complex matrix commuting with both Delta and V is scalar. A real orthogonal matrix commuting with both is I or minus I. These are common commutants of the pair, not commutants of an individual Hamiltonian.

For m at least three, badness is the original AndersonSymmetryConverseRefutation.bad predicate: at every real coupling, the conjunction of simple spectrum and nonvanishing of every nonzero eigenvector fails. The stronger displayed nodal assertion supplies a real eigenvalue and a nonzero real eigenvector at the same site q for every real t, normalized by z(q+1)=1. No nodal assertion is made for m=2.

The gcd g is monic and has a monic descent G over R[t][lambda]. This G has a monic divisor of positive degree, so the polynomial nodal factor is nonconstant. It divides both original bivariate characteristic polynomials and remains monic and a common divisor after every real specialization. Every monic irreducible pi dividing the actual trace product divides g; it also has a monic descent F dividing G. The specialization of F remains monic and divides both actual characteristic polynomials at every real t. No exceptional real coupling is removed.

The algebra proof starts from the actual negative-site projector (I-V)/2. Its adjacency compression has exactly the edge between p=(m-1)r and q=p+1; squaring gives E_pp+E_qq. The positive projector (I+V)/2 sends this pair into the two actual positive runs. Successively removing the preceding frontier yields the sum of their next diagonal units. The run preceding p has length r-1; the run following q has length r-2. At frontier r-1 only the former survives. Its negative neighbour gives an adjacent diagonal unit. The frozen cycle_diagonal_units_full theorem is then applied directly to these actual units; its propagation proof is reused.

For the nodal construction, periodic transport has block B_r and total monodromy B_r^m. The determinant-one two-by-two Chebyshev formula shows B_r^m=I at each trace value 2cos(2 pi k/m), with 0<2k<m. Choosing an initial state transported to (0,-1) at q produces z(q)=0 and z(q+1)=1. The defect changes a coefficient multiplying zero, so this is an eigenvector of the actual defect Hamiltonian, including the cyclic endpoint equations.

In an irreducible quotient field AdjoinRoot(pi), a root of the trace product yields this actual eigenvector. It is a root of both the actual characteristic polynomial and the actual deleted-site minor, proving the two divisibilities and hence divisibility by their monic gcd. Integrally closed monic descent and coefficient evaluation are supplied by pinned mathlib. At real couplings, the nonconstant complex discriminant attains an interior trace value; Hermitian spectral theory makes the eigenvalue real, and real parts preserve the normalized eigenvector.

The construction proves the stated family and factor inclusions. It makes no assertion of general-r irreducibility, equality of g with the trace product, squarefreeness, or a globally analytic eigenpair selection.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/AndersonDefectFamily.defect_family`
- Dependency: [D5/S0/Observation/MatrixTracePowerSum](../../../../S0/Observation/MatrixTracePowerSum.md)
- Dependency: [D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation](../AndersonSymmetryConverseRefutation.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/AndersonDefectSeed](AndersonDefectSeed.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CycleDiagonalUnitPropagation](CycleDiagonalUnitPropagation.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/CyclicTridiagonalTransferTrace](../../SpectralGraph/CyclicTridiagonalTransferTrace.md)
