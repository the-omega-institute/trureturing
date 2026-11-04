# The first characteristic coefficient separating the actual Cayley graphs

## Abstract

The actual same-group Cayley graphs have a first characteristic coefficient difference fixed by their first return moment defect.

**Theorem 1.1 (Equal coefficients before the return threshold and exact negative defect at the threshold).**

Lean statement: `D5/S3/FiniteGroups/BajnokBeattyFirstCharacteristicDefect.first_characteristic_defect`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/BajnokBeattyFirstCharacteristicDefect.first_characteristic_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* B. Bajnok and W. K. Beatty (2024). *On the Diameter of Undirected Cayley Graphs of Finite Abelian Groups*. URL: <https://arxiv.org/abs/2406.04045v1>.

*Commentary.*

Let p,t be integers with p>=3 odd and t>=2. No primality assumption is imposed, so composite odd p are included. Put m=6t-1, D=(m^2-9)/2=(3t+1)(6t-4), H=Z/pZ x Z/(pD)Z, N=p^2D, and n=p(m-3)=p(6t-4). In Lean the moduli are natAbs and n is toNat; positivity of the displayed parameters identifies these with the positive integer values. The result constructs the finite vertex type and proves |H|=N and 0<n<=|H|.

Use the actual additive maps q19(x,y)=(-x+y,-3tx+(3t-1)y) and q33(x,y)=(tx+(1-t)y,-(3t+1)x+(3t-2)y), with coordinates reduced modulo p and pD. For each map q the graph is graph(q), the undirected simple Cayley graph for {q(1,0),-q(1,0),q(0,1),-q(0,1)} on this same H. Let A19 and A33 be precisely the complex adjacency matrices of these two graphs. These matrices are defined in the theorem, rather than supplied as arbitrary matrices. Their Hermitian proofs come from Mathlib's isAdjMatrix_adjMatrix followed by Matrix.IsAdjMatrix.isHermitian.

The input BajnokBeattyCayleyReturnMoments.first_return_moment_defect supplies |H|=N, equality of all shorter rooted closed-walk counts and traces, and trace(A33^n)-trace(A19^n)=2N. This is the graph theorem for those exact coordinate maps. Its return words are transported from the lattice quotient by the actual coordinate equivalences and identified with simple-graph walks after proving the four steps distinct and nonzero. The characteristic theorem adds no trace, count, kernel, step-separation, or spectrum assumptions.

Define c19(j)=charpoly(A19).coeff(N-j) and c33(j)=charpoly(A33).coeff(N-j), where j=0 is the leading coefficient. The coefficient result is c19(j)=c33(j) for every natural j<n and c33(n)-c19(n)=-2p(3t+1), interpreted as the integer embedded in the complex numbers. Consequently the first differing degree when reading the characteristic polynomials downward from their monic term is N-n. The defect is nonzero because p>=3 and t>=2, so their characteristic polynomials are distinct.

The generic MatrixFirstMomentCoefficientBridge is consumed here with these actual adjacency matrices. It uses Mathlib's unitary spectral theorem and Vieta formula to derive the elementary-symmetric Newton recurrence for actual characteristic coefficients. Subtracting the two recurrences at the first unequal moment gives n(c33(n)-c19(n))=-(trace(A33^n)-trace(A19^n))=-2N. All earlier terms cancel, and the leading coefficient contributes one. The negative sign comes from the signed characteristic-polynomial Newton recurrence, not from the parity of n. The parameter identity D=(3t+1)(m-3) gives N=n p(3t+1), hence N/n=p(3t+1) and the asserted gap.

Translation of H acts on each Cayley graph and makes the rooted return counts independent of the root. At length n the (3,3) graph gains exactly two oriented horizontal wrapping returns at each vertex: the constant positive-horizontal and negative-horizontal words from the first-return theorem. The trace sums these rooted counts, so the defect is 2N. Newton's coefficient comparison divides by the length n, producing the factor N/n. This gives a group-action interpretation of the return-count theorem and the factor N/n. Exact orbit orders and isometric-cycle claims are not separately formalized here; no spectral classification is required.

For the boundary case p=3,t=2, D=56, N=504 and n=24, so the first differing polynomial degree is 480 and c33(24)-c19(24)=-42. For p=5,t=2 it is degree 1360 with gap -70; for the composite case p=9,t=2 it is degree 4464 with gap -126. Transient full-telescope Lean applications verify these three specializations directly from the symbolic theorem, without enumerating matrices or words. The general assertion rests on the exact graph/moment supplier and the matrix coefficient derivation.

Bajnok-Beatty arXiv:2406.04045v1 provides the Cayley-diameter setting through the cited repository Library note. The coefficient comparison is a repository consequence of the earlier return and graph-moment argument using standard spectral, Newton, and Vieta results. No literature novelty or completed spectral classification is claimed. This increment records characteristic-polynomial inequality; it does not add a separate formal graph-isomorphism obstruction.

## References

- Truth anchor: `D5/S3/FiniteGroups/BajnokBeattyFirstCharacteristicDefect.first_characteristic_defect`
- Dependency: [D5/S0/Observation/MatrixFirstMomentCoefficientBridge](../../S0/Observation/MatrixFirstMomentCoefficientBridge.md)
- Dependency: [D5/S3/FiniteGroups/BajnokBeattyCayleyReturnMoments](BajnokBeattyCayleyReturnMoments.md)
