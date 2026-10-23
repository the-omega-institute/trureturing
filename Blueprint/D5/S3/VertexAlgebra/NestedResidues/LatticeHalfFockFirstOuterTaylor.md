# LatticeHalfFockFirstOuterTaylor

## Abstract

The original current/source fused Taylor equality.

**Theorem 1.1 (The full original actual fused equality).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor.fused_weighted_identity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor.fused_weighted_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

Fix the original lattice data, actual tensor x, covector phi, states a,b, signed gamma,delta,d,r,n and arbitrary supplied natural K. Let J be the actual current, A and B the original slices, Ad the slice of neutralMode(i,d,a), L=frequencyBound(a)+1, M=frequencyBound(b)+1 and degree=L+M+K-d-r-2. The finite Laurent numerator P satisfies the original universal homogeneous six-order coefficient equation; every integer numerator exponent is retained.

For every genuine whole-field locality order H1 of Ad,B, the actual coefficient phi(Q_r^(gamma+1)(Ad,B;H1)[n] x) equals the sum over u<(degree+1).toNat of collisionTaylor(P,gamma,u,(degree-u).toNat) times fusedResidueWeight(u-M,d-L). The complete original telescope also retains the independent middle and reverse locality families H2,H3. These families need no extra restriction for this first equality.

For d<L put t=(L-d-1).toNat and C=M+K+t. The actual homogeneous quotient supplies both the original current/source readout and its whole-field completion. Completion pads H1 to max(H1,C). A rational pole bound alone does not identify an arbitrary truncated finite product with its complete residue.

The local J/A Laurent residue is expanded before choosing either remaining order. Relabelling the surviving original labels A,B as the two labels of the binary evaluator preserves both Hahn coefficient maps. Its finite terms have numerator exponents (e(0)+e(1)-ell-a,e(2)) and diagonal exponent -C+ell+a. The signed two-order binary evaluator applies at the padded cutoff, including cancellation at nonnegative diagonal powers. The original homogeneous coefficient equation fixes the final output exponent to -n-1.

The finite triangle (ell,a) maps to (u=ell+a,ell). Vandermonde combines choose(-1/2,ell) and choose(e(0),a) into choose(e(0)-1/2,u), yielding associatedTaylor(P,gamma,u,(degree-u).toNat) times choose(-M,t-u), with the exact filter u<=degree. The existing finite left outer Taylor contraction then gives the original collision sum because -(t:Z)-1=d-L.

For d>=L the actual neutral mode vanishes and the fused residue weight is zero. Negative degree gives the empty Taylor range. Zero degree, empty numerator support, zero tensor or covector, negative Laurent exponents and lifts, K=0 and an empty original outer cutoff remain included. The complete middle equality is separate; the reverse equality and the full three-component bridge are not consequences asserted here.

The calculation uses classical formal local-field calculus of Matsuo and Nagatomo and the twisted lattice conventions of Bakalov and Kac, math/0402315. Hahn, Laurent, binomial and partial-fraction operations use Mathlib, with work by Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio, Kevin Buzzard, Sidharth Hariharan and Aaron Liu, Apache 2.0. Actual field composition follows Scott Carnahan's vertexAlg, revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0. This is a formal residue computation; no literature novelty, Monster realization or complete physical string model is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockFirstOuterTaylor.fused_weighted_identity`
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/BinaryLaurentEvaluation](BinaryLaurentEvaluation.md)
