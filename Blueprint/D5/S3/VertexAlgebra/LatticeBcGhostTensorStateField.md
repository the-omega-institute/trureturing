# Compiled bridges

## Abstract

Actual lattice matter tensor bc state-field on the original carrier.

TensorProduct.lift composes the accepted finite integer-mode convolution with the actual lattice and bc state fields. The matter factor is even; parity is carried by the bc factor.

Signed occupation and physical labels. For a finite occupied-site set S, let d(S) be the number of odd sites minus the number of even sites. The existing BcGhostNumber.J acts on the occupation basis by J(e_S) = d(S)e_S, and on an arbitrary finite expansion a = sum_S a_S e_S by J(a) = sum_S d(S)a_S e_S. Thus odd c occupations contribute +1 and even b occupations contribute -1. This is integer ghost number, not conformal energy or just parity. The reconstructed field labels are shifted physical labels: currentField(b)_n = physical b(n-1) and currentField(c)_n = physical c(n+2), for every integer n. The existing J_b_commutator and J_c_commutator give [J,b(k)] = -b(k) and [J,c(k)] = c(k) for every physical integer k; J_L_commutator gives degree zero for the original stress modes.

Signed reconstruction. A site i supplies the divided derivative of order floor(i/2) of its b or c current field, with b for even i and c for odd i. Divided differentiation changes the mode index and its scalar coefficient, but not its ghost degree sigma(i), where sigma(i) = -1 for even i and +1 for odd i. The empty word field is the identity field. For a nonempty word i::w, wordField is the signed normal product of siteField(i) and wordField(w), with exchange scalar (-1) raised to length(w). The signed normal product is the residue at parameter -1; its two ordered sums carry their actual exchange sign. Induction through this recursion gives [J,wordField(w)_n] = (sum over i in w of sigma(i)) wordField(w)_n, for every integer n. The ordinary endomorphism product step reuses the existing product_degree supplier at LatticeBcGhostBrstGhostNumber, rather than a second commutator-product theorem.

Statewise finite residues. For residue parameter p and mode n, the left summands on v are weight(p,i) A_(p-i)(B_(n+i)v), and the right summands are weight(p,i) B_(p+n-i)(A_i v), with natural i and integer field indices. The residue is the left sum minus epsilon(p) times the exchange scalar times the right sum. The actual residue_left_finite and residue_right_finite suppliers give finite support separately on v and on Jv. The image of a finite-support summand family under J also has finite support because J(0)=0. Consequently map_finsum, finsum_sub_distrib and scalar mapping legitimately move the even J commutator inside each statewise finite sum. Applying product_degree to each ordered pair proves residue degree equal to the sum of the two field degrees, with no change to the exchange scalar and no global cutoff, analytic convergence premise or uniform bound on occupations.

All-state Ward identity. The canonical basisWord enumerates each finite occupation set once. Its signed word degree equals d(S), using the original degree_insert supplier and the original J_single eigenaction, not a re-proved occupation-count lemma. The existing stateField_expansion is Y(a) = sum_S a_S wordField(basisWord(S)). Linearity and the word commutator therefore give [J,Y(a)_n] = Y(Ja)_n and, after evaluation, J(Y(a)_n v) = Y(Ja)_n v + Y(a)_n(Jv). These identities hold for every original ghost state a, every original ghost input v and every n in the integers, including mixed-degree states. No ghost-current zero-mode realization of J is assumed.

Actual matter tensor convolution. On pure tensors, Y_D(m tensor a)_n(u tensor v) = sum over integer i of Y_matter(m)_i u tensor Y_ghost(a)_(n-1-i) v. This is the actual stateField_mode_tmul formula, not a replacement graded multiplication. The existing diagonal_finite result applies to the base convolution, to the convolution with Ja, and to the convolution with Jv. For J_D = identity on matter tensor J, these three finite-support facts justify moving J_D through the sum and distributing the two Ward terms. Tensor induction in both arguments then proves J_D(Y_D(A)_n V) = Y_D(J_D A)_n V + Y_D(A)_n(J_D V), for arbitrary full algebraic tensor states A,V, every lattice datum D and every integer n. Matter has ghost number zero. No inverse Gram matrix, rank 26, positivity, signature condition, conformal-energy restriction or finite-dimensional energy fibre is needed for this identity.

Integer-degree consequence. If r,s are integers and JA = r A, JV = s V, with the integers embedded in the complex scalars, the Ward identity and complex bilinearity give J(Y(A)_n V) = (r+s) Y(A)_n V for every integer n. The same substitution gives the tensor statement with J_D and Y_D. This includes negative degrees and the zero output; it is a conditional eigenvalue consequence, not a proof that arbitrary states are eigenvectors, that all quotient classes admit homogeneous representatives, or that an integer direct-sum decomposition exists. It is an application of the covariance proof, with no independent mathematical or novelty claim attached to a separately named degree theorem.

**Theorem 1.1 (All-state creation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Creation is proved on arbitrary algebraic tensor states by tensor induction.

**Theorem 1.2 (Vacuum creativity).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creativity`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creativity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonnegative mode vanishes on the actual tensor vacuum.

**Theorem 1.3 (Actual parity decomposition).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.parity_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.parity_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second-factor parity projections are idempotent, orthogonal, and exhaustive on arbitrary tensor states.

**Theorem 1.4 (Original translation bridge).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.translation_original`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.translation_original` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bridge retains both Gram inverse equations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.parity_decomposition`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.stateField_creativity`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostTensorStateField.translation_original`
- Dependency: [D5/S3/VertexAlgebra/LatticeAllStateField](LatticeAllStateField.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstCharge](LatticeBcGhostBrstCharge.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostBrstGhostNumber](LatticeBcGhostBrstGhostNumber.md)
