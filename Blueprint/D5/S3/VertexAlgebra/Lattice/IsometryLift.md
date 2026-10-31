# Isometry Lifts on the Actual Lattice Vertex Algebra

## Abstract

Every additive isometry lifts to the actual lattice fields on all polynomial and finite-charge states.

Let D have finite rank r, integral symmetric Gram matrix G and even diagonal. Write L=Z^r, B(a,b)=sum_i,j a_i G_ij b_j, and V for the finite charge sum of complex oscillator polynomials in X_(i,k), i in Fin(r), k in N. The state-field map Y, vacuum 1_V=single(0,1), charged rawCoeff and translation T are the actual constructed operators on V. Let g:L to L be an additive equivalence satisfying B(g(a),g(b))=B(a,b) for all a,b. Rank zero, singular forms and indefinite forms are included; positivity and a Gram inverse are unnecessary.

The literal sign is epsilon(a,b)=(-1)^c(a,b), where c is the existing lower-triangular integral cocycle, with half the diagonal of G. Put S_ij=c(g(e_i),g(e_j))+c(e_i,e_j) modulo two. Isometry and cocycle symmetrization make S symmetric. The existing quadratic refinement liftPhase(S, a modulo two) gives a nonzero unit eta(a), with eta(0)=1 and eta(a+b) epsilon(a,b)=eta(a) eta(b) epsilon(g(a),g(b)). Thus no phase compatibility equation is imposed as an extra premise.

**Theorem 1.1 (The carrier equivalence transforms charges and every oscillator).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/IsometryLift.lift_single`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/IsometryLift.lift_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Let M_ji be the jth coordinate of g(e_i). The polynomial algebra equivalence S_g fixes complex constants and sends X_(i,k) to sum_j M_ji X_(j,k), at every frequency k. Its inverse uses the columns of g inverse. The existing finite matrix substitution equivalence supplies both inverse identities.

The complex-linear equivalence U is determined by U(single(a,p))=eta(a) single(g(a),S_g(p)). Its explicit inverse sends single(b,q) to eta(g inverse(b)) inverse times single(g inverse(b),S_g inverse(q)). All states have finite charge support.

**Theorem 1.2 (Vacuum, arbitrary charged coefficients, all state modes and translation).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/IsometryLift.lift_compatible`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/IsometryLift.lift_compatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The same U fixes 1_V. For every a in L, k in Z and v in V, U(rawCoeff(a,k)v)=eta(a) rawCoeff(g(a),k)U(v). For every u,v in V and every n in Z, U((Y(u))_n v)=(Y(U(u)))_n U(v). Finally U(Tv)=T(U(v)) for every v. The mode index is unchanged. Inhomogeneous mixed oscillator polynomials and arbitrary finite sums of charges remain in scope.

Polynomial substitution transports the creation series and its formal exponential by the existing power-series map and substitution laws. The contraction identity is sum_j M_ji B(g(a),e_j)=B(a,e_i). Polynomial algebra-homomorphism extensionality therefore transports the translated polynomial on arbitrary p, and injectivity preserves its coefficient support. The actual rawCoeff-on-single identity and the phase equation then transport the exact finite raw convolution.

Let W be the complex subspace of states u whose every integer mode intertwines U on every input. The actual iterate identity proves that u_r v lies in W whenever u and v do: apply U to its two sums using their actual finite supports, transport both ordered terms, and use the target iterate identity. Charged ground states belong to W by the raw coefficient law and Y(single(a,1))=actualField(a).

All neutral currents follow from charged grounds. The exact coefficient rawCoeff(a,1-B(a,a)) single(-a,1) is epsilon(a,-a) single(0,sum_i a_i X_(i,0)). Its normalized mode is B(a,a)-2, including zero and negative norms. At a=e_i, the nonzero sign and product closure place single(0,X_(i,0)) in W. Its actual negative mode -k-1 multiplies any sector polynomial by X_(i,k). Polynomial induction and finite charge sums give W=V. Translation then follows from T(u)=(Y(u))_(-2) 1_V.

For the positive A2 matrix G=[[2,1],[1,2]] and g(a,b)=(-b,a+b), the literal cocycle is invariant and eta is one. Writing x_k=X_(0,k), y_k=X_(1,k), the substitution is x_k to y_k and y_k to -x_k+y_k, so y_0 squared maps to x_0 squared minus 2 x_0 y_0 plus y_0 squared. The phase-sensitive reflection g(a,b)=(a+b,-b) has compatible eta(a,b)=(-1)^(a b). These illustrate mixing and the role of the literal section.

A lift for each individual isometry does not assert a coherent action of the whole isometry group, a splitting of the extension formed by the lifts or preservation of finite order. There is no standard fixed-space normalization. The result concerns the algebraic ungraded vertex algebra; conformal-vector, positive-energy, PCT and physical-realization claims are outside its statement.

The lattice-field and lift context is classical: Bakalov-Kac, math/0402315v1, section 4.1, and Frenkel-Lepowsky-Meurman. Cocycle refinement, finite matrix substitution and power-series naturality are reused results. Residue reconstruction retains Matsuo-Nagatomo, hep-th/9706118v1, Proposition 1.5.5 and Theorem 5.4.1, and the inherited Scott Carnahan vertexAlg Apache-2.0 attribution in its owning sources. No literature novelty is claimed.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/IsometryLift.lift_compatible`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/IsometryLift.lift_single`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector](NormFourVirasoroVector.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualVertexAlgebra](../LatticeActualVertexAlgebra.md)
- Dependency: [D5/S3/VertexAlgebra/OriginalCurrentMetric](../OriginalCurrentMetric.md)
