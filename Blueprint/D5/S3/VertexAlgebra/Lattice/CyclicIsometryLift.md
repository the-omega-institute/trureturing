# Exact Cyclic Lifts on the Actual Lattice Vertex Algebra

## Abstract

Every finite-order additive lattice isometry admits an actual sign-character-corrected lift of the same exact order.

Let D have finite rank r, integral symmetric Gram matrix G and even diagonal. The charge lattice is L=Z^r with bilinear form B. The actual carrier V is the finite charge sum of complex oscillator polynomials, with the constructed state-field map Y, vacuum single(0,1) and translation T. Rank zero, singular forms and indefinite forms are included. Let g be any additive equivalence preserving B. For a positive natural number m suppose g iterated m times is the identity.

Write c for the actual lower-triangular cocycle modulo two and eta for the literal phase of the actual isometry lift U_g. Isometry and c(a,a)=B(a,a)/2 make every diagonal entry of the defect matrix zero modulo two. Its fourth-root factors are therefore one. Thus eta(a)=(-1)^q(a), where q is the existing off-diagonal quadratic refinement on charges modulo two.

**Theorem 1.1 (The canonical operator power and the orbit norm character).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift.canonical_power`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift.canonical_power` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Set N_m(a)=sum_(0<=j<m) g^j(a) and Q_m(a)=product_(0<=j<m) eta(g^j(a)). The orbitCharacter takes values in F2 and satisfies (-1)^orbitCharacter(a)=Q_m(a). It is additive and g-invariant. On the full actual carrier, U_g^m is the diagonal operator multiplying the a-charge sector by Q_m(a), with every oscillator polynomial unchanged. For every charge a the exact identity is Q_m(a)=eta(N_m(a)) (-1)^B(a,N_m(a)).

For a_j=g^j(a) and S_n=sum_(0<=j<n) a_j, the prefix identity is q(S_n)+sum_(0<=j<n)q(a_j)=c(S_n-a,a_n)+c(a,S_n-a). Its induction uses g(S_n)=S_n-a+a_n and the quadratic defect law. At n=m, a_m=a and cocycle symmetrization yields B(a,N_m(a)) modulo two. Additivity follows by telescoping the cocycle defect along two orbits; shifting an orbit gives invariance.

Oscillator substitution powers are checked on the polynomial generators: the n-th substitution sends X_(i,k) to the charge-coordinate combination determined by g^n(e_i), at the same frequency k. Polynomial induction proves identity substitution when g^m=1. The actual lift formula on single(a,p), followed by finite-support linear extension, then proves the operator identity on every state.

**Theorem 1.2 (A sign correction preserves all actual modes and the exact charge order).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift.cyclic_lift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift.cyclic_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

There exists an additive character chi:L to F2 such that W=U_g D_chi, where D_chi(single(a,p))=(-1)^chi(a) single(a,p), fixes the actual vacuum, commutes with T, and satisfies W((Y(u))_n v)=(Y(W(u)))_n W(v) for all u,v in V and all n in Z. Moreover W^m=1. If the exact permutation order of g is m, then for every natural k, including zero, W^k=1 if and only if m divides k.

If the norm N_m(a) reduces to zero modulo two, the orbit-norm identity gives Q_m(a)=1: both q(N_m(a)) and B(a,N_m(a)) vanish modulo two. The reduced orbit functional therefore vanishes on the reduced norm kernel. It descends to the norm image by linear-map factorization, and a linear functional on that image extends to all reduced charges. Its pullback is chi, with chi(N_m(a))=orbitCharacter(a), so the two signs cancel in the m-th actual operator power.

The diagonal action preserves arbitrary integer modes because the actual charge_homogeneity theorem places each homogeneous product in charge a+b. Additivity of chi gives its scalar law. Bilinear extension in both input states proves the result for arbitrary oscillator polynomials and finite sums of charges. Composition with the actual all-state isometry theorem gives the full covariance law for W. Translation is the mode -2 applied to the vacuum.

The lower order bound uses the actual nonzero state single(a,1). If W^k=1, its charge is both g^k(a) and a. Distinct charges remain distinct direct summands even for a degenerate bilinear form. Hence g^k=1, and the general order-of-element divisibility theorem gives m divides k.

The central-extension setting is classical in Frenkel-Lepowsky-Meurman, Dong-Nagatomo and Lepowsky. Borcherds, Monstrous moonshine and monstrous Lie superalgebras, Lemma 12.1, uses the orbit argument for standard lifts in the Leech lattice setting. That printed setting is not the source of the singular and indefinite generality above. No literature novelty is claimed.

The correction concerns a single cyclic subgroup. It can change the phase on fixed charges and need not preserve standard fixed-space normalization. The literal canonical lift may have order twice m. Choosing these corrections individually does not give a section for the whole isometry group.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift.canonical_power`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/CyclicIsometryLift.cyclic_lift`
- Dependency: [D5/S3/VertexAlgebra/Lattice/IsometryLift](IsometryLift.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
