# The Actual Norm-Four Annihilator Vertex Algebra

## Abstract

The literal nonnegative norm-four mode annihilator inherits the actual lattice vertex algebra and its coset conformal action.

Let D be the production finite-rank even integral lattice data. Carrier(D) is the actual finite-charge polynomial oscillator carrier, vacuum is single(0,1), Y is its actual state-field map and T its charge-sensitive translation. For a charge a and a complex scalar s, let e be NormFourVirasoroVector.vector(D,a,s). Define A as exactly the submodule of v in Carrier(D) such that Y(e)_j v=0 for every integer j at least zero. The notation Y(u)_n means the Laurent coefficient with exponent -n-1. There is no substituted e-zero kernel, positive-mode-only condition, assumed closure, or auxiliary smaller space.

**Theorem 1.1 (Actual vacuum, every integer coefficient and translation preserve the literal space).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.actual_closure`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.actual_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary production D, charge a and complex s, the actual vacuum belongs to A. For all u,v in A and every integer n, Y(u)_n v belongs to A; T(v) also belongs to A. All restricted state-field coefficients, for every u,v in A and every integer n, have underlying value exactly Y(u.val)_n v.val.

For each nonnegative j, the actual mode commutator of Y(e)_j with Y(u)_n has terms binomial(j,k)Y(e_k u)_(j+n-k), indexed by natural k. Every actual state e_k u is zero by the literal hypothesis on u, so every term is zero. Applying the zero commutator to v and using e_j v=0 proves coefficient closure for arbitrary integer n. Creativity gives vacuum membership. The actual identity T(v)=Y(v)_(-2)vacuum then gives translation closure.

**Definition 1.2 (A genuine StateFieldVertexAlgebra on the literal subtype).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.restrictedVertexAlgebra`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.restrictedVertexAlgebra` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,s, restrictedVertexAlgebra is a StateFieldVertexAlgebra on CommutantCarrier(D,a,s)=A. Its data are restrictedY, the actual vacuum and restricted T. The field is a VertexOperator with statewise lower truncation inherited from the actual ambient Hahn order, and every integer coefficient is the actual ambient coefficient. The construction proves the vacuum field, creation at -1, creativity at all n at least zero, T(vacuum)=0, covariance [T,Y(u)_n]=-nY(u)_(n-1), and finite-order locality. For every u,v,w in A and all integers p,q,r, it inherits the complete integer Borcherds identity: the left family binomial(p,i)(u_(r+i)v)_(p+q-i)w, the first right family (-1)^i binomial(r,i)u_(p+r-i)(v_(q+i)w), and the second right family (-1)^i binomial(r,i)epsilon(r)v_(q+r-i)(u_(p+i)w) each have their actual finite support; the left finsum equals the finsum of the signed difference of the right terms. Subtype inclusion preserves zero exactly, hence each support and the finsum identity.

The concrete lower-truncation, covariance, iterated-locality and finite-support inheritance adapts the existing LatticeInvolution fixed-subtype implementation. Its reflection-specific closure is not a premise here. This module uses the actual ambient StateFieldVertexAlgebra and the independently proved annihilator closure.

**Theorem 1.3 (The actual restricted coset field, translation and all-integer Virasoro law).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.coset_conformal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.coset_conformal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be the complex Gram matrix and let H satisfy both HG=1 and GH=1. Suppose B(a,a)=4 and s squared equals one. Then c=omega(D,H)-e lies in the literal A, as witnessed by cosetVector. For every integer n and every v in A, the underlying value of restrictedY(c)_n v is exactly the actual ambient Y(c)_n v.val. Put C_m=restrictedY(c)_(m+1) for every integer m. On A, C_(-1)=restricted T, and for all integers m,n, [C_m,C_n]=(m-n)C_(m+n)+delta_(m+n,0)((rank(D)-1/2)/12)(m^3-m)I. Thus this actual ungraded vertex algebra has coset conformal state c and central charge rank(D)-1/2.

Membership subtracts the complete reverse mixed OPE e_j omega from the complete self OPE e_j e: both give T(e), 2e, zero, vacuum/4 at j=0,1,2,3 and zero throughout the tail j at least four. The actual complementary mode is Ltot_m-Le_m. At m=-1, the Sugawara mode is T and Le_(-1)=e_0 kills every state of this literal space, proving C_(-1)=T there. The accepted all-integer coset Virasoro law on the full carrier restricts through the injective subtype inclusion. At rank 24 the central charge specializes to 47/2; no extra numerical theorem is needed.

The norm-four formula is classical: Shimakura, arXiv:1202.6107, (1.3), attributes it to Dong-Mason-Zhu, Theorem 6.3. Ambient lattice fields follow Bakalov-Kac, math/0402315, section 4.1. The accepted NormFourCosetVirasoro mixed products and coset law and NormFourVirasoroVector self products supply their original attribution. The concrete annihilator closure and restriction here are repository derivations from those suppliers, without a novelty claim for the classical coset method. Imported Carnahan, Matsuo-Nagatomo and Kytola sources retain their license notices. No positivity, grading, CFT type, simplicity, rationality, fusion, Baby Monster or Monster completion is asserted. No identification with the commutant of an independently constructed full Ising VOA is asserted.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.actual_closure`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.coset_conformal`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/NormFourCommutant.restrictedVertexAlgebra`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourCosetVirasoro](NormFourCosetVirasoro.md)
