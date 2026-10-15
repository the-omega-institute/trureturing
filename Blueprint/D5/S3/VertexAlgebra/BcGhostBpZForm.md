# Operator-Derived Ghost BPZ Pairing

## Abstract

The full algebraic bc Fock pairing is constructed from its actual graded-reversed creator word and native top coefficient, with a derived nonconstant phase and all-integral ghost and stress transpose laws.

The carrier is the unrestricted Fock = (Finset Nat) →₀ Complex. The increasing basisWord is the released creator-word reconstruction, and the product is the real noncommutative Module.End product of the reversed list of bpzSite operators. Its graded factor is (-1)^(card(S)(card(S)-1)/2). Even sites 2r transpose to (-1)^r b(r+2); odd sites 2r+1 transpose to (-1)^r c(r-1). The top vector is the actual c(-1)c(0)c(1)vacuum = -basis{1,3,5}, and topCoeff is minus the coefficient at that finite top set.

**Theorem 1.1 (Finite site involution).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.rho_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.rho_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preserved site map exchanges each outside even/odd pair and reverses the three top sites. It uses no infinite complement.

**Theorem 1.2 (Finite paired occupation set).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.chi_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.chi_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

chi(S) = rho(S minus Z) union (Z minus rho(S intersect Z)), with Z={1,3,5}. This preserved map is involutive on every finite occupation set.

**Theorem 1.3 (Actual ordered-word coefficient bridge).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.rawBasis_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.rawBasis_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Signed insertion/deletion coefficient identities pull the native reversed word back from Z, one actual operator at a time. The resulting occupation is chi(S). eps(S) is defined by the genuine raw value on basis(chi(S)), not by an assumed kernel. For every right state y the raw coefficient equals eps(S) y(chi(S)). In particular S={0}, T={1,3,5,7} gives +1, not the constant-sign candidate value -1.

**Theorem 1.4 (Derived nonzero phase).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.eps_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.eps_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct creator sites make every coefficient pullback admissible. Its finite product of native signs is nonzero. Coefficient conjugation also fixes eps(S). This is standard bc mathematics, not a novelty or positivity claim.

**Theorem 1.5 (Native finite phase kernel).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_kernel`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite Finsupp extension defines bpz(x) as an actual operator and BPZ(x,y)=topCoeff(bpz(x)y). Its basis value is eps(S) if T=chi(S), otherwise zero. There is no finite occupation or mode cutoff and no record assuming an adjoint or invariant form.

**Theorem 1.6 (All-integer ghost degree selection).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_degree_selection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_degree_selection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preserved degree(S)+degree(chi(S))=3 supplies selection on homogeneous states of arbitrary integer degrees. Mixed states remain genuine superpositions. Pi=parityPart(0)-parityPart(1) is the actual parity operator, not a single sign assigned to a mixed state.

**Theorem 1.7 (All-integral b transpose).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_b`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_b` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BPZ(b(m)x,y)=(-1)^m BPZ(Pi(x),b(-m)y). The proof uses the actual raw creator insertion identity and native deletion coefficients. A parity-p homogeneous left state contributes (-1)^p.

**Theorem 1.8 (All-integral c transpose).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_c`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_c` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BPZ(c(n)x,y)=(-1)^(n-1) BPZ(Pi(x),c(-n)y), on the same full carrier and for every integral n.

**Theorem 1.9 (Exact normal-order correction).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_normalPair`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_normalPair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transpose of normalPair(p,q) is -(-1)^(p+q) times normalPair(-p,-q), minus BPZ(x,y) precisely when p is in {-1,0,1} and p+q=0. The scalar middle-mode term is retained, rather than discarded under normal ordering.

**Theorem 1.10 (Finite native stress transpose).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_stress`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_stress` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

BPZ(L(m)x,y)=(-1)^m BPZ(x,L(-m)y). Both actual L_interval_sum expressions use the common symmetric interval with radius max(cutoff(m,x),cutoff(-m,y))+2. Negation is a proved finite index bijection. Only the m=0 correction survives to the finite middle set, and its weighted -1+0+1 sum is exactly zero. No unbounded sum is reindexed.

**Theorem 1.11 (Derived symmetry).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Symmetry is derived from the actual ordered-word transpose laws, odd total paired parity, and genuine vacuum/top normalization. It is not inherited as an assumption from a constant-sign candidate.

**Theorem 1.12 (Conjugate-left ghost form).**

Lean statement: `D5/S3/VertexAlgebra/BcGhostBpZForm.Hghost_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/BcGhostBpZForm.Hghost_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hghost(x,y)=BPZ(conjCoeffs(x),y), with no outer star. Hghost(a x,y)=star(a) Hghost(x,y), and Hghost(x,a y)=a Hghost(x,y). Its Hermitian symmetry follows from the derived BPZ symmetry and real native phase. No positive-definiteness or matter-form assertion follows.

Primitive b/c here carry physical integral indices. The released currentMode shifts vertex indices: currentMode(b,1)=b(0) and currentMode(c,-2)=c(0). These are physicalB0 and physicalC0; the primitive b(1) and c(-2) are not that zero-mode pair. On v=e_empty, u=e3, j=e1, k=-e13, z=-e15, w=-e135, the only nonzero ordered scalar pairings are v/w, w/v, u/z, z/u, j/k, k/j, all +1. B0 sends u to v, k to j, w to -z and kills the other three; C0 sends v to u, j to k, z to -w and kills the other three. These scalar values and homogeneous/scalar specializations are transient compiled exact checks, not extra bind-only theorem declarations. They provide no indexed matter delta, charged BPZ phase or orthonormal matter frame.

Original-Q transpose, charged matter/PCT mode transpose, quotient descent and the physical form remain open. A later individual A(n) calculation must retain the exact -(1/2)(-1)^parity n d0(n) BPZtotal(x,C0 y) correction, and cancel it only after the genuine finite symmetric Q sum. Linear lattice theta is not antilinear PCT. Relative C0 is an insertion/lift on actual restricted relative preimages, not a relative endomorphism or a form on arbitrary absolute representatives; ker(B0) isotropy, {Q,C0}=-(1/2)V0 and [B0,V0]=0 still need the genuine total-form interface. Real transverse pullback, isometry, radical, positivity, exceptional/zero-charge sectors and global physics are not claimed. The full moonshine/VOA/CFT/anomaly/fusion/string/AdS objective remains open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_b`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_c`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_degree_selection`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_kernel`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_normalPair`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_stress`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.BPZ_symmetric`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.Hghost_hermitian`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.chi_involutive`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.eps_nonzero`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.rawBasis_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/BcGhostBpZForm.rho_involutive`
