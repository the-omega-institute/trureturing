# Original CAR and Borcherds identities for the descent current

## Abstract

Original CAR and Borcherds identities for the descent current

For every D : LatticeData, use the original tensor state carrier, ghostB, originalMode, actual parity P and descentCurrent. Write B_j = ghostB D j, mu_n(x,y) = originalMode D n x y and K(x,y) = mu_0(B_(-1)x,y). The input lattice has exactly rank : Nat, an integral Gram matrix G, symmetry and even diagonal. No positivity or nondegeneracy is added, and rank zero remains allowed wherever the displayed hypotheses permit it.

The current identities use the original CAR, actual beta field and signed Borcherds residue calculus. H appears only in the energy statements, with both equations H * gramComplex D = 1 and gramComplex D * H = 1. They keep every original lattice charge, all original states and the original epsilon conventions. Neither a critical rank nor a no-ghost assertion is introduced.

Source-specific four-slot Reg audits for the public theorems remain unfinished: https://github.com/the-omega-institute/trureturing/issues/29596. Adjacent templates do not supply the complete original telescopes, source selections and checked escape coordinates for these owners. No declared_validated registration is claimed; this delivery uses the explicit linked-issue exception.

**Theorem 1.1 (The original antighost CAR on the tensor carrier).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_car`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_car` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D : LatticeData, integers m,n and x : State D, B_m(B_n x) + B_n(B_m x) = 0, where B_j = ghostB D j. The proof lifts the existing bc-ghost CAR by the original tensor map and evaluates it at x. No matrix, inverse Gram, rank, cycle, parity or energy hypothesis is needed.

**Theorem 1.2 (The literal same-mode antighost square vanishes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_square`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, integer m and original state x, B_m(B_m x) = 0. The same-mode CAR gives twice this vector equal to zero; the nonzero scalar 2 in Complex cancels. This is a consumed consequence of b_car, used in the current closure and current Leibniz proofs.

**Theorem 1.3 (Relative antighost closure of the actual current).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_b0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_b0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x,y : State D satisfying B_0 x = 0 and B_0 y = 0, B_0 K(x,y) = 0. CAR moves B_0 across B_(-1), and the actual beta-mode-one Borcherds identity eliminates the remaining B_(-1) square. Neither input is assumed to be a Q-cycle; no rank or positivity restriction is added.

**Theorem 1.4 (Energy covariance from the actual Ward identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_L0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_L0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1, and arbitrary x,y : State D, totalL0 D H (K(x,y)) = K(totalL0 D H x,y) + K(x,totalL0 D H y). The proof combines the original identity {Q,B_0} = totalL0 with the two odd current derivation laws. There is no critical-rank assumption and neither x nor y must be closed, homogeneous or of zero energy.

**Theorem 1.5 (The original antighost acts on every integer mode).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_minus_one_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_minus_one_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, original states x,y and integer n, B_(-1)(mu_n(x,y)) = mu_n(B_(-1)x,y) + mu_n(Px,B_(-1)y). This is the beta-mode-zero specialization of the actual signed Borcherds identity. Both parity projections and reverse terms are retained before the zero-binomial sums collapse. No homogeneous-input assumption is used.

**Theorem 1.6 (The even zero-mode commutator as a vector identity).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.even_zero_mode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.even_zero_mode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, states u,v,w and integer n, if Pu = u and Pv = v, then mu_0(u,mu_n(v,w)) = mu_n(mu_0(u,v),w) + mu_n(v,mu_0(u,w)). The third state is unrestricted. The actual homogeneous Borcherds identity, at even parities and zero binomial index, proves this on the original carrier.

**Theorem 1.7 (Exact unsigned current Leibniz before quotienting).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_leftLeibniz`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_leftLeibniz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and x,y,z : State D with Px = -x and Py = -y, K(x,K(y,z)) = K(K(x,y),z) + K(y,K(x,z)). The third state z is arbitrary. Oddness makes B_(-1)x and B_(-1)y even; b_minus_one_mode, b_square and even_zero_mode identify the nested currents as literal vectors. No cycle, quotient, inverse-Gram, energy or rank assumption occurs.

**Theorem 1.8 (Zero energy of relative closed representatives).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_zero_energy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_zero_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary D and H with both inverse-Gram equations hHG and hGH, let x,y belong to cycles D H and assume B_0 x = B_0 y = 0. Then totalL0 D H (K(x,y)) = 0. Actual Q-closure of K and current_b0 are inserted into the original Ward identity. No rank-26, charge, positivity or nonzero-momentum hypothesis is required.

The tensor CAR and native Borcherds suppliers retain their original lattice and ghost attribution, Scott Carnahan's residue calculus, and Mathlib. These are algebraic current identities on the stated complex; no literature novelty, physical positivity, no-ghost theorem, complete string theory, spacetime reconstruction or AdS/CFT conclusion is asserted.

Direct mathematical suppliers: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder`

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_car`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_minus_one_mode`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.b_square`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_L0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_b0`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_leftLeibniz`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.current_zero_energy`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeBRSTCurrentIdentities.even_zero_mode`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](LatticeBRSTCohomologyBVSecondOrder.md)
- Narrative reference: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyBVSecondOrder](LatticeBRSTCohomologyBVSecondOrder.md)
