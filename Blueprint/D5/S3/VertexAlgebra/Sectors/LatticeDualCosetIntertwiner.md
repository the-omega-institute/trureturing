# Full rational Hahn dual-coset fields and derived ground spectrum

## Abstract

LatticeDualCosetIntertwiner

All entries quantify over arbitrary finite-rank symmetric even integral LatticeData D, including rank zero. Charge D is the original integral charge lattice; Carrier D is the complete finitely supported charge carrier with polynomial oscillators. a,b are integral module parameters, H is a complex matrix, and I is an arbitrary source-linear rational Hahn field. mode(I,u,tau) is raw coefficient -tau-1. Whenever stated, the full hypotheses are Lawful D a b H I, H G_C=1 and G_C H=1, rational mu,nu and exact duality G_Q mu=a, G_Q nu=b. Positivity and integral unimodularity are not assumed. The acting algebra and all module actions, cocycle and original conformal state are the actual native ones.

Classical lattice-fusion conventions follow Bakalov--Kac, math/0402315v1, section 4.1. Imported residue and Pascal suppliers retain Scott Carnahan, ScottCarnahan/vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea; imported Sugawara suppliers retain Kalle Kytölä, VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. Both suppliers retain their Apache-2.0 attributions. These are native applications and proofs of classical mathematics; no literature novelty is claimed.

**Definition 1.1 (Fields).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.Fields`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.Fields` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Carrier D →ₗ[Complex] HVertexOperator Rational Complex (Carrier D) (Carrier D): the entire source-linear rational Hahn ambient space, with source and input states both arbitrary. No lawful field, nonzero field, prescribed charge support, exponent coset or leading scalar is built into this type.

**Definition 1.2 (mode).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,I,u and rational tau, mode I u tau is (I u).coeff(-tau-1), a complex linear endomorphism of the input carrier.

**Definition 1.3 (leftTerm).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.leftTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.leftTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary D,a,I,h,u,v, integers p,r, rational tau and natural i: binomial(p,i) times mode I ((action(a,h)[r+i])u) (p+tau-i) v.

**Definition 1.4 (firstTerm).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.firstTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.firstTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary D,a,b,I,h,u,v,p,r,tau,i: (-1)^i binomial(r,i) times action(a+b,h)[p+r-i] applied to mode I u (tau+i) v.

**Definition 1.5 (secondTerm).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.secondTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.secondTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary D,b,I,h,u,v,p,r,tau,i: (-1)^i binomial(r,i) times the residue sign epsilon(r) times mode I u (tau+r-i) ((action(b,h)[p+i])v). The residue sign is distinct from the lattice cocycle epsilon(D,m,n).

**Definition 1.6 (Lawful).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.Lawful`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.Lawful` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every source u and rational tau, source L(-1) differentiates the field: mode I (moduleL(a,H,-1)u) tau = -tau times mode I u (tau-1). The target L(-1) commutator equals the same derivative using target a+b and input b. For every algebra state h, source u, input v, integers p,r and rational tau, EACH of leftTerm, firstTerm and secondTerm has finite natural-index support, and sum(leftTerm)=sum(firstTerm)-sum(secondTerm). These are full arbitrary-charged mixed Jacobi laws; there is no charge, exponent-coset or leading-normalization axiom.

**Definition 1.7 (operatorSpace).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.operatorSpace`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.operatorSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,a,b,H, the complex submodule of Fields D consisting exactly of Lawful fields. Private lawful_zero, lawful_add and lawful_smul establish closure and are live consumers of the three separate finite-support laws. Closure establishes no nonzero element.

**Definition 1.8 (ground).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every integral charge n, ground D n is Finsupp.single n 1 in the actual carrier; the polynomial has no oscillators.

**Definition 1.9 (groundPower).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every rational mu,nu and integral n,l, groundPower is pairing D (n+mu) (l+nu), with rational coordinates and the original Gram pairing.

**Definition 1.10 (groundScalar).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundScalar`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundScalar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D,I,mu,nu,n,l, take the coefficient of I(ground n)(ground l) at raw power groundPower(mu,nu,n,l), then its charge n+l component, then polynomial constantCoeff. No nonvanishing or normalization is assumed.

**Definition 1.11 (chargedPower).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.chargedPower`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.chargedPower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every D and integral d,m,n, chargedPower D d m n = bilinear D m n + sum_i m_i d_i, an integer.

**Theorem 1.12 (mode_smul_source).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode_smul_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode_smul_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,I, complex c, source u, rational tau and input v, mode I (c smul u) tau v = c smul mode I u tau v. No Lawful or inverse hypotheses. Derived by source linearity. Used by coefficient_charge, charged_source_recurrence and reconstruct_source.

**Theorem 1.13 (mode_add_source).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode_add_source`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode_add_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,I,u,w,tau,v, mode I (u+w) tau v is the sum of the two source modes. No Lawful or inverse hypotheses. Derived by source linearity. Used by reconstruct_source and ground_sequence_detects_zero.

**Theorem 1.14 (ward).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Lawful I, all algebra h, source u, input v, integer p and rational tau: action(a+b,h)[p](mode I u tau v) - mode I u tau(action(b,h)[p]v) = sum_i leftTerm(D,a,I,h,u,v,p,0,tau,i). Set r=0 in full Jacobi; the other binomial sums each collapse to i=0. No inverse or duality hypotheses. Used by ground_current_ward, energy_ward and coefficient_charge.

**Theorem 1.15 (current_ground).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.current_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.current_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integral d,n, colour i and natural j, action(d,currentState i)[j](ground n) equals (bilinear(unitCharge i,n)+d_i) smul ground n if j=0 and zero otherwise. No I, Lawful or inverse hypotheses. Substitute the native current coefficients and differentiate the constant polynomial. Used by ground_current_ward and pair_ground_detects_zero.

**Theorem 1.16 (ground_current_ward).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_current_ward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_current_ward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Lawful I, integral n, arbitrary input v, colour i, integer p and rational tau, the current commutator on mode I (ground n) tau v equals (bilinear(unitCharge i,n)+a_i) smul mode I (ground n) (p+tau) v. Apply ward and current_ground; all positive source-current terms vanish. No inverse or duality hypotheses. Used by pair_ground_detects_zero and reconstruct_input.

**Theorem 1.17 (energy_ward).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.energy_ward`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.energy_ward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Lawful I and all u,v,tau, moduleL(a+b,H,0)(mode I u tau v) - mode I u tau(moduleL(b,H,0)v) = mode I (moduleL(a,H,0)u) tau v - (tau+1) smul mode I u tau v. Use ward with the original omega and p=1, then the actual source-translation law. No inverse or duality hypotheses. Used by ground_eigen.

**Theorem 1.18 (current_component).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.current_component`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.current_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,d,i, integer m, arbitrary carrier v and charge k, the charge k component of action(d,currentState i)[m]v is shiftedCurrentPolynomial D d 1 i k m (v k). The proof extends the native single-charge current formula through finite-support linear induction. No I, Lawful or inverse hypotheses. Used in coefficient_charge and pair_ground_detects_zero.

**Theorem 1.19 (coefficient_charge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.coefficient_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.coefficient_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Lawful I with H G_C=1, integral source/input/output charges n,l,k, arbitrary oscillator polynomials u,v and rational tau, a nonzero charge k component of mode I (single n u) tau (single l v) forces k=n+l. Zero-current Ward identities give all Gram row equations; cancel the nonzero polynomial and apply the original Gram left inverse. No right-inverse, positivity or rational-duality hypothesis. This forces charge support, as used by ground_charge.

**Theorem 1.20 (ground_charge).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_charge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Lawful I with H G_C=1 and every n,l,k,tau, a nonzero charge k component of the ground-to-ground mode forces k=n+l. This is coefficient_charge at the constant source and input polynomials. Used by ground_charge_projection.

**Theorem 1.21 (ground_charge_projection).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_charge_projection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_charge_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Lawful I with H G_C=1 and all n,l,tau, the whole ground-to-ground mode equals single(n+l, its n+l component). Use ground_charge to eliminate every other charge. No right inverse or rational duality is required. Used by ground_leading and pair_ground_detects_zero.

**Theorem 1.22 (ground_energy_difference).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_energy_difference`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_energy_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, rational mu,nu and integral n,l, q_(mu+nu)(n+l)-q_mu(n)-q_nu(l)=groundPower(mu,nu,n,l). Expand the original quadratic form using symmetry and bilinearity. No I, inverse or exact-duality hypothesis. Used by ground_spectrum.

**Theorem 1.23 (ground_L0).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_L0`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_L0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D,H, integral d, both inverse equations, rational mu with G_Q mu=d and integral n, actual moduleL(d,H,0)(ground n)=q_mu(n) smul ground n. Specialize moduleL_basis_zero to oscillator exponent zero. No Lawful field is required. Used by ground_eigen.

**Theorem 1.24 (dual_add).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.dual_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.dual_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and integral a,b, rational mu,nu with G_Q mu=a and G_Q nu=b, G_Q(mu+nu)=a+b coordinatewise. Distribute the finite sums. No I or inverse hypotheses. Used by ground_spectrum.

**Theorem 1.25 (ground_eigen).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_eigen`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_eigen` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for all n,l and rational raw power s, actual moduleL(a+b,H,0) on (I(ground n)).coeff s (ground l) is multiplication by q_mu(n)+q_nu(l)+s. Apply energy_ward at tau=-s-1 and the two actual ground_L0 equations. The coefficient may be zero. Used by ground_spectrum.

**Theorem 1.26 (ground_spectrum).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_spectrum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for every n,l,k, oscillator exponent e and rational raw power s, a nonzero polynomial coefficient e in charge k of the ground-to-ground field implies BOTH k=n+l and s=groundPower(mu,nu,n,l)+oscillatorEnergy(e). Combine charge selection with actual moduleL_coeff, cancel the nonzero coefficient and use the quadratic energy difference. This derives the rational exponent restriction from the laws. This joint charge/energy restriction is used by ground_below, ground_leading and pair_ground_detects_zero.

**Theorem 1.27 (ground_below).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_below`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_below` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for all n,l and rational s strictly below groundPower(mu,nu,n,l), the entire raw coefficient is zero. A hypothetical nonzero charge/monomial coefficient contradicts ground_spectrum and nonnegative natural oscillator energy. Used by mode_below and the charged recurrences.

**Theorem 1.28 (ground_leading).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_leading`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full hypotheses, for every n,l, the full raw coefficient at groundPower equals groundScalar(mu,nu,n,l) smul ground(n+l). Charge projection and the spectrum force oscillator energy zero, hence exponent zero. The scalar can vanish. Used by mode_leading and the charged recurrences.

**Theorem 1.29 (charged_ground_leading).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.charged_ground_leading`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.charged_ground_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D and integral d,m,n, the actual charged action at integer mode -chargedPower(d,m,n)-1 sends ground n to epsilon(D,m,n) smul ground(m+n). Compute the native creation coefficient at zero with the original cocycle. No inverse, rational duality or Lawful field hypotheses. Used by charged_source_recurrence and charged_input_recurrence.

**Theorem 1.30 (charged_ground_above).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.charged_ground_above`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.charged_ground_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,d,m,n and integer j strictly greater than -chargedPower(d,m,n)-1, the charged action at j on ground n is zero. The native creation index is negative. No inverse, duality or Lawful field hypotheses. Used by both charged recurrences.

**Theorem 1.31 (chargedPower_add).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.chargedPower_add`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.chargedPower_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,a,b,m,n,l, chargedPower(a+b,m,n+l)=chargedPower(a,m,n)+chargedPower(b,m,l). Distribute bilinear and coordinate pairings. No I, H or rational duality is required. Used by both charged recurrences.

**Theorem 1.32 (groundPower_source_shift).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower_source_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower_source_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,b, rational mu,nu with G_Q nu=b, and integral m,n,l, groundPower(mu,nu,m+n,l)=groundPower(mu,nu,n,l)+chargedPower(b,m,l). Expand the rational Gram pairing and use physical_pairing_integral. No inverse or Lawful field hypotheses; no duality assumption on mu. Used by charged_source_recurrence and groundPower_input_shift.

**Theorem 1.33 (groundPower_input_shift).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower_input_shift`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower_input_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all D,a, rational mu,nu with G_Q mu=a, and integral m,n,l, groundPower(mu,nu,n,m+l)=groundPower(mu,nu,n,l)+chargedPower(a,m,n). Use groundPower_source_shift with the arguments exchanged and symmetry. No inverse or Lawful field hypotheses; no duality assumption on nu. Used by charged_input_recurrence.

coefficient_charge and ground_spectrum supply the charge and energy restrictions used in ground rigidity. The derivation uses source linearity, Ward specializations, quadratic expansion, actual ground L0 specialization, dual addition and charged leading-index formulas in the proofs named above. current_component uses finite-charge induction. Private lawful_zero, lawful_add and lawful_smul establish the closure properties used to define operatorSpace. The module specifies the full-law space and derives constraints on any element. It proves neither the existence of a nonzero lawful field nor a dimension-one equality, categorical fusion equivalence, physical realization or completion of string theory.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.Fields`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.Lawful`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.chargedPower`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.chargedPower_add`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.charged_ground_above`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.charged_ground_leading`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.coefficient_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.current_component`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.current_ground`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.dual_add`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.energy_ward`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.firstTerm`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower_input_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundPower_source_shift`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.groundScalar`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_L0`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_below`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_charge`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_charge_projection`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_current_ward`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_eigen`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_energy_difference`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_leading`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ground_spectrum`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.leftTerm`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode_add_source`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.mode_smul_source`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.operatorSpace`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.secondTerm`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetIntertwiner.ward`
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetPositiveEnergy](LatticeDualCosetPositiveEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorGroundRigidity](LatticeSectorGroundRigidity.md)
