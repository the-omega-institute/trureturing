# Two spectral levels with arbitrary complex matrix blocks

## Abstract

A finite weighted Gram certificate proves the noncommutative two-level balanced cubic supplier.

**Definition 1.1 (Spectral denominator).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.den`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.den` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set q(r)=r²+r+1; this is positive for every r>0.

**Definition 1.2 (Auxiliary positive polynomial).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.aux`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.aux` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Set a(r)=4r²+7r+4. It enters the finite Gram factorization.

**Definition 1.3 (First divided-difference overlap).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.tau`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.tau` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the normalized spectral values 1,r³, tau(r)=3 sqrt(r)(r+1)/(2q(r)). The first coefficient is (2/3) times the Schur transform with this off-diagonal multiplier.

**Definition 1.4 (Repeated-index remainder).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.kappa`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.kappa` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact rational remainder is r(r-1)²(r²-r+1)(r²+7r+1)/(12q(r)^4). The proof derives it from the finite coefficient kernels and uses its nonnegativity, including r=1.

**Definition 1.5 (Second Gram weight).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gap`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The weight d=(r-1)²(4r²+7r+4)/(4q²) equals 1-tau² and is nonnegative.

**Definition 1.6 (Remaining Gram weights).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramGap`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both remaining weights equal rho=r(r-1)²(r+1)²(5r^4+22r³+36r²+22r+5)/(3q^4(4r²+7r+4)). All weights are nonnegative, without a spectral-gap denominator.

**Definition 1.7 (First coordinate of p).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pv`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This rational square-root coefficient is the v-coordinate of the finite Gram vector p.

**Definition 1.8 (First coordinate of q).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qv`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This rational coefficient is the v-coordinate of the finite Gram vector q and the coefficient of CC* in the upper diagonal block of B.

**Definition 1.9 (Overlap of p with w).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pw`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact coefficient pw equals tau times pv plus d times pc. It is also the coefficient of C*C in the lower diagonal block of B.

**Definition 1.10 (Overlap of q with w).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qw`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact coefficient qw equals tau times qv plus d times qc.

**Definition 1.11 (Second coordinate of p).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pc`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient pc=(3r³+15r²+19r+8)/(q(4r²+7r+4)) has no division by r-1.

**Definition 1.12 (Second coordinate of q).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qc`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qc` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient qc=-sqrt(r)(r-1)(2r²+3r+2)/(q(4r²+7r+4)) also includes r=1 directly.

**Definition 1.13 (Squared length of p).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pn`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational coefficient pn is proved equal to pv²+d pc²+rho. It is independently constrained by 4-tau²-2qv-pn=kappa.

**Definition 1.14 (Squared length of q).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qn`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational coefficient qn is proved equal to qv²+d qc²+rho and satisfies 4-tau²-2pw-qn=kappa.

**Definition 1.15 (Real matrix trace).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.tr`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.tr` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use Re Tr on arbitrary finite square complex matrices. Rectangular cyclic trace identities never commute the matrix factors.

**Definition 1.16 (Normalized block direction).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.direction`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.direction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite index types m,n, let S=[[A,C],[C*,H]], where C is an m-by-n complex matrix. Positivity is imposed on this full block matrix.

**Definition 1.17 (First balanced coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.first`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.first` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L1=(2/3)[[A,tau C],[tau C*,H]]. The proof identifies it with P^-1(P R+R P)P^-1 for the cube-root coefficient R.

**Definition 1.18 (Second balanced coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.second`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.second` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The upper diagonal block is -A²/9-r³(2r+1)CC*/(3q²), the lower diagonal block is -H²/9-(r+2)C*C/(3q²), and the upper off-diagonal block is -sqrt(r)((2r+1)AC+r²(r+2)CH)/(3q²). The lower block retains the reversed ordered products.

**Definition 1.19 (Noncommutative Gram row).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramRow`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row X(v,p,q,w) is [[v A,p C],[q C*,w H]], with four real coefficients and the original ordered matrix products.

**Definition 1.20 (Diagonal Gram row).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramDiag`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramDiag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(v,w)=diag(v I,w I) on the direct sum of the two index types.

**Definition 1.21 (The first Schur transform).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.transport`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T=[[A,tau C],[tau C*,H]]=(3/2)L1. No invertibility of T is assumed or used.

**Definition 1.22 (Actual quadratic kernel).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.balancedQuadratic`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.balancedQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B=-3L2+(3/2)L1². Direct block multiplication identifies it with the symmetrized finite cross moment.

**Definition 1.23 (Finite weighted square).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.squareEnergy`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.squareEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four rows use v=(1,0,0,0), w=(tau,1,0,0), p=(pv,pc,1,0), q=(qv,qc,0,1), with weights (1,d,rho,rho). The energy is the weighted sum of Re Tr((X_j-2V_j W)* S (X_j-2V_j W)), where * means adjoint. The last two V_j vanish. PSD S makes every summand nonnegative, including singular S.

**Definition 1.24 (Normalized spectral root).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.baseRoot`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.baseRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P=diag(I,r I), so Y=P³ has spectral values 1,r³ with arbitrary multiplicities.

**Definition 1.25 (Explicit balancing root).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.inverseRoot`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.inverseRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D=diag(I,r^-1 I)=P^-1 for r>0.

**Definition 1.26 (Cubic coefficient solver).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.solveRoot`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.solveRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse of E ↦ P²E+PEP+EP² divides the diagonal blocks by 3 and 3r² and the off-diagonal blocks by q. These denominators are nonzero for r>0, including repeated levels.

**Definition 1.27 (First cube-root coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootFirst`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootFirst` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R has diagonal blocks A/3,rH/3 and off-diagonal blocks r sqrt(r) C/q and its adjoint. Its linear cubic coefficient is exactly K=baseDirection.

**Definition 1.28 (Second cube-root coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootSecond`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootSecond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q is obtained by solving P²Q+PQP+QP²+PR²+RPR+R²P=0. Its displayed finite block kernels are checked against this equation and against L2.

**Definition 1.29 (Third cube-root coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootThird`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootThird` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U is defined by applying solveRoot to the negative ordered cubic cross terms P(RQ+QR)+RPQ+QPR+(RQ+QR)P+R³. This defines the coefficient before deriving its trace normalization.

**Definition 1.30 (Third balanced coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.third`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.third` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L3=D(PU+UP+RQ+QR)D, formed by squaring the cube-root series. The proof independently derives Tr L3=Tr(L1 L2)-(1/3)Tr L1³+(2/9)Tr S³ from these actual coefficient formulas.

**Definition 1.31 (Positive repeated-index cyclic words).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pairEnergy`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pairEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

E=Re Tr(ACC*)+Re Tr(HC*C). Principal-block positivity and PSD congruence prove E>=0; no rank assumption is made.

**Definition 1.32 (The cubic supplier).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.supplier`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.supplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

F(Z)=Re Tr L3+2 Re Tr(Z L2)+Re Tr(L1 Z²)-(5/48)Re Tr L1³. The matrix coefficients come from the cube-root recurrence, independently of the certificate.

**Definition 1.33 (Linear cube coefficient).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeLinear`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For P=diag(I,rI), define A_P(R)=P²R+PRP+RP². The block denominators prove that this map is injective.

**Definition 1.34 (Quadratic cube cross terms).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeQuadratic`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic cross terms are PR²+RPR+R²P.

**Definition 1.35 (Cubic cube cross terms).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeCubic`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeCubic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cubic cross terms are P(RQ+QR)+RPQ+QPR+(RQ+QR)P+R³; all orders are retained.

**Definition 1.36 (Physical direction in the spectral frame).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.baseDirection`

*Formalization.* `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.baseDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K=diag(I,r sqrt(r) I) S diag(I,r sqrt(r) I). Its off-diagonal blocks are r sqrt(r) C and r sqrt(r) C*, and its lower diagonal block is r³H.

**Theorem 1.37 (Pointwise supplier from the actual cubic recurrences).**

Lean statement: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.supplier_of_cubic_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.supplier_of_cubic_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all finite index types m,n, every r>0, PSD S=[[A,C],[C*,H]], Hermitian Z, and matrices R,Q,U satisfying A_P(R)=K, A_P(Q)+PR²+RPR+R²P=0, A_P(U)+P(RQ+QR)+RPQ+QPR+(RQ+QR)P+R³=0, form L1=D(PR+RP)D, L2=D(PQ+QP+R²)D and L3=D(PU+UP+RQ+QR)D. Then 0<=kappa(r)E/6<=F(Z). The proof identifies the three arbitrary coefficient matrices with the explicit finite spectral kernels using injectivity of A_P. No desired inequality is an input hypothesis.

The exact internal identity is 6F(Z)=kappa(r)E+squareEnergy(Z+L1/2). It follows from the actual third-trace normalization and the independently proved finite Gram moments. The unshifted Gram energy U_G is Tr A³+Tr H³+(2qv+pn)Tr(ACC*)+(2pw+qn)Tr(HC*C). Consequently 4Tr S³-Tr T³-3U_G=3kappa(r)E. The identity includes r=1 and singular directions directly, and uses no pseudoinverse, Sylvester minimization, Mellin-integral premise, rank restriction, commutativity, spectral floor, or trace normalization.

The external target is He–Saunderson–Fawzi, arXiv:2502.05627v1 Conjecture 6.2, journal DOI 10.1007/s10107-025-02314-0 Conjecture 1; see Library/Divergence/he2025operatorconvexity.md. Cubic-series multiplication, cyclic trace, and PSD congruence are classical. This repository certificate is not attributed to that paper, and no literature novelty is asserted. The theorem has an explicit algebraic coefficient-recurrence interface. The actual CFC derivative consumer, finite reindexing, unitary coordinates and common-scale normalization are supplied by HsfBalancedCfcBridge. Triangle-free spectra with more than two levels are not formalized here. Three-distinct-level interactions, independent X,Y, all alpha>2 and the complete continuing HSF conjecture remain open.

The corresponding Reg mirror supplies the typed whole-telescope arena, actual-law bridge, rejected intervention, sensitivity and observational dependence. Source-selection reconstruction and declared-template binding are unfinished under https://github.com/the-omega-institute/trureturing/issues/23103. This is not a declared_validated registration or independent review.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.aux`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.balancedQuadratic`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.baseDirection`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.baseRoot`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeCubic`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeLinear`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.cubeQuadratic`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.den`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.direction`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.first`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gap`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramDiag`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramGap`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.gramRow`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.inverseRoot`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.kappa`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pairEnergy`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pc`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pn`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pv`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.pw`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qc`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qn`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qv`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.qw`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootFirst`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootSecond`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.rootThird`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.second`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.solveRoot`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.squareEnergy`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.supplier`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.supplier_of_cubic_recurrence`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.tau`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.third`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.tr`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfBalancedSpectralCertificate.transport`
