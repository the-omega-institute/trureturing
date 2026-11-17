# Canonical-to-native finite spectral bridge

## Abstract

Exact finite spectral extraction, full raw boundary transport and inverse canonicalization

**Definition 1.1 (Reuse of the canonical core).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.A`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.A` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

A(c) is exactly OpenBoundaryMPSTwoSiteMinimality.core at (c,0,0). The final two canonical boundary coordinates do not affect these matrices. There is no competing canonical core.

**Definition 1.2 (Reuse of the canonical left row).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.L`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

L(c) is the same original left row (c0,1).

**Definition 1.3 (Trace difference).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.h`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.h` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

h=c4-c1.

**Definition 1.4 (Spectral discriminant).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.D`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.D` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

D=h squared plus 4 c2 c3.

**Definition 1.5 (First canonical offset).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t0`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t0` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

t0=c1-c0 c2.

**Definition 1.6 (Second canonical offset).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t1`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

t1=1+c3-c0 c4.

**Definition 1.7 (Diagonal-product numerator).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.U`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.U` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

U=h t0 t1-c2 t1 squared+c3 t0 squared.

**Definition 1.8 (Exact algebraic exclusions).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.Admissible`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For arbitrary five complex coordinates c and complex e, require e squared=D and c2 D U (U+D) nonzero. There is no polynomial-dependent restriction, dimension assumption or assumed gauge conclusion.

**Definition 1.9 (First eigenvalue).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.lam`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.lam` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

lambda=(h+e)/(2 c2).

**Definition 1.10 (Second eigenvalue).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.mu`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.mu` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

mu=(h-e)/(2 c2). Both square-root branches are allowed.

**Definition 1.11 (Canonical spectral frame).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.T`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

T=A0 times the matrix with rows (1,1) and (lambda,mu).

**Definition 1.12 (Actual conjugated core).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.K`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

K=T inverse A0 T. Its entries are named u,v,w,t in row order.

**Definition 1.13 (First conjugated entry).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.u`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.u` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

u=K00, the recovered canonical scalar.

**Definition 1.14 (Second conjugated entry).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.v`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

v=K01.

**Definition 1.15 (Third conjugated entry).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.w`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.w` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

w=K10.

**Definition 1.16 (Fourth conjugated entry).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

t=K11.

**Definition 1.17 (Eigenvalue gap).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.gap`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.gap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

delta=-e/c2 equals mu-lambda.

**Definition 1.18 (Diagonal gauge).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.rho`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.rho` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

rho=Delta/(delta u v), with Delta=-c2.

**Definition 1.19 (Full gauge matrix).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.S`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

S=T diag(1,rho).

**Definition 1.20 (Native trial parameter).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.z`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.z` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

z=Delta/(delta u squared).

**Definition 1.21 (Native first offset).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.offset`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.offset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

alpha=delta v w/Delta.

**Definition 1.22 (Existing native sector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.sector`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.sector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

Use precisely OpenBoundaryMPSInteriorRootRealization.Sector with lambda,mu,a=lambda-alpha. Native G,B and core remain the source of truth.

**Definition 1.23 (Full left boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.nativeLeft`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.nativeLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

l=L S.

**Definition 1.24 (Full right boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.nativeRight`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.nativeRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural N and arbitrary complex two-column R, r=u to the power N times S inverse R. This includes the entire raw core scalar.

**Definition 1.25 (Computed native row normalizer).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.leftNormalizer`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.leftNormalizer` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

K_l has rows l G and l B G. It is computed from the native core and left boundary, not defined by the desired inverse.

**Theorem 1.26 (Spectral frame and entry exclusions).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.spectral_frame`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.spectral_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every admissible c,e, detT=e, L T=(1,1), and M T=T diag(lambda,mu) for M=A1 A0 inverse. The actual K has detK=-c2, ut=c2 U/D and vw=c2(U+D)/D. Thus u,v,w,t and delta are all nonzero. The entry identities use the equation e squared=D, the exact canonical matrices and the actual inverse of T.

**Theorem 1.27 (Exact native core equivalence).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.native_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.native_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every admissible c,e, detS and z are nonzero; the native delta is gap, native alpha is offset, native beta=delta u t/Delta, and delta alpha beta is nonzero. Since beta=mu-a and alpha=lambda-a, beta-alpha=delta. The extracted left row is (1,rho). For each binary symbol, A_i S=u S core_native,i. The same existing native sector is Regular if and only if 1+conjugate(lambda) mu is nonzero. The transfer cross factor is separate from distinct eigenvalues.

**Theorem 1.28 (Every length and arbitrary right boundary).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.raw_amplitude`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.raw_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every admissible c,e, every natural N including zero, and every original R, the entire raw length-N state with canonical A,L,R equals the native state with the existing sector and z and boundaries l=L S and r=u^N S inverse R. A conjugation MonoidHom and List.smul_prod transport every ordered word, then the actual boundary contraction cancels the gauge. No scalar or boundary component is omitted.

**Theorem 1.29 (Measured normalizer and recovered scalar).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.normalizer_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.normalizer_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every admissible c,e, the actual native K_l equals u inverse times S. Its actual inverse gives l K_l inverse=u L; the second entry is exactly u. This follows by multiplying the proved symbol identities by OpenBoundaryMPSTwoSiteMinimality.normalized_rows at (c,0,0), reusing the original canonical row theorem directly.

**Theorem 1.30 (Two cores and both boundaries return exactly).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.canonicalization_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.canonicalization_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every admissible c,e, natural N and arbitrary original R, set J=K_l. For both symbols, u J core_native,i J inverse=A_i. The canonical left row u inverse l J inverse=L. The canonical right column u (u^N) inverse J r=R. Thus the same finite gauge has a proved inverse at the scalar recovered from the actual normalizer.

**Definition 1.31 (Canonical five-complex witness).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessC`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessC` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

c*=(0,0,1/2,0,1).

**Definition 1.32 (Existing native sector).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessSector`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessSector` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

The original native Sector is (lambda,mu,a)=(2,0,1).

**Definition 1.33 (Actual native left row).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessLeft`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessLeft` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

l=(1,1).

**Definition 1.34 (Actual native right column).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessRight`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

r=(1,I). Its complete column is retained.

**Definition 1.35 (Length-dependent canonical right column).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessCanonicalRight`

*Formalization.* `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessCanonicalRight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

R_N=2^N times (1,1+I), for every natural N.

For every natural N, the existing native G is [[1,1],[1,-1]] and B=diag(2,0). The actual leftNormalizer is [[2,0],[2,2]], with inverse [[1/2,0],[-1/2,1/2]]. Thus l K_l inverse=(0,1/2), whose second entry is 1/2. Canonicalization at t_can=1/2 gives exactly both original canonical symbol matrices at c*, the original left row (0,1), and the full right column R_N. This is the numerical application of canonicalization_inverse to the same actual native data, with every length-dependent factor retained.

**Theorem 1.36 (Return to the very same native witness).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.fixed_witness_extraction`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.fixed_witness_extraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural N, c*,e=1 is admissible, D=1, U=-1/2, U+D=1/2. T=[[1,0],[1,1]], K=[[1/2,1/2],[1/2,-1/2]], rho=1, sector=(2,0,1), z=1 and l=(1,1). With R_N extraction returns exactly r=(1,I). With raw R=(1,1+I), it returns exactly (1/2)^N times (1,I). The separate transfer cross factor 1+conjugate(lambda) mu is one.

**Theorem 1.37 (Restore the canonical quotient scale).**

Lean statement: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.fixed_witness_quotient_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.fixed_witness_quotient_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Critch, Andrew; Morton, Jason (2014). *Algebraic geometry of matrix product states*. DOI: [10.3842/SIGMA.2014.095](https://doi.org/10.3842/SIGMA.2014.095). URL: <https://arxiv.org/abs/1210.2812v4>.

*Commentary.*

For every natural N, the existing OpenBoundaryMPSQuotient.positiveBoundary at (c*,sigma=4^N,eta=1+I) equals R_N. The squared modulus of its first entry is 4^N and the ratio of its second to first entry is 1+I. The theorem also states and proves the exact full raw length-N state equality between this canonical positiveBoundary input and the original native G,B,l,r witness. It transports precisely the same native b, retaining the raw scalar.

This supplier preserves the original Ma--Zhang C8 canonical core and left row, with their CC BY 4.0 attribution. It supplies an explicit inverse for a later nonvanishing or dominance argument. It proves no actual-image density, genericity, arbitrary-polynomial descent, realified field norm, positive-environment transport or full C9 result. C9 remains open and solved-open-problem KPI is zero. Static finite algebra adds no dynamics, energy, clock, physical inverse or thermodynamic claim.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.A`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.Admissible`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.D`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.K`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.L`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.S`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.T`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.U`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.canonicalization_inverse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.fixed_witness_extraction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.fixed_witness_quotient_boundary`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.gap`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.h`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.lam`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.leftNormalizer`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.mu`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.nativeLeft`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.nativeRight`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.native_extraction`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.normalizer_inverse`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.offset`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.raw_amplitude`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.rho`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.sector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.spectral_frame`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t0`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.t1`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.u`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.v`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.w`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessC`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessCanonicalRight`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessLeft`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessRight`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.witnessSector`
- Truth anchor: `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSSpectralExtraction.z`
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorRootRealization](OpenBoundaryMPSInteriorRootRealization.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQuotient](OpenBoundaryMPSQuotient.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSTwoSiteMinimality](OpenBoundaryMPSTwoSiteMinimality.md)
