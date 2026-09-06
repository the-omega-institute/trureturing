No new off-line zero, prime-gap bound, RH proof, larger positivity window,
canonical source admission or frozen-state transition is asserted.

## [PR #5895] REAL_STRUCTURE_AND_UNIFORM_TRANSVERSE_ZERO_EXCLUSION

### 1. Research target and current literature

This increment continues the actual-ground/prolate comparison in Connes,
Consani and Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1, Section 8.
The author-hosted revised volume and its Section 8 were checked on 2026-09-06.
The explicit-model limit in Lemma 7.3 and the genuine lowest-mode comparison
remain distinct. This increment gives a structured robustness certificate
at one fixed window; it does not claim the unbounded-scale comparison.

The methodological comparison is Gnazzo, Guglielmi, Poloni and Sicilia,
Structured distance to singularity as a nonlinear system of equations,
arXiv:2603.05419v1 (2026-03-05), Section 2.2, equations (12)-(14). Their inner
problem is a classical minimum-norm linear solve preserving the allowed
perturbation structure. Here the structure is a real even function space,
and a complex zero gives two real equations. Their nonlinear matrix Newton
algorithm is not used, and the elementary least-norm formula is not new.

Connes and van Suijlekom, Quadratic Forms, Real Zeros and Echoes of the
Spectral Action, arXiv:2511.23257v1, already supply a qualitative real-zero
mechanism for their actual operator class under its analytic, simplicity
and evenness hypotheses. The present finite-window computation does not
claim priority for real zeros of a Weil ground transform. Its output is a
quantitative margin stable under every allowed real even norm-ball error.

Cross-PR readback included loning's #5326 boundary/certificate distinctions,
the user's #5882 complex readout-ball work, and the new #5602 directional and
prolate-model certificates. We reuse the existing Rayleigh owner and do not
repeat #5882's complex one-readout solve or #5602's fixed-window root count.

A chronological correction to the previous appendix: #5602 at
`d6f6e53737a9a7ad3ea1aa00414f91136be5fba4` now contains an executed fixed-scale
prolate comparison, `prime3_prolate_model_certificate.json`. It reports an
aligned unit true-prolate-to-candidate bound 113/100000, with paper spectral
projection/domain identifications still explicit. Thus the fixed-scale
model comparison is no longer merely a plan. The unbounded-scale comparison
remains open. That concurrent result is not this session's work and was not
recomputed here.

### 2. Why the real structure must be proved, rather than asserted

A small norm distance to a real even candidate does not make an arbitrary
complex perturbation real or even. Let iota,A:D->H be complex-linear maps
on the actual operator domain, k the candidate and p,q two eigenvectors
with the same real eigenvalue lambda<T and

    <iota(k),iota(p)>=<iota(k),iota(q)>=1.

If candidate-orthogonal domain vectors have energy at least T times their
squared norm, the difference p-q is simultaneously an eigenvector below T
and candidate-orthogonal. The existing nonzero-overlap theorem excludes a
nonzero Hilbert-space difference. Consequently iota(p)=iota(q).

Let J on D and C on H be compatible sigma-semilinear maps, with

    iota(Jf)=C(iota(f)),       A(Jf)=C(A(f)),
    <Cx,Cy>=sigma(<x,y>),     Jk=k,     sigma(lambda)=lambda.

Then Jp has the same normalized eigenvalue equations, so C(iota(p))=iota(p).
For sigma=complex conjugation this gives reality. For sigma=identity and C
the spatial reflection it gives evenness. No bounded extension, complete
spectral expansion, or prior simplicity assertion is used. Actual domain
commutation with conjugation/reflection still belongs to the Weil realization.

`ProjectiveModeSymmetry` proves this uniqueness, the semilinear fixedness
statement, and its application to the actual p=u/<iota(k),iota(u)> constructed
using the existing nonzero-overlap theorem.

### 3. Exact least energy for a real error to satisfy two readouts

Work in a real inner-product space. Let b,c be the two projected Riesz
vectors and set

    U=||b||^2, V=||c||^2, C=<b,c>, Delta=UV-C^2>0.

For target readouts x,y define

    w0=((Vx-Cy)/Delta)b+((Uy-Cx)/Delta)c,
    E(x,y)=(Vx^2-2Cxy+Uy^2)/Delta.

Direct substitution gives <b,w0>=x, <c,w0>=y and ||w0||^2=E(x,y).
Every other feasible w satisfies the exact identity

    ||w||^2=E(x,y)+||w-w0||^2.

Therefore

    exists real w, ||w||^2<=e, <b,w>=x, <c,w>=y
       iff E(x,y)<=e.                                    (RT1)

If b,c are orthogonal to the candidate, w0 is also orthogonal. The witness
cannot exploit a forbidden candidate direction. The determinant-positive
hypothesis is explicit; this inverse formula is not applied at a rank drop.
A separate dual theorem needs no rank hypothesis: any s,t such that

    (s*x+t*y)^2 > e*||s*b+t*c||^2

excludes simultaneous attainment. All these statements have actual proof
bodies in `RealReadoutCancellation` and use standard real inner products.

For the Fourier transform of a real even function at z=x+iy, the two
unprojected real kernels are

    R_z(t)=cos(xt)cosh(yt),     I_z(t)=-sin(xt)sinh(yt).

For a unit real candidate k, subtract each kernel's component along k.
Writing A=F(k)(z), the target pair for a zero is (-Re A,-Im A).
The minimum E(-Re A,-Im A) is the exact structured cancellation cost over
the real candidate-orthogonal error space. It is not the distance to an
actual eigenvector of a prescribed operator.

### 4. Full Gram integrals and the actual pointwise comparison

Let L=log(3), a=L/2 and I=[-a,a]. Define

    H(z)=sinh(Ly)/(2y)+sin(Lx)/(2x),
    J(z)=a+sin(Lz)/(2z).

The removable values are taken continuously. Direct integration gives

    integral R_z^2=(H+Re J)/2,
    integral I_z^2=(H-Re J)/2,
    integral R_z I_z=Im J/2.

After projection along k,

    U=(H+Re J)/2-(Re A)^2,
    V=(H-Re J)/2-(Im A)^2,
    C=Im J/2-Re A*Im A.                                  (RT2)

These are full-interval integrals, not a Fourier truncation of the possible
error w. `RealTransverseReadout` constructs continuous kernels as actual
Mathlib real L2 elements and proves their integral, mixed-Gram and norm
identities. The trigonometric specialization above and the arithmetic Weil
form/domain identification remain explicit paper analysis.

The existing 129 integer candidate and existing energy fields give

    e=44669457/489267186193 < 1/10000.

No eigensolver or zeta-zero locations enter this computation. The input
candidate literal and four rational fields were read from the remote files,
then the exact semantic projections were hashed. The computation does not
attest the complete upstream file bytes or rerun their spectral verifier.

Directed intervals give, at z=14+i/4,

    E_real > 0.002322838158732562,
    E_real/e > 25,
    E_complex < 0.000016023090139011 < e.                  (RT3)

Thus the old exact complex error ball permits cancellation, whereas the
real ball with the same norm budget excludes it. The previous complex-ball
statement remains mathematically correct. Its inference about what a
physical real mode can do must retain the allowed scalar structure.

The limitation at z=20+i/4 is also retained:

    E_real approximately 0.000051342801868446 < e.

The real error ball is still large enough to cancel there. This does not
assert a zero of the true ground transform. Improving decimal precision
alone cannot eliminate a genuinely feasible ball perturbation.

### 5. Removing the coordinate singularity at the real axis

The raw imaginary kernel tends to zero as y->0. Its Gram determinant then
vanishes quadratically, even when the transverse information is nonzero.
For y!=0 divide the second equation by y and use

    T_f(x,y)=Im(F(f)(x+iy))/y,
    h_(x,y)(t)=-sin(xt)*sinh(yt)/y.

Define h_(x,0)(t)=-t*sin(xt). Then T_f(x,0)=F(f)'(x) for real even f.
The existing real-cost expression is unchanged under nonzero rescaling of
the second equation; `rescaled_pair_cost` proves that identity explicitly.

When the rescaled Gram is nondegenerate, its continuous limit is the
least energy to enforce F(k+w)(x)=0 and F(k+w)'(x)=0 simultaneously.
This is the local double-zero constraint associated with the escape of a
conjugate pair from the real axis. The limiting interpretation is paper
analysis here; no unproved rank condition is suppressed.

### 6. A full near-axis tube, using one transverse dual constraint

For |t|<=a and |y|<=b, the mean-value bound for sinh gives

    |sinh(yt)/y| <= |t|cosh(ab),

including its continuous value at y=0. Consequently

    ||h_(x,y)||_2 <= cosh(ab)*sqrt(2a^3/3).                 (RT4)

For every real even error w with ||w||_2<=r,

    T_(k+w)(x,y) >= T_k(x,y)-r*cosh(ab)*sqrt(2a^3/3).      (RT5)

This uses the full L2 norm. It is not restricted to the candidate's 129
Fourier coordinates and does not even need the error's orthogonality to k.
The general uniform-margin transport is proved in
`RealTransverseReadout.transverse_region_nonvanishing`.

The finite candidate uses the same translated basis as the existing cert:

    V_n(t)=(-1)^n exp(2*pi*i*n*t/L)/sqrt(L),
    k_n=p_n/sqrt(sum p_j^2),
    sum p_j^2=1208925819614761052253583.

Put u_n=x-2*pi*n/L. Away from its removable sinc poles the actual finite
Fourier formula yields the nonsingular expression

    T_k(x,y)=2/sqrt(L) * [
      a*cos(ax)*sinhc(ay)*sum_n k_n*u_n/(u_n^2+y^2)
      -sin(ax)*cosh(ay)*sum_n k_n/(u_n^2+y^2)],             (RT6)

where sinhc(v)=sinh(v)/v with sinhc(0)=1. This expression is even in y.
The region below contains no unresolved rational Fourier denominator.

Use the 64 closed rational boxes

    X_i=[14+i/64,14+(i+1)/64],             0<=i<16,
    Y_j=[j/8,(j+1)/8],                    0<=j<4.

They cover [14,57/4] times [0,1/2] exactly. Equation (RT6) is evaluated on
whole interval boxes, not at their centers. The sinhc enclosure keeps terms
through v^22/23! and bounds the positive remainder by

    (1/3)^24 / 25! / (1-(1/3)^2/(26*27)),

valid for |v|<=1/3. This also covers y=0 without division by zero.

The executed interval inequalities are

    T_k(x,y) > 43/5000 on every box,
    cosh(a/2)*sqrt(2a^3/3) < 173/500,
    r=1/100.

Since

    43/5000-(173/500)*(1/100)=257/50000 > 1/200,

every real even error in this ball satisfies

    |Im(F(k+w)(x+iy))| > |y|/200
    for 14<=x<=57/4 and 0<|y|<=1/2.                       (RT7)

Thus there are no nonreal zeros in this entire tube, including arbitrarily
small nonzero ordinates. On the axis the continuous transverse value is a
positive real derivative, so any real zero in this interval is simple and
there can be at most one. This does not itself establish that a zero exists.
The concurrent directional certificate in #5602 supplies a separate actual
fixed-window root count; it was not recomputed or appropriated here.

### 7. Scope of the computation and the formal sources

The three new Lean modules have nineteen public definitions/theorems and
nineteen same-path Scribe handles. They prove domain eigenmode symmetry,
exact real cancellation costs, the actual generic continuous-kernel L2
identities and uniform-margin transport. No new axiom, sorry or admit is
introduced. Lean elaboration, transitive axiom reports and Scribe emission
were not executed; all new source remains Candidate.

The number-theoretic spectral enclosure and its domain realization remain
upstream analytic inputs. The concrete cosine/sinh kernel specialization,
its mean-value bound, the finite sinc identity and the interval arithmetic
engine are not all kernel-replayed in this increment. Equations (RT2)-(RT7)
are a detailed paper/interval certificate, distinct from the generic Lean
statements. This division is intentional and does not label the whole tube
as a completed Lean theorem about the canonical Weil operator.

New executable files in `research/weil_ground_mode/`:

    certify_prime3_real_transverse.py
    prime3_real_transverse_certificate.json
    test_real_transverse.py
    real_transverse_validation.json

The output records exact rational outward roundings of all 64 box floors.
Those roundings are computed from exact binary interval endpoints, not from
displayed floating-point approximations. The runtime used mpmath 1.3.0.
Input hashes identify the candidate integer list and four energy fields,
not the full upstream source. Changing either mathematical input is rejected.

Executed checks: 797 full-rank real examples and energy decompositions,
2,391 rescalings, 797 candidate-orthogonal witnesses, 100 exact complex-phase
normalizations, 50 real-versus-complex separations, and two singular Gram
rejections. Directed-interval replays at 50 and 90 digits passed; candidate,
energy and precision mutations were rejected. Ordinary and optimized Python
runs passed. These are single-author checks, not an independent review.

### 8. Consequence for the open-problem strategy

The complex-ball obstruction at 14+i/4 is removed by the actual real error
structure, without improving the spectral enclosure. The quantitative
resource is the transverse derivative signal divided by its real Riesz
norm. The vanishing raw imaginary signal near the axis must not be mistaken
for vanishing information.

This is still one fixed window. For a genuine unbounded-scale argument one
must control the same candidates and their symmetry/domain realization,
their prolate comparison, and uniform structured readout margins. A finite
list of successful scales does not prove the needed limit. The real-ball
failure at 20+i/4 further motivates retaining the genuine eigenvalue and
energy-direction equations when a norm-only certificate is insufficient.

No new RH proof, off-line zeta zero, maximal positivity window, globally
simple Xi zeros, or all-scale real-zero/convergence theorem is claimed.

Primary references checked in this round:

- Connes, Consani, Moscovici, Zeta Spectral Triples,
  https://arxiv.org/abs/2511.22755 ; Section 8 and Lemma 7.3.
- Connes, van Suijlekom, Quadratic Forms, Real Zeros and Echoes of the Spectral
  Action, https://arxiv.org/abs/2511.23257 .
- Gnazzo, Guglielmi, Poloni, Sicilia, Structured distance to singularity as a
  nonlinear system of equations, https://arxiv.org/html/2603.05419v1 ;
  Section 2.2, equations (12)-(14), and the stated rank-drop caveat.
