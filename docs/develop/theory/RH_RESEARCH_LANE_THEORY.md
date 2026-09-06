参考：

- Connes, Consani, Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1, Sections 3, 4, 7, 8.
- Connes, van Suijlekom, Quadratic Forms, Real Zeros and Echoes of the Spectral Action, arXiv:2511.23257v1, (11), Theorems 5.6 and 6.1. The matrix and theorem pages were inspected as PDF images.
- Suzuki, Weil's quadratic form via the screw function, arXiv:2606.09096v1, Lemma 3.1 and Sections 3.2, 4.1.
- Connes, Consani, Spectral triples and zeta-cycles, Enseign. Math. 69 (2023), 93-148; arXiv:2106.01715v1, Lemma 2.2 and Proposition 2.3. The arXiv text and the publisher bibliographic record were checked.
- Marcus Chuk, Weil positivity in compact windows: certified two-sided bounds and a Landau-Widom decay law, arXiv:2608.24827, original abstract only in this round.

## [PR #5602 / PR #5065] PROJECTIVE_RAYLEIGH_TO_FINITE_ROUCHE_CERTIFICATES

### Mathematical scope

Candidate source increment, 2026-09-06. The two Lean owners and their two
canonical Scribes were delivered in PR #5895, commit
`a3a735c0aec1c5159cfd37a4bc44f13997d9aecf`. This section extends the existing
`docs/develop/theory/RH_RESEARCH_LANE_THEORY.md`; it does not replace any
previous text. No Lean compilation, axiom audit or admission is claimed.
The earlier reviewed ground-mode branch is
`f3646121b6880735dfeb0319f4a7d8973c32d0be`; the reviewed Burnol branch is
`76e2068b7362e46cbaf9769d9a25cf6e6745e769`.

The mathematical goal is the second missing step of Connes, Consani and
Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, Section 8: quantitatively
compare the true lowest Weil mode with the explicit prolate-derived candidate.
Their Lemma 7.3 concerns the explicit candidate's transform. It does not
identify the actual lowest mode with that candidate. Their Section 8 also
retains the simple-even lowest-mode obligation.

This increment formalizes an error-transport result and a finite boundary
criterion. It does not solve either all-scale obligation. In particular the
BPT scalar zero-tail premise on the Burnol branch remains unresolved here.

### 1. What the cross-PR inspection changed

Loning's PR #5296 isolates boundary transversality from a transfer spectral
gap. PR #5326 proposes rectangle Rouche certificates and highlights the cost
of obtaining a determinant lower bound from many singular values. Both PRs
are theory increments, so their proposed global transfer identifications are
not used as Lean assumptions or asserted as established results.

The concrete reused theorem is the existing
`D5.S3.Weil.ZetaAnalytic.RoucheZeroCount.rectangle_zero_count_eq_of_norm_sub_lt`,
read at the ground-mode branch. It compares analytic multiplicity sums of
actual functions on a rectangle, under a strict boundary inequality and the
exact finite zero catalogs required by that API.

PR #5602 supplies a much more direct analytic application than an arbitrary
new transfer representation: actual arithmetic Weil form computations and
an existing real-domain Rayleigh enclosure. Its sharper complex/projective
estimate was recorded only on paper. That is the first proof gap closed by
the present Candidate source.

PR #5562 contains scaled Schur row estimates. Those can improve how an
actual coercivity budget is certified. They are not substituted for a
concrete infinite-complement certificate in the present theorem.

### 2. Linear domain and a nonzero overlap

Let D be a complex vector space, H a complex inner-product space, and

    iota, A : D -> H

complex-linear maps. A is the action on its domain. No extension of A to an
everywhere-defined bounded endomorphism is made. Write

    q(f) = Re <iota(f), A(f)>.

Assume symmetry on this domain, norm(iota(k))=1, iota(u) nonzero, and

    A(u) = lambda iota(u),     ell <= lambda < T,
    q(k) <= U < T,
    q(f) >= T norm(iota(f))^2 whenever <iota(k),iota(f)>=0.

The selected eigenpair and the domain/coercivity properties remain inputs.
The theorem does not manufacture a ground eigenvector.

Set alpha=<iota(k),iota(u)>. If alpha were zero, applying the complement
inequality to u would give T norm(iota(u))^2 <= lambda norm(iota(u))^2,
contradicting lambda<T and iota(u) nonzero. Hence alpha is nonzero.

There is no normalization hypothesis on u. Arbitrary nonzero complex phase
and amplitude of an eigenvector therefore cause no denominator ambiguity.

### 3. Exact projective energy identity

Put p=alpha^(-1)u and w=p-k. The candidate normalization gives

    <iota(k),iota(p)>=1,       <iota(k),iota(w)>=0.

Linearity preserves the eigenvalue equation for p. Taking its inner product
with k and with w, and using symmetry, gives the exact identity

    q(w) = lambda norm(iota(w))^2 + q(k) - lambda.

Both complex mixed terms are retained in this derivation. This is a
classical two-dimensional Rayleigh identity, not a new number-theoretic law.
The comparison literature is Zhu, Argentati and Knyazev, *Bounds for the
Rayleigh quotient and the spectrum of self-adjoint operators*, SIAM Journal
on Matrix Analysis and Applications 34 (2013), 244-256, Section 3, especially
the two-dimensional reduction and equation (3.1). Their paper is formulated
for bounded self-adjoint operators; the proof here works directly on D and
does not invoke that bounded-operator hypothesis for the Weil realization.

Writing e=norm(iota(w))^2, complement coercivity yields

    (T-lambda)e <= q(k)-lambda <= U-lambda.

Since e>=0 and T-lambda>0, q(k)>=lambda is a consequence. It is not a
separate assumption. Since U<T, the same inequality gives e<1.

Now ell<=lambda and e<=1 imply

    (T-ell)e
      = (T-lambda)e + (lambda-ell)e
      <= U-lambda + lambda-ell
      = U-ell.

Therefore

    norm(iota(u/alpha-k))^2 <= (U-ell)/(T-ell) < 1.

The denominator is T-ell. The existing real estimate with T-U is retained
unchanged; its proof is not duplicated or silently relabeled.

### 4. Sharpness and the exact fixed-window arithmetic

For a diagonal two-mode operator diag(lambda,nu), nu>lambda, take a unit
candidate k=(c,s exp(i theta)), c^2+s^2=1 and c nonzero. The ground eigenline
is the first coordinate and the exact candidate-orthogonal threshold is

    T=lambda s^2+nu c^2,       mu=q(k)=lambda c^2+nu s^2.

For U=mu, ell=lambda, and s^2<c^2, the new bound is attained:

    norm(u/<k,u>-k)^2=s^2/c^2=(mu-lambda)/(T-lambda).

The independent exact-arithmetic development check exercises 1,200 such
complex cases, including non-unit eigenvectors and five complex scalings.
These checks are not Lean proofs or numerical evidence about zeta zeros.

The actual remote JSON `prime3_refined_certificate.json` reports

    ell=103/2000000000,
    U=560909/10000000000000,
    T=1/200000.

This increment verifies, by rational arithmetic and a Candidate Lean proof,

    (U-ell)/(T-ell)=15303/16495000 < (61/2000)^2.

The constant was already present in the remote certificate. It is not a new
or sharper numerical enclosure produced by this continuation. The interval
verifier and its full-space Fourier/domain argument were not replayed here.
The corresponding norm radius is conditional on those analytic premises.

### 5. Transport through actual linear observations

Let L_z : H -> C be continuous complex-linear functionals. The candidate
readout is g(z)=L_z(iota(k)); the projective eigenmode readout is
f(z)=L_z(iota(p)). Suppose norm(L_z)<=K on a boundary Gamma. Then

    |f(z)-g(z)| <= K norm(iota(w)).

No determinant is introduced at this stage. The observation norm and the
boundary floor are separate quantities; neither follows from the spectral
gap alone.

Let S be a finite set of boundary samples and suppose every z in Gamma lies
within distance h of a sample. Suppose additionally

    |g(t)|>=m                  for every t in S,
    |g(z)-g(t)|<=L dist(z,t)   for the covered points.

Then the whole boundary satisfies

    |g(z)|>=eta,      eta=m-Lh.

The proof uses the reverse triangle inequality. Mere positivity at sampled
points would not establish this conclusion without coverage and variation.

Combining this with the variational enclosure gives the acceptance test

    eta>0,
    K^2 (U-ell) < eta^2 (T-ell).

All operations in the last inequality are rational when the five certified
budgets are rational. Square-root evaluation is unnecessary.

### 6. Actual rectangle zero counts

Assume the actual f and g are analytic on a neighborhood of the closed
rectangle and provide the exact finite zero catalogs required by the
existing rectangle theorem. The preceding acceptance test proves

    |f(z)-g(z)|<|g(z)| on the entire rectangle boundary.

The existing owner then gives

    sum_{rho in Z_f} analyticOrderNatAt(f,rho)
      = sum_{rho in Z_g} analyticOrderNatAt(g,rho).

The Candidate theorem `rectangle_zero_count_eq_of_projective_rayleigh`
composes the operator-domain proof, finite mesh proof and this existing
analytic theorem. It does not assume the final boundary inequality as a
premise. Analyticity, linear-observation bounds, mesh coverage/variation,
and the variational operator hypotheses are still explicit.

For a synthetic two-dimensional regression with A=diag(0,4), k=(12/13,5/13)
and L_z(v)=z v_1+v_2, the sample rectangle is [-2,2]+i[-2,2]. A 128-point
mesh admits h=1/16, L=12/13, m=19/13, K=3. Thus eta=73/52 and the exact
squared-budget slack is 39744/28561>0. The two linear polynomials have zeros
0 and -5/12, respectively, both inside the rectangle. This checks a
nonvacuous instance of the budget; it is explicitly not a Weil instance.

### 7. Fourier application and the unresolved scale limit

For L2 functions supported on [-a,a], the usual unnormalized Fourier
readout satisfies, by Cauchy-Schwarz,

    |F(f)(z)| <= sqrt(2a) exp(ab) norm(f)_2,   |Im z|<=b.

One can sharpen its squared norm to integral_{-a}^a exp(2 Im(z)t) dt, with
value 2a at Im(z)=0. A concrete bundled L2 Fourier functional, its analyticity
and these norm bounds have not been constructed in the new Lean owners.
The generic readout input is not silently identified with that functional.

With an explicitly fixed scalar normalization c_a, a sufficient estimate
for controlling the spectral part of the transform error is

    |c_a| sqrt(2a) exp(ab) sqrt((U_a-ell_a)/(T_a-ell_a)) -> 0

for every b<1/2. Any z-dependent zero-free factor has its own sup-norm cost
and cannot be silently absorbed into a scalar c_a.

There is also a second approximation problem: the numerical dyadic candidate
k_a in PR #5602 has not been identified with the explicit prolate candidate
in Connes--Consani--Moscovici. The complete transform comparison has three
separately controlled terms:

    actual mode -> certified numerical candidate,
    numerical candidate -> correctly normalized prolate candidate,
    prolate candidate -> Xi.

Their Lemma 7.3 addresses the last arrow. The present variational proof
addresses a quantitative interface for the first. It does not close the
middle arrow or prove the stated rate on an unbounded sequence of scales.
The fixed a=log(3)/2 certificate establishes no such scale family.

For the Burnol branch, the analogous independent open input is still the
actual multiplicity-weighted scalar zero-tail estimate. Brent--Platt--
Trudgian, Math. Comp. 90 (2021), 2923-2935, Theorem 1, equations (1)-(3),
provides the reference analytic estimate. This continuation does not replace
that proof by the unrelated Rayleigh identity.

### 8. Source anchors and references

Candidate owners:

- D5/S3/Weil/ZetaBridge/WeilProjectiveRayleighCapture.lean
- D5/S3/Weil/ZetaBridge/WeilProjectiveRoucheBudget.lean

Both have paired Scribe sources using `StatementSource.FromLean()` for every
public theorem. No generated Blueprint Markdown is authored by this package.

Primary references:

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*,
  arXiv:2511.22755v1, Lemma 7.3 and Section 8.
  https://arxiv.org/html/2511.22755v1
- P. Zhu, M. E. Argentati, A. V. Knyazev, *Bounds for the Rayleigh quotient
  and the spectrum of self-adjoint operators*, SIAM J. Matrix Anal. Appl.
  34 (2013), 244-256, Section 3, equation (3.1), DOI 10.1137/120884468.
  https://arxiv.org/abs/1207.3240
- R. P. Brent, D. J. Platt, T. S. Trudgian, *Accurate estimation of sums over
  zeros of the Riemann zeta-function*, Math. Comp. 90 (2021), 2923-2935,
  Theorem 1, equations (1)-(3), DOI 10.1090/mcom/3652.

This work supplies proof scripts for a classical variational estimate and
its analytic certificate transport. It claims no new prime bound, larger
certified support window, actual off-line zero, all-scale simple-even theorem,
prolate identification, convergence to Xi, or proof of RH.


### 9. Final concurrent-PR readback

The final PR #5602 readback was
`fa7e4acb41f7a9cbdcd1164dc1fc96d3fd43faff`. It adds the source
`WeilEvenFourierObservationTail.lean` (blob
`ed27b739935d3e944e6081cf7324626a13fec388`). Its actual theorem proves absolute
convergence and an N^(-3) squared-norm budget for the defined complex-frequency
response of a square-summable even exterior coefficient sequence, in its
specified pole-free frequency band. The source explicitly retains its L2
Fourier identification as a separate paper bridge. It is not a scalar sum
over the zeros of zeta, so it does not discharge the BPT premise of #5065.

This source can supply a more tailored observation budget than a global
L2-to-Fourier bound once its identification is formalized. The present
readout-norm interface retains that input explicitly and does not assert it
has already been derived from this new owner. None of these concurrent
changes overlaps the two Candidate owner paths in the present package.


## [PR #5895] JOINT_NORMALIZED_FOURIER_READOUT_DISK

### 1. The concrete missing step and the new uncertainty object

This continuation addresses the normalization part of the second missing
step in Connes, Consani and Moscovici, *Zeta Spectral Triples*,
arXiv:2511.22755v1, Section 8. A controlled eigenvector line still needs a
controlled scalar normalization before its Fourier transform can be compared
with the explicit prolate candidate. The latter candidate's convergence in
Lemma 7.3 does not establish the genuine lowest-mode comparison.

The preceding projective Rayleigh theorem constructs p=u/<k,u>, where k is
a unit candidate and u is a nonzero selected eigenvector. It supplies

    p=k+w,       <k,w>=0,       ||w||^2<=e,
    e=(upper-lower)/(threshold-lower).

This continuation determines the exact image of an error ball under a pair
of affine complex readouts followed by division. Numerator and denominator
share the same w. Their correlation must be retained. The algebraic tools
are classical: Cauchy-Schwarz, the minimum-norm solution of one scalar linear
equation and completion of a complex square. No mathematical priority,
new spectral enclosure or all-scale convergence result is claimed.

New candidate source:

    D5/S3/Weil/GroundMode/NormalizedReadoutDisk.lean

Its eight public declarations have a matching canonical Scribe. The source
is logically reviewed but has not been elaborated by Lean in this runtime.
The proof statements and all computational output must retain that status.

### 2. Exact affine-ratio range, with an explicit attaining witness

Let b,c be vectors in an arbitrary complex inner-product space H. The
inner product is conjugate-linear in its first entry. Fix complex d,a and
a real e>=0. For ||w||^2<=e define

    R(w) = (a+<c,w>)/(d+<b,w>).

Assume the strict anchor margin

    e ||b||^2 < |d|^2.

Cauchy-Schwarz gives |<b,w>|^2<=e||b||^2. Thus the denominator is nonzero
throughout the ball. The stronger uniform modulus floor is

    |d+<b,w>| >= |d|-sqrt(e||b||^2).

For every complex r, the exact range characterization is

    (exists w, ||w||^2<=e and R(w)=r)
      iff |rd-a|^2 <= e ||c-conj(r)b||^2.                    (NR1)

Necessity follows by rearranging the actual ratio equation as

    <c-conj(r)b,w> = rd-a

and applying Cauchy-Schwarz. For sufficiency put s=c-conj(r)b. If s=0,
(NR1) forces rd-a=0 and w=0 works. Otherwise choose the explicit vector

    w = (rd-a)/||s||^2 * s.

Then <s,w>=rd-a and ||w||^2=|rd-a|^2/||s||^2<=e. The already proved
anchor margin justifies division. This proof includes e=0 and degenerate
one-point images; no inverse or witness oracle is an algorithm input.

Exactness here is with respect to the complex Hilbert error ball. The
errors of a particular Weil eigenvector obey additional equations, so the
same disk is an enclosure for them. Its attainability is not a claim that
every point is realized by an actual Weil ground mode.

### 3. The correlated disk and its division-free certificate

Write

    U=||b||^2,     V=||c||^2,     C=<c,b>,
    D=|d|^2-eU > 0,
    B=a*conj(d)-eC,
    S=|B|^2-D*(|a|^2-eV).

The exact disk is

    |D r-B|^2 <= S.                                         (NR2)

Its ordinary center is B/D and its squared radius is S/D^2. Nonnegativity
of S follows, for example, by applying the equivalence to w=0. No numeric
square root is required to replay the membership inequality.

The identity used by the Lean proof is

    |D r-B|^2-S
      = D*(|rd-a|^2-e||c-conj(r)b||^2).

Expanding the radius numerator gives an independently checked formula:

    S=e*(|d|^2 V+|a|^2 U-2 Re(d*conj(a)*C)
          -e*(UV-|C|^2)).                                  (NR3)

The complex covariance C and its Gram determinant UV-|C|^2 remain present.
Treating numerator and denominator uncertainties independently discards
precisely this information. At identical readouts the disk is the single
point r=1, whereas separate triangle estimates can still be positive.

### 4. Projected Riesz data for the actual normalized mode

Let L_j(f)=<h_j,f>, d=L_0(k), a=L_1(k), with ||k||=1. Define the explicit
projected Riesz vectors

    b=h_0-<k,h_0>k,       c=h_1-<k,h_1>k.

For the actual w orthogonal to k, these projections preserve both error
readouts. Their Gram data satisfy

    U=||h_0||^2-|d|^2,
    V=||h_1||^2-|a|^2,
    C=<h_1,h_0>-a*conj(d).                                 (NR4)

The new source proves these three identities. It also composes (NR2) with
the existing projective Rayleigh enclosure, so the new eigenmode consumer
uses the actual variational hypotheses rather than accepting a final norm
error as an unexplained oracle. It concludes that L_0(p) is nonzero and
that the actual L_1(p)/L_0(p) belongs to the disk.

Multiplying u by any nonzero scalar leaves this quotient unchanged. The
normalization is therefore defined on the actual eigenline. Its certified
anchor remains a separate mathematical condition; it is not inferred just
from a simple eigenvalue or a spectral gap.

### 5. A real candidate, a fixed basis convention and explicit Fourier Gram data

The numerical consumer reads the existing 129 integers in
`research/weil_ground_mode/certify_prime3_refined.py` as AST literals. The
whole source Git blob is

    a8690fc54e79d1a80b12aeca2ce4837bb9e585af.

It reads the existing Neumann-weighted energy record, Git blob

    bee31b4b002be2c1cff78a53689232a5d87662b5.

Both complete local input byte strings were reconstructed from the remote
readbacks and their Git blob hashes checked before this computation. The
input source is not imported or executed. No eigensolver or zero positions
enter the new consumer, and the upstream spectral verifier is not rerun.

Let L=log(3), I=[-L/2,L/2]. The actual basis inherited from the paper's
(2.6), (3.17) and (3.21) is

    V_n(t)=(-1)^n exp(2*pi*i*n*t/L)/sqrt(L).

The sign (-1)^n is required by translation from [0,L]. It agrees with this
volume's existing Cauchy-response convention. For even functions the two
Fourier sign conventions coincide. With the negative-exponential convention
and away from removable sinc poles,

    F(V_n)(z)=2 sin(Lz/2)/(sqrt(L)*(z-2*pi*n/L)).

The integer coefficient energy is exactly

    sum_n p_n^2 = 1208925819614761052253583.

The unit candidate uses k_n=p_n/sqrt(sum p_n^2), not the unnormalized dyadic
vector. In particular p_0=-843813904619 and

    d=F(k)(0)=sqrt(L)*p_0/sqrt(sum p_n^2).

On the even L2 space the full Fourier Riesz Gram has, for z=x+iy,

    ||h_0||^2=L,
    ||h_z||^2=sinh(Ly)/(2y)+sin(Lx)/(2x),
    <h_z,h_0>=2 sin(Lz/2)/z.                                (NR5)

The quotients have their continuous values at x=0, y=0 and z=0. These are
integrals of |cos(zt)|^2 and cos(zt) over I. Equations (NR4)-(NR5) determine
U,V,C without an infinite coefficient truncation. Their identification with
the actual bundled L2/form-domain objects remains a paper bridge, as in
the preceding actual Weil certificate. It is not established by parsing a
JSON report or by the abstract Hilbert-space theorem alone.

### 6. Executed directed-interval result

The newer energy numbers are

    lower=2252813807/40960000000000000,
    upper=560909/10000000000000,
    threshold=3/250000.

The new source and an independent Fraction calculation give

    e=44669457/489267186193 < 1/10000.                       (NR6)

Using exactly the existing candidate, the interval consumer proves

    D > 647/1000,
    |d|-sqrt(eU) > 797/1000.                                (NR7)

Consequently every allowed projective error has |F(p)(0)|>797/1000. The
normalized Fourier transform is therefore well-defined and introduces no
pole through division by its zero-frequency value.

At the fixed complex frequency z=1+i/4, the disk gives

    |F(p)(z)/F(p)(0)-F(k)(z)/F(k)(0)| < 3/4000.             (NR8)

The directed interval for the tighter budget is approximately
0.0007418181100654655. The conventional separate projected-triangle budget

    sqrt(e)*(sqrt(V)+|a/d|sqrt(U))/(|d|-sqrt(eU))

is independently certified to exceed 3/200 at that same frequency. Hence
the new certified upper budget is over twenty times smaller. This compares
two sufficient uncertainty budgets; it does not measure the unknown actual
error or claim a twentyfold improvement in an eigenvalue computation.

The seven frequencies in the report are pointwise consumers, not an
exhaustive boundary cover or a compact-uniform theorem. In particular the
ball disk at z=14+i/4 still contains zero. The norm enclosure alone is
therefore insufficient for zero exclusion at that point. This concerns
permitted ball errors, not the zeros of the actual ground transform.

### 7. Reproducibility, finite checks and remaining work

New files under `research/weil_ground_mode/`:

- `certify_prime3_normalized_readout.py`
- `prime3_normalized_readout_certificate.json`
- `test_normalized_readout.py`
- `normalized_readout_validation.json`

The consumer checks both immutable input blob identities, recomputes e
from the exact energy fields, validates the even coefficient list, evaluates
the full Gram in directed intervals and independently expands (NR3). All
acceptance comparisons use intervals or rational arithmetic. Display values
are not reused as certificates. Ordinary execution and -O execution retain
the same explicit failure checks.

Exact Gaussian-rational tests cover 1,200 multidimensional cases, 1,336
constructed attaining witnesses, 1,187 rejected ratio queries, 120 exact
boundary cases and three degenerate cases. Removing the required conjugation
is detected in 2,491 checks; changing the covariance sign is detected in
2,521 checks. Interval replays at 50 and 90 decimal digits agree on all
stated rational bounds. Altered candidate input, altered energy report and
insufficient interval precision are rejected. These are development checks,
not an independent-author review or a Lean kernel verdict.

For a scale family, the relevant normalization-sensitive error is now

    E_a(z)=|B_a(z)/D_a-a_a(z)/d_a|+sqrt(S_a(z))/D_a.

A sufficient remaining goal is an independently certified D_a>0 and
sup_{z in K}E_a(z)->0 on every compact K in the target strip, together with
convergence of the same candidates' normalized transforms to Xi(z)/Xi(0).
The disk retains the actual readout covariance, allowing a more targeted
condition than a single global Fourier operator norm. It does not prove
that condition along unbounded scales. The dyadic candidates have still not
been identified with the explicit prolate model. The simple-even all-scale
problem, that model comparison and the Xi limit remain unresolved.

No new off-line zero, prime-gap bound, RH proof, larger positivity window,
canonical source admission or frozen-state transition is asserted.
