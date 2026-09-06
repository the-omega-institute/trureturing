- Connes, Consani, Moscovici, Zeta Spectral Triples, arXiv:2511.22755v1, Sections 3, 4, 7, 8.
- Connes, van Suijlekom, Quadratic Forms, Real Zeros and Echoes of the Spectral Action, arXiv:2511.23257v1, (11), Theorems 5.6 and 6.1. The matrix and theorem pages were inspected as PDF images.
- Suzuki, Weil's quadratic form via the screw function, arXiv:2606.09096v1, Lemma 3.1 and Sections 3.2, 4.1.
- Connes, Consani, Spectral triples and zeta-cycles, Enseign. Math. 69 (2023), 93-148; arXiv:2106.01715v1, Lemma 2.2 and Proposition 2.3. The arXiv text and the publisher bibliographic record were checked.
- Marcus Chuk, Weil positivity in compact windows: certified two-sided bounds and a Landau-Widom decay law, arXiv:2608.24827, original abstract only in this round.

---

## [PR #5602] NEUMANN_COMPLETION_CANONICAL_MODEL_AND_FOURIER_OBSERVATION

# 2026-09-06: arithmetic high-mode weights, a finite prolate candidate family, and complex observation error

This append supplies the previously unwritten theory for
`WeilArchimedeanHighModeBounds` and `WeilNeumannGammaBoundary`, records the
replayed combined certificate, and explains the new
`WeilEvenFourierObservationTail` Lean/Scribe pair. It keeps the same
`literatureRHS(weilTest f f)`, `gammaBracket`, operator realization, and
Fourier convention. The results below distinguish mathematical proofs,
executed interval computations, and Lean proof scripts. No Lean elaboration,
Scribe compilation, or `#print axioms` execution was performed in this round.

## 1. Cross-PR inputs and the actual open problem

The research target remains the two missing steps in Connes-Consani-Moscovici
(CCM), *Zeta Spectral Triples*, arXiv:2511.22755v1, Section 8: simple-even
lowest modes of the actual Weil operator and sufficiently accurate
approximation by their explicit prolate model along unbounded scales.
A fixed-window certificate does not close either unbounded-scale assertion.

The following actual sources were read, including both authors' work:

* loning, PR #5326, head `3beb435bf9ca8aa35aa6079ea4033a9c2e6c9007`,
  `RH_OFFLINE_ZERO_LEE_YANG_INSTANTANEOUS_PHASE_TRANSITION_THEORY.md`,
  Sections C14-C15: a Schur floor incurs a dimension-dependent determinant
  floor. Its canonical determinant identity and boundary approximation
  remain independent obligations. This motivates controlling the scalar
  Fourier output directly rather than introducing another determinant.
* AlyciaBHZ, PR #5580, head `e1699ed18ff0e8145870c2d44374193d83766851`,
  `OrderedStableBalancedTruncation.lean`: stability and an output error
  bound concern the same constructed reduced system. Its discrete Stein
  hypotheses are not hypotheses of the unbounded Weil operator; no direct
  application of that theorem is asserted here.
* AlyciaBHZ, PR #5562, branch `work/prime-weil-foundations-probe-20260905`,
  `ScaledComplexQuadraticRowBound.lean`, blob
  `1b94a72bebdf5128d020fe755b285099a35b70a1`: complex coefficients, individual
  energy weights, and absolute series budgets are already supported.
  Its scaled-row assumptions are not automatically true for our arithmetic
  matrix. No duplicate general row-bound owner is added.

Suzuki, arXiv:2606.09096v1, already studies the same closed Weil realization,
small-window ground modes, and an inverse Neumann Laplacian in Section 8.2.
His inverse on mean-zero functions differs from the massive resolvent
comparison below. Neumann ideas, Hilbert inequalities, projection estimates,
and Schur/Feshbach methods are classical. No priority claim is made for them.

## 2. Restore the all-parity logarithmic comparison

Let L=2a>0, omega_n=2*pi*n/L, b_j=2j+1/2. Extract the Gamma part of the
existing arithmetic boundary symbol:

\[
g_L(n)=\sum_{j\ge0}\frac{\omega_n(1-e^{-b_jL})}{b_j^2+\omega_n^2}.
\]

For w>0 the positive telescoping inequality

\[
\frac{w}{(2j+5/2)^2+w^2}
\le w\left(\frac1{w+2j+1/2}-\frac1{w+2j+5/2}\right)
\]

and the zeroth term give an absolutely convergent majorant with sum at most
1+1/w. The actual symbol therefore satisfies

\[
|g_L(n)|\le1+\frac{L}{2\pi|n|}\qquad(n\ne0).
\tag{CO1}
\]

The same-source Fourier diagonal is

\[
d_n^\Gamma=\gamma(\omega_n)+\frac2L\sum_{j\ge0}
(1-e^{-b_jL})\frac{b_j^2-\omega_n^2}{(b_j^2+\omega_n^2)^2}.
\]

The absolute correction series is bounded by the preceding majorant divided
by |omega_n|, because |b_j^2-omega_n^2|<=b_j^2+omega_n^2. Thus

\[
|d_n^\Gamma-\gamma(\omega_n)|
\le\frac1{\pi|n|}+\frac{L}{2\pi^2n^2}.
\tag{CO2}
\]

The existing `arithmetic_archimedean_high_mode_bounds` proof script proves
(CO1) for the actual extracted symbol, absolute summability of the correction,
and its bound. Identification of the series with the actual diagonal is the
Fourier calculation already recorded in (AC3), using the trigamma series.

On l2(Z), H_nm=1/(m-n) for m!=n and H_nn=0 has norm at most pi.
Indeed its circle Fourier multiplier is, up to the sign convention,
i*(pi-theta) on 0<theta<2*pi. Its coefficients follow by integration by parts;
Parseval proves the bound on finite sequences and then by density on l2.
Every coordinate compression has the same bound. On |n|>=n0>=1 the complete
Gamma off-diagonal block is [D_{-g},H]/pi, so (CO1) bounds its norm by
2+L/(pi*n0), including all cross-shell couplings.

Use the previously proved gamma(t)>=log(t/(2*pi))-2/t for t>0. Let P_L be
an independently justified norm budget for the actual finite prime block,
and D_L=2*(sinh(L/2)-L/2) its actual pole negative-channel budget. Then

\[
q_a(y)\ge\sum_{|n|\ge n_0}d_o(L,n;n_0)|y_n|^2,
\tag{CO3}
\]

\[
d_o(L,n;n_0)=\log\frac{|n|}{L}-2-
\frac{2L+1}{\pi n_0}-\frac{L}{2\pi^2n_0^2}-P_L-D_L.
\]

This is a simultaneous lower form, first proved on finite Fourier vectors.
For extension to the whole high form domain, subtract the finite low
projection from a trigonometric form-core approximation. That projection
is form-norm continuous since its finitely many basis vectors are in the
operator domain. Add a constant to make the displayed diagonal weights
nonnegative and use lower semicontinuity of the weighted coefficient sum.
This also proves finiteness of that sum for a vector in the original form
domain. The actual form core is the one of Connes-Consani,
arXiv:2106.01715v1, Lemma 2.2 and Proposition 2.3. The Hilbert, Fourier and
form-domain bridges here remain paper proofs, not declarations of CO1's owner.

For c=3, L=log3 and n0=65, use P_L=log2/sqrt2. The compressed prime-2
translations have disjoint input and output segments since L<2log2; hence
the norm of their sum is at most one. At n0, (CO3) gives a constant greater
than 1.5184518986360646, verified by directed interval arithmetic. It grows
as log(|n|/65). This supplies the previous logarithmic-weighted certificate
and the odd-sector weights in the combined certificate below.

## 3. Restore the exact Neumann Gamma completion

Set I=[-a,a]. For b>0 define independently the compressed free resolvent
and the Neumann resolvent of -d^2/dx^2+b^2 by their Green kernels:

\[
R_b^F(x,y)=\frac{e^{-b|x-y|}}{2b},\qquad
R_b^N(x,y)=
\frac{\cosh(b(\min(x,y)+a))\cosh(b(a-\max(x,y)))}{b\sinh(2ba)}.
\]

The latter has zero endpoint derivative and a derivative jump -1 at x=y.
A direct hyperbolic calculation, separately for x<=y and y<=x, gives

\[
2b(R_b^N-R_b^F)(x,y)=
\frac{2\cosh(bx)\cosh(by)}{e^{bL}-1}
+\frac{2\sinh(bx)\sinh(by)}{e^{bL}+1}.
\tag{CO4}
\]

Its integrated quadratic form is the sum of the corresponding two positive
squares of boundary moments. Every kernel is bounded on the fixed compact
square and L2(I) is included in L1(I); thus the complex-valued integrated
identity follows from Fubini, not from an assumed sign of the Weil form.

The digamma partial-fraction formula gives

\[
\gamma(t)-\gamma(0)=\sum_{r\ge0}\frac{2t^2}{b_r(b_r^2+t^2)},
\qquad b_r=2r+\tfrac12.
\tag{CO5}
\]

Each summand corresponds to (2/b_r)I-2b_r R^F_{b_r}. Replace the free
resolvent by the Neumann one and use (CO4). With the orthonormal Neumann
basis nu_0=L^(-1/2) and
nu_j=sqrt(2/L)*cos(pi*j*(x+a)/L), j>=1, one obtains

\[
\begin{aligned}
q_\Gamma(f)={}&\sum_{j\ge0}\gamma(\pi j/L)|\langle\nu_j,f\rangle|^2\\
&+2\sum_{r\ge0}\left[
\frac{|\langle\cosh(b_r\,\cdot),f\rangle|^2}{e^{b_rL}-1}
+\frac{|\langle\sinh(b_r\,\cdot),f\rangle|^2}{e^{b_rL}+1}\right].
\end{aligned}
\tag{CO6}
\]

To justify every infinite expression, first subtract gamma(0)*||f||^2.
All resolvent increments, Neumann frequency increments, and boundary
squares are then nonnegative. Prove the finite-mixture identity and use
Tonelli and monotone convergence. This is an equality of extended forms;
on the actual Gamma form domain the terms on the right are finite.
The original Weil realization is unchanged. Neumann conditions belong to
a comparison operator, not to a replacement for the original domain.

On the even sector use the canonical phase-adjusted cosine basis
phi_n=(-1)^n*sigma_n*cos(2*pi*n*x/L)/sqrt(L), with sigma_0=1 and
sigma_n=sqrt2 for n>=1. Write omega_n=2*pi*n/L and
M_b(v)=sum sigma_n*v_n/(b^2+omega_n^2). Direct integration gives

\[
\langle\cosh(b\,\cdot),f\rangle
=\frac{2b\sinh(bL/2)}{\sqrt L}M_b(v).
\]

Combining the b_0=1/2 boundary square with the actual even pole contribution
2*|<cosh(x/2),f>|^2 yields

\[
q_{\Gamma+\mathrm{pole}}(f)=\sum_{n\ge0}\gamma(\omega_n)|v_n|^2
+\frac2L\sum_{r\ge0}b_r^2\eta_r(L)|M_{b_r}(v)|^2,
\tag{CO7}
\]

where eta_0=e^(L/2)-1 and eta_r=1-e^(-b_r L) for r>=1. All eta_r are
positive. Consequently the whole even high form has the lower weight

\[
d_e(L,n)=\gamma(2\pi n/L)-P_L
\ge\log(n/L)-\frac{L}{\pi n}-P_L.
\tag{CO8}
\]

At c=3 and n>=65 this is greater than 7/2. For example use log3<11/10,
pi>3, log2/sqrt2<1/2 and log(65/log3)>401/100. The last comparison follows
from e<11/4, e^(1/100)<100/99 and (11/4)^4*(100/99)<650/11. Then
401/100-11/1950-1/2>7/2. These are direct rational comparisons.
The old `WeilNeumannGammaBoundary` scripts prove (CO4), its finite real
quadratic identity and finite canonical-mixture positivity. The complex
L2, infinite-mixture and operator-domain consequences are the paper proof
above. The even weight (CO8) is not assigned to the odd Fourier sector.

## 4. Replayed combined certificate with all exterior modes retained

The actual checker is
`research/weil_ground_mode/certify_prime3_neumann_weighted.py`, SHA-256
`d6c150268b3f041701a40b804499218bd164555dede6d9c2bd30e7a10a195a99`.
It verifies the pinned dependency `certify_prime3_refined.py` before import;
its SHA-256 remains
`8bb067fc5499b0f2e1e48836e7a82237a15504109f82a856c72478d1096d69d0`.

Keep the same 129-entry dyadic even candidate, N=64, M=32768, 44-bit
coefficient quantization and 60-bit directed error radii. The even block
uses (CO8); the odd block uses (CO3). For each shell a rational lower
energy is selected and verified strictly below its directed analytic
interval. All resolvent weights use T=3/250000. They therefore also bound
the correction at every shift ell<=T. The exact shell Gram and weighted
radius energies are accumulated with checked integer/rational arithmetic.
For each sector, if t is the weighted squared Frobenius norm of the
quantized matrix and e its weighted error energy, the checks

\[
e<\eta,\qquad4te<(\eta-e)^2
\]

prove a Gram norm error below eta. This follows by applying the ordinary
Gram perturbation identity to W^(1/2)C; it does not multiply an unweighted
matrix inequality by a noncommuting weight. The entire |m|>M tail uses
the prior second-jet four-moment positive majorant, with scalar budget
9e-13, divided by the relevant energy denominator at M+1.

The weighted Gram error budgets are 4/152587890625 (even) and
8/152587890625 (odd). The sum of the integer shell Grams has exactly the
previous hash `7f4e1049624807432efe96a68fe63babbc1c3bd37f2d40600a4cddadbddb85a9`.
No zero data or eigensolver is used. All final positive LDL tests were
executed; the entire final output was reproduced exactly in a second run.
A failed intermediate LDL search is not evidence of a negative eigenvalue.

Let k be this fixed candidate normalized in L2. The final rational bounds are

\[
\ell=\frac{2252813807}{40960000000000000},\quad
U=\frac{560909}{10000000000000},\quad T=\frac3{250000}.
\tag{CO9}
\]

The even full-lower test, even k-orthogonal test, and odd test are strictly
positive. Their displayed minimum LDL pivots are respectively
0.003202644247409436, 0.26802217563245934, and 0.040988013296152585.
These pivots prove positivity, not eigenvalue lower bounds. Weighted square
completion on the entire form domain gives

\[
q(f)\ge\ell\|f\|^2,\qquad f\perp k\Longrightarrow q(f)\ge T\|f\|^2.
\]

The odd lower bound T also exceeds ell, so the full lower bound covers both
parities. The actual Rayleigh interval is below U. Compact resolvent and
min-max give a simple isolated even lowest line, with

\[
5.50003370849609375\cdot10^{-8}\le\lambda_0<5.60909\cdot10^{-8},
\quad\lambda_1\ge1.2\cdot10^{-5}.
\]

The existing projective argument (RE4) consequently gives

\[
\left\|u/\langle k,u\rangle-k\right\|^2
\le\frac{44669457}{489267186193}<\frac1{10000}.
\tag{CO10}
\]

This improves the earlier 0.01475 bound to 0.01 for the same candidate and
window. The preceding Neumann-only replay had threshold 1/200000 and bound
0.02; it did not improve 0.01475. The successful improvement uses different
justified weights in the two parity sectors. The full operator theorem
remains a paper/computer-assisted result, not a Lean kernel-certified result.

## 5. The new Lean estimate controls the actual complex Fourier observable

For n>0 direct integration in the same basis gives

\[
\widehat\phi_n(z)=
\frac{2\sqrt{2/L}\,z\sin(Lz/2)}{z^2-(2\pi n/L)^2}.
\tag{CO11}
\]

The paired positive and negative modes cancel the leading inverse-frequency
term. Let y=sum_{n>N}v_n phi_n be any even L2 tail, N>=1. If L*|z|<=pi*N,
put w=L*z/(2*pi); then |n^2-w^2|>=3*n^2/4. The identity

\[
\frac1{3x^3}-\frac1{3(x+1)^3}-\frac1{(x+1)^4}
=\frac{6x^2+4x+1}{3x^3(x+1)^4}\ge0
\]

proves sum_{n>N}n^(-4)<=1/(3N^3), including convergence. Young's inequality
and this positive majorant prove absolute convergence of the Cauchy series
for every square-summable complex v. Finite Cauchy-Schwarz followed by its
sum limit proves

\[
\boxed{|\widehat y(z)|^2\le
\frac{8L^3}{27\pi^4N^3}|z\sin(Lz/2)|^2\|y\|_2^2.}
\tag{CO12}
\]

`WeilEvenFourierObservationTail.even_exterior_fourier_observation_bound`
proves absolute convergence and the precise normalized coefficient-series
inequality. There is no upper exterior cutoff or assumed boundary
cancellation. To identify that response with the actual L2 Fourier tail,
use Parseval and convergence of the finite cosine sums in L2(I), hence L1(I).
Their transforms converge at each complex z by Cauchy-Schwarz on the fixed
window. Equation (CO11) identifies the finite sums, and the proved absolute
series convergence identifies their limit. This last Fourier-space bridge
is a paper proof rather than a second hidden Lean assumption.

On |z|<=R, |Im z|<=b, use |sin(Lz/2)|<=exp(bL/2) to obtain

\[
|\widehat y(z)|\le\sqrt{\frac8{27\pi^4}}L^{3/2}R e^{ba}N^{-3/2}\|y\|_2.
\tag{CO13}
\]

When a certified high energy is at least beta*||y||^2, the squared
observation budget is divided by beta. This controls the entire exterior
observation. It does not assert that the low component of a ground-mode
error is small, or that exp(ba) has disappeared.

## 6. Fix the Mellin normalization before identifying Xi

Use the exact standard definition Xi(z)=xi(1/2+iz),
xi(s)=s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)/2, and dx=du/u.
CCM (7.1)-(7.2) write

\[
h(u)=\frac\pi2u^2(2\pi u^2-3)e^{-\pi u^2},\qquad
\mathcal E h(u)=u^{1/2}\sum_{m\ge1}h(mu).
\]

For our chosen Haar and Fourier normalization, the exact scalar is checked
by a Mellin calculation, not inferred from a zero plot:

\[
\int_0^\infty h(t)t^{s-1}dt
=\frac{s(s-1)}8\pi^{-s/2}\Gamma(s/2).
\tag{CO14}
\]

For Re s>1 the absolute sum-integral interchange gives

\[
\int_0^\infty\mathcal E h(u)u^{s-1/2}\frac{du}{u}=\xi(s)/4.
\]

The written h is self-Fourier, has h(0)=0 and integral zero. Poisson
summation gives E h(u)=E h(1/u), and its Gaussian tail gives entire Mellin
continuation. Hence the inverse Fourier kernel for our Xi is

\[
\Phi(x)=4\mathcal E h(e^x),\qquad\widehat\Phi=\Xi.
\tag{CO15}
\]

This agrees with the theta kernel already written in this volume. The
factor 4 corrects a scalar mismatch when importing the literal h in CCM;
it does not alter zeros or invalidate a statement made only up to a scalar.
A numerical check at z=0 gave the ratio 1/4 for the unscaled transform;
that check is a diagnostic, while (CO14) supplies the proof.

## 7. An explicit finite dyadic prolate family with the correct strip limit

This construction is separate from the fixed 129-entry certificate vector.
Take lambda=e^a along the integers lambda>=2, so the arithmetic cutoff
c=lambda^2 is integral and tends to infinity. Use the canonical spheroidal
functions ps_n^0(x/lambda;(2*pi*lambda^2)^2) in the convention of CCM (7.10).
The explicit normalizations

\[
h_{0,\lambda}=2^{-1/2}\lambda^{-1/2}\operatorname{ps}_0^0,
\qquad h_{4,\lambda}=3\,2^{-1/2}\lambda^{-1/2}\operatorname{ps}_4^0
\]

have the Hermite limits in CCM (7.11)-(7.12). Set I_j(lambda)=integral of
h_{j,lambda} over [-lambda,lambda] and

\[
h_\lambda=\frac{\sqrt3}{2^{11/4}}
\left(h_{4,\lambda}-\frac{I_4(\lambda)}{I_0(\lambda)}h_{0,\lambda}\right).
\tag{CO16}
\]

The first prolate mode has positive integral, so the denominator is nonzero.
CCM Lemma 7.2 and its Fourier-eigenvalue argument give
I_j(lambda)=h_j(0)+O(lambda^-2). Thus (CO16) has integral zero and
sup_{[-lambda,lambda]}|h_lambda-h|<=C*lambda^-2 for a fixed finite C at
large lambda. This is the published prolate approximation input, not a
new Lean theorem and not a statement about the unknown Weil ground mode.

Define, with zero extension outside [-a,a],

\[
p_a(x)=4e^{x/2}\sum_{1\le m\le\lambda e^{-x}}h_\lambda(me^x),
\qquad p_a^+(x)=\frac{p_a(x)+p_a(-x)}2.
\tag{CO17}
\]

There are at most lambda^2 summands. Evenization is explicit: finite prolate
Fourier eigenvalues need not coincide, so reciprocal symmetry of this
finite model is not assumed.

Retain the omitted Gaussian terms when comparing (CO17) with (CO15).
For u in [lambda^-1,lambda], monotonicity of t^4*exp(-pi*t^2) on t>=1 and
integration by parts give

\[
|\mathcal E h_\lambda(u)-\mathcal E h(u)|
\le u^{-1/2}\bigl(C/\lambda+R_H(\lambda)\bigr),
\]

\[
R_H(\lambda)=\pi^2e^{-\pi\lambda^2}
\left(\lambda^5+\frac{\lambda^3}{2\pi}
+\frac{3\lambda}{4\pi^2}+\frac3{8\pi^3\lambda}\right).
\tag{CO18}
\]

For some explicit finite D, R_H(lambda)<=D/lambda for lambda>=1; each
polynomial-Gaussian factor has a bounded maximum. Consequently
|p_a(x)-Phi(x)|<=4(C+D)e^-a*e^(-x/2) inside the window. Its squared L2
error is at most 16(C+D)^2*e^-a. The exterior Phi tail is double-exponential.
In particular ||p_a^+|| is bounded by a constant B independent of large a.
For every b<1/2, weighted integration of the same bound gives

\[
\sup_{|\Im z|\le b}|\widehat{p_a^+}(z)-\Xi(z)|
\le C_b e^{-(1/2-b)a}.
\tag{CO19}
\]

The integrals on the negative and positive half-windows are respectively
(e^((1/2+b)a)-1)/(1/2+b) and (1-e^(-(1/2-b)a))/(1/2-b), multiplied by
4(C+D)e^-a. Evenization averages the bounds at z and -z. These formulas
justify the claimed strip rate without discarding a nonzero Gaussian tail.

Now project onto the actual canonical even Fourier space P_N. Its
coefficients are explicit finite integrals:

\[
b_{a,j}=4\sum_{m=1}^{\lambda^2}
\int_{-a}^{\log(\lambda/m)}e^{x/2}h_\lambda(me^x)\phi_j(x)\,dx.
\tag{CO20}
\]

Because phi_j is even these also equal the coefficients of p_a^+.
Set d_{a,j}=2^-p*floor(2^p*b_{a,j}+1/2), and define the finite dyadic model
p_tilde_a=sum_{j=0}^N d_{a,j} phi_j. Rounding gives an L2 error at most
sqrt(N+1)*2^-p. Applying (CO13) to the entire projection tail gives, on
|z|<=R and |Im z|<=b with LR<=pi*N,

\[
\begin{aligned}
|\widehat{\widetilde p_a}(z)-\Xi(z)|\le{}&
C_b e^{-(1/2-b)a}
+\sqrt{\frac8{27\pi^4}}L^{3/2}R e^{ba}N^{-3/2}B\\
&+\sqrt{L(N+1)}e^{ba}2^{-p}.
\end{aligned}
\tag{CO21}
\]

For example the explicit choices

\[
N_a=\lceil(a+1)e^{a/3}\rceil,\qquad
p_a^{\rm bits}=\left\lceil\frac{2a/3+2\log(a+1)}{\log2}\right\rceil
\tag{CO22}
\]

give, on every compact substrip rectangle,

\[
\boxed{\sup_{|z|\le R,|\Im z|\le b}
|\widehat{\widetilde p_a}(z)-\Xi(z)|
\le C_{R,b}e^{-(1/2-b)a}.}
\tag{CO23}
\]

Indeed N_a+1<=3(a+1)e^(a/3) for a>=log2. The projection term then has the
same exponential rate, and the rounding term is at most sqrt6 times that
rate. The pole-free band condition holds eventually for each fixed R.
Xi(0)>0, also seen from the positive Phi on x>=0, shows p_tilde_a is nonzero
eventually. With c_a=||p_tilde_a|| and k_a=p_tilde_a/c_a, (CO23) proves
c_a*hat(k_a)->Xi for this specified family.

(CO22) is a resolution sufficient for the function limit, not a sufficient
resolution for the arithmetic spectral certificate. One may choose any
larger N and choose p so that
sqrt(L*(N+1))*2^-p<=exp(-a/2); then the same rate is retained. Resolving an
exponentially small arithmetic gap may require vastly more precision.
No executable certified evaluator for all the prolate integrals in (CO20)
is asserted here. Their definition and analytic approximation are explicit;
their interval implementation remains a separate numerical obligation.
The old certified k at c=3 is not identified with (CO20).

## 8. A directional Schur estimate for the same Fourier observable

The following paper estimate specifies what the remaining arithmetic work
must control. It is not an assertion that its certificates hold at every
scale. Suppose the actual same candidate has been certified to satisfy
ell<=lambda<=mu<=U<T, q(f)>=T||f||^2 on k-perp, and the simple even ground
mode u has norm one. Set alpha=<k,u> and w=u/alpha-k. The earlier projective
argument proves alpha!=0, w perpendicular to k, and

\[
q(w)-\lambda\|w\|^2=\mu-\lambda,\quad
\|w\|^2\le\frac{\mu-\lambda}{T-\lambda}<1.
\]

It follows, retaining the actual energy instead of just the gap, that

\[
q(w)-\ell\|w\|^2\le U-\ell.
\tag{CO24}
\]

Assume k lies in P_NH. Put x=P_Nw, y=Q_Nw, C=Q_N A|P_NH, and let
D=diag(d_e(L,n)-ell), n>N, have a strictly positive lower bound. Suppose
an actual complete coupling majorant Gbar>=C^*D^-1 C has been certified,
and the finite matrix

\[
H=A_N-\ell I-\overline G+\rho kk^*,\qquad\rho>0,
\]

is positive definite. Since x is perpendicular to k, weighted completion
and (CO24) give

\[
\langle x,Hx\rangle+
\|D^{1/2}y+D^{-1/2}Cx\|^2\le U-\ell.
\tag{CO25}
\]

On the even space the actual complex Fourier functional has representer
g_z(t)=cos(conj(z)*t), since the inner product is linear in the second
argument. Let g_P and g_Q be its two components and set

\[
h_z=P_{k^\perp}(g_P-C^*D^{-1}g_Q),\qquad
\mathcal D_a(z)=\langle h_z,H^{-1}h_z\rangle
+\langle g_Q,D^{-1}g_Q\rangle.
\tag{CO26}
\]

Writing the Fourier output in the two coordinates of (CO25) and applying
Cauchy-Schwarz in their direct-sum energy norm proves

\[
\boxed{|\widehat w(z)|^2\le(U-\ell)\mathcal D_a(z).}
\tag{CO27}
\]

All high pairings are legitimate: the original form domain is included
in the D form domain, C has finite domain and l2 images, and D^-1 is
bounded. The second term of (CO26) has the explicit N^-3 observation
bound (CO12), divided by the lower bound of D. The first term is a
finite inverse quadratic form with an arithmetic high-mode correction.
That correction still requires an interval evaluation and an infinite-tail
bound; it is not assigned a numerical value in this round.

For the family (CO20), a sufficient remaining arithmetic target is

\[
c_a^2(U_a-\ell_a)\sup_{z\in K}\mathcal D_a(z)\longrightarrow0
\tag{CO28}
\]

for every compact K in |Im z|<1/2, together with the actual full-space
coercivity certificates used in (CO24)-(CO25). This is a directly observed
error budget, not a determinant floor raised to the realization dimension.
It can be used with the repository's rectangle Rouche machinery when
strict boundary lower bounds and errors are actually available. No such
all-rectangle certificate or ground-family limit is claimed here.

## 9. What has and has not been removed from the problem

The executed fixed-window estimate has genuinely improved. On paper, the
actual high-mode weights have an independent arithmetic proof, and an
explicit finite dyadic prolate family now has a calibrated Xi limit with
quantified projection and rounding errors. The new Lean increment proves
the infinite complex observation-tail bound with absolute convergence.

The first open research obligation is still to certify the *same* family
(CO20) against the actual Weil operator along an unbounded scale sequence,
and make (CO28), or the earlier weighted projective bound, tend to zero.
No finite matrix positivity assumption has been promoted to an arithmetic
theorem without its certificate. Neither the Neumann comparison nor the
new observable estimate is claimed to evade the earlier shift barrier.
The remaining low-mode error, prime cancellations, and prolate integral
certification require further work. No RH proof, universal simple-even
family theorem, or end-to-end Lean real-zero limit is asserted.

References used for this append:

* Connes, Consani, Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1,
  (7.1)-(7.12), Lemmas 7.2-7.3 and Section 8. The literal normalization was
  independently checked by (CO14), and the omitted Gaussian tail is retained.
* Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1,
  Theorems 1.1-1.4 and Section 8.2. Results stated under RH are not used.
* Connes, Consani, *Spectral triples and zeta-cycles*, arXiv:2106.01715v1,
  Lemma 2.2 and Proposition 2.3, for the actual form core.
* Dusson, Sigal, Stamm, *Analysis of the Feshbach-Schur method for the Fourier
  spectral discretizations of Schrodinger operators*, arXiv:2008.10871v2.
  The elimination principle is classical; its Schrodinger regularity
  assumptions are not silently imported into the Weil problem.
* DLMF 5.7.6, digamma partial fractions, and the Gamma integral and recurrence,
  for the elementary resolvent and Mellin computations.
