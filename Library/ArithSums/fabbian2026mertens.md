---
bibkey: fabbian2026mertens
authors: Giacomo Fabbian
year: 2026
title: An explicit Mertens-product bound at the Morrill–Platt threshold, with applications to Robin's inequality
doi: 10.5281/zenodo.23025480
url: https://doi.org/10.5281/zenodo.23025480
claim: The preprint's uniform Mertens-product bound implies Robin for integers with v₂ at most 25; the necessary interval constants were checked, while external analytic premises remain literature inputs. This filter is weaker than existing least-counterexample restrictions.
strata_touched: []
license: citation-only
triage: anchor
---

# Explicit Mertens bound and the single-valuation Robin filter

The primary source is the Zenodo preprint, record **23025480**, version **1.0**, published **29 September 2026**. Its PDF and supplement were inspected; no peer-reviewed publication or Lean verification is asserted. The analytic reduction below uses its stated external premises, not a new proof of those premises.

## Exact interface

With $\vartheta(x)=\sum_{p\le x}\log p$, Proposition 1 states, for every real $x\ge X_0$,

$$
\sum_{p\le x}\log\frac p{p-1}-\gamma-\log\log\vartheta(x)\le B,
\qquad X_0=29996208012611,\quad B=1.3064373\cdot10^{-8}.
$$

Theorem 2 combines this bound with the existing Morrill–Platt finite verification: for a prime $p$ and an integer $J\ge1$, the condition

$$
-\log(1-p^{-J-1})>B
$$

implies Robin's inequality for every $n>5040$ with $v_p(n)\le J$. In particular, **$2^{26}\nmid n$ suffices**; being 26-free is a stronger restriction on $n$ and therefore a corollary. This does not exclude integers divisible by $2^{26}$.

The reduction uses ordered modified Euler factors (Lemma 3.2). If $N_k\le n<N_{k+1}$ for consecutive primorials and $p\le p_k$, it bounds $Z(n)=\sigma(n)/n$ by $(1-p^{-J-1})N_k/\varphi(N_k)$. The argument also allows $p\nmid n$; it does not insert an absent prime into the actual Euler product. The displayed finite verification covers $5040<n\le X_0^\#$ by combining the two Morrill–Platt ranges. In [arXiv:1809.10813v4](https://arxiv.org/abs/1809.10813v4), these are Theorem 13 and Corollary 14; the paper cites the published numbering 5 and 2. This imports an existing finite interval, without extending or rerunning it.

## Verified constants and remaining dependencies

The supporting derivation in §§2–5 was checked for the selected $p=2,J=25$ consequence. In particular, the integrated explicit formula uses RH only at the already verified finite height $3\cdot10^{12}$; its remaining zeros and infinite tail are bounded unconditionally. No use of global RH was found in that inspected chain. The external inputs are the Morrill–Platt verification, Platt–Trudgian finite-height zero verification, the integrated explicit formula and classical zero sum/count, Rosser–Schoenfeld bounds, and Büthe and Platt–Trudgian bounds for $\vartheta$. The original Morrill–Platt statements were checked; the other external original proofs and computations were not all re-audited.

The required C2–C3 checks and **only the $p=2,J=25$ part of C4** were executed with python-flint **0.8.0**, Python **3.12.13**, **160-bit** interval arithmetic and one thread. All selected strict comparisons passed, with exit code zero. The containing balls for the two final margins were

$$
B-(A^*+P_2^+(X_0)+P_1^+(X_0))
\in[1.13086113662967602691919\cdot10^{-14}\ \pm7.55\cdot10^{-38}],
$$

$$
-\log(1-2^{-26})-B
\in[1.83678830486995981542314977235185765273209096\cdot10^{-9}\ \pm1.57\cdot10^{-54}].
$$

Both lower endpoints are positive. The auxiliary sign conditions for the zero-count bound, the zeta logarithmic derivative at $-1$, and the $u,\kappa$ hypotheses were also checked. The full C4 prime catalogue, its maximality assertions, missing-prime threshold, and external finite Robin intervals were not rerun. These constant checks do not constitute a kernel proof or independent verification of every analytic premise.

## Source integrity and reproduction boundary

The separate `reproducibility.zip` in the cited record contains the correct Robin certificate program; all **49** entries in its SHA-256 manifest matched. The archive SHA-256 is `258cca99fe0cc326d7ef325e07d6ba4d80502a4c3b4b0e7b930ed3901f22a44c`. The checked `robin_bounds.py` has SHA-256 `d38b6c86b742f4dd921bac593a92971d58612d8e15da75dde15bbfd66f3c8fd4`.

The record's `source.zip`, despite matching its advertised size and MD5, contains an unrelated prime-level GL(2) simple-zero manuscript. It was not used as the Robin source. This attachment mismatch does not imply that the separate certificate package is absent or invalid. Also, `run_all.sh` records individual child return codes without aggregating failure; its own successful exit alone is not a certificate. The selected checks called the relevant library functions and asserted each required interval comparison directly.

## Reuse boundary for FIB and CA research

The valuation filter can be applied to an actual integer whose FIB source has already supplied its exact valuation. It supplies no new relation between a FIB address and divisibility. Its fixed bound on the joint signed prime quantity does not reach the finer scale needed to exclude the surviving candidates.

The preprint itself explains that its necessary conditions for arbitrary counterexamples are weaker than known conditions on a **least** counterexample, which must be superabundant. Its cited single-prime exchanges already give $v_2\ge43$ and $v_3\ge27$ there; these numbers are not the precise values of the stronger floor-log estimates. Thus the $2^{26}$ filter does not improve exclusion of the classical least-counterexample test set. Nor does it change the [zero self-cutoff deficit at every CA integer](../Arith/alaoglu1944highly.md) or supply the [missing actual-candidate signed estimate](nicolas2025comparison.md). It is a reusable source restriction, not progress from a proportion or finite filter to full RH.

## Variable primitive allowance at surviving selected sources

Keeping the variable in the preprint's primitive bound does not by itself
reach the complete signed Robin target at the remaining selected sources.
The following is a source-specific comparison of existing estimates, not
a new prime-error bound, general RH criterion or originality claim.
It is a paper derivation without Lean certification.

### The primary allowance before the fixed constant

In the cited version-1 PDF, §4.1, printed p.8, let

$$
w(t)=\frac{1+\log t}{t^2\log^2t},\qquad
P_1(x)=\int_x^\infty(t-\psi(t))w(t)\,dt=-I_\psi(x).
$$

Use $H=3\cdot10^{12}$ for the source's verified height, called $T$
in the paper, and put

$$
S=2+\gamma-\log(4\pi)>0,\qquad
\Sigma'=\frac{2(\log(H/(2\pi))+1)}{\pi H},
$$

$$
M(t)=St^{3/2}+\Sigma't^2+t\log(2\pi)+2+\frac{\log2}{t}.
$$

Lemma 4.4, printed p.9, bounds the absolute primitive error by $M(t)$.
For zeros above $H$ it uses only $\beta\le1$, replacing
$t^{\beta+1}$ by $t^2$; the resulting positive allowance is
$\Sigma't^2$. Lemma 4.5, printed pp.9–10, states, for $1<x\le Y$,

$$
|P_1(x)|\le U(x,Y):=M(x)w(x)+M(Y)w(Y)
 +\int_x^Y M(t)|w'(t)|\,dt
 +\int_Y^\infty\epsilon(t)t w(t)\,dt.
\tag{V1}
$$

Here $\epsilon$ is the nonnegative pointwise envelope from the source's
(P6)(c). Every term of $U$ is nonnegative. The original analytic inputs
and selected certificate checks are reused as described above; none is
independently reproved or rerun.

### Compare at the actual Robin source

Keep the conditionally selected least global Robin maximizer $N$ and its
clock $A=\log N$, $L=\log A$, $T_A=\sqrt A\log A$.
The [existing selected-source restriction](../Analytic/polak2026finiterobinca.md#combining-finite-zero-verification-with-the-classical-zero-free-region),
(Z8), places every surviving such source at $A>3\cdot10^{23}$.
This is a restriction on that selected maximizer, not a least-counterexample
bound or an all-integer finite verification. The [effective core comparison](nicolas2025comparison.md#an-effective-allowance-stronger-than-the-existing-core-envelope),
(G7)–(G9), supplies the sufficient signed target

$$
T_A I_\psi(A)\ge-\mathcal E(L),\qquad
\mathcal E(L)<2\sqrt2-2.00014<1\quad(L\ge26).
\tag{V2}
$$

At this same clock, the first endpoint term in (V1) alone gives, for
every $Y\ge A$,

$$
T_A U(A,Y)\ge T_A\Sigma'A^2w(A)
=\Sigma'\sqrt A\left(1+\frac1{\log A}\right).
\tag{V3}
$$

The elementary bounds $e<3$ and $\pi<4$ give

$$
\frac H{2\pi}>\frac H8=375000000000
>3^{24}=282429536481>e^{24}.
$$

Thus $\log(H/(2\pi))>24$ and
$\Sigma'>50/(12\cdot10^{12})>4\cdot10^{-12}$.
Also $A>3\cdot10^{23}>(5\cdot10^{11})^2$, so (V3) yields

$$
\boxed{T_A U(A,Y)>2>\mathcal E(L)\qquad(Y\ge A).}
\tag{V4}
$$

Consequently the direct absolute primitive allowance (V1), even with
its handoff $Y$ optimized and its variable dependence retained, cannot
pay (V2) at any surviving selected source. This is a lower bound on
the allowance $U$, not on $|P_1|$ or the actual signed integral:
(V1) still gives only $T_A I_\psi(A)\ge-T_AU(A,Y)$.
No adverse sign of the actual error, Robin counterexample or impossibility
of a sharper method follows.

The obstruction is the positive $\Sigma't^2$ envelope for unverified
zeros, already present at the starting endpoint. A smaller majorant
using additional zero information, or a genuinely signed estimate,
would require a different supplier. The existing reflected-zero and
zero-free-region estimates in the Polak note remain separate, stronger
inputs; they are not repeated or added to this allowance. The complete
same-source signed target and RH remain unproved.

## A near-Euler contour for the complete negative-heat trace

The absolute primitive allowance (V1) remains insufficient at the
selected source by (V4). A different interface is available from the
complete signed zero trace already retained in
[the Nicolas comparison note](nicolas2025comparison.md#a-joint-small-negative-time-comparison-of-the-complete-signed-trace),
(NH1), (NH8)–(NH18). The result here improves its joint comparison error;
it does not supply a signed main-term bound.

Reuse the cited Dobner negative-time convolution and positive Fourier
kernel, the DLMF digamma sector estimate, Euler products, Cauchy estimates
and the complete contour balance. These are `literature-attested`
inputs. The parameter-dependent full-trace estimate below is a
`repo-derived` paper-level application. Within the inspected existing
notes and cached primary interfaces, no supplier of this exact joint
estimate was identified; no exhaustive literature, mathematical-priority,
numerical-constant or Lean-certification claim is made.

Keep $A\ge e^2$, $L=\log A$, and the complete principal continuation

$$
\widehat F_A(z)=\frac{A^{z-1}}{zL}+E_1((1-z)L),\qquad
Z_\epsilon(A)=\sum_{\xi_{-\epsilon}(w)=0}\widehat F_A(w).
$$

Both ordinate signs and every actual multiplicity are included. At zero
time this is exactly the original trace. There are absolute constants
$c>0$ and $C<\infty$ such that

$$
\boxed{|Z_\epsilon(A)-Z_0(A)|\le
 C\epsilon A^\eta\eta^{-8},\quad
 0<\eta\le\tfrac12,\quad
 0<\epsilon\le c\eta^4,\quad \epsilon L\le1.}
\tag{VE1}
$$

In particular, choosing $\eta=1/L$ gives

$$
\boxed{|Z_\epsilon(A)-Z_0(A)|\le C\epsilon L^8,
 \qquad0<\epsilon\le cL^{-4}.}
\tag{VE2}
$$

The constant $c$ may be reduced so that the small-time and
$\epsilon L\le1$ hypotheses hold in (VE2). The exponent $8$ is a paid
upper-bound exponent, not an optimality assertion.

### Pay normalization on a half-plane approaching the Euler boundary

Retain $J_\epsilon(s)=s+(\epsilon/4)\operatorname{Log}(s/(2\pi))$,
$\gamma(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)/2$ and
$\gamma_{-\epsilon}(s)=\gamma(s)
\exp((s-J_\epsilon(s))^2/\epsilon)$ from (NH7). Set

$$
U_\epsilon(s)=\frac{\xi_{-\epsilon}(J_\epsilon(s))}
 {\gamma_{-\epsilon}(s)},\qquad
R_s(v)=\frac{\gamma(s+iv)}{\gamma(s)}
 e^{-iv\operatorname{Log}(s/(2\pi))/2}.
$$

The exact Gaussian identity (NH8) extends to $\Re s>1$:

$$
U_\epsilon(s)=\frac1{\sqrt{\pi\epsilon}}\int_{\mathbb R}
 e^{-v^2/\epsilon}R_s(v)\zeta(s+iv)\,dv.
\tag{VE3}
$$

Indeed, both sides are analytic there. The bound below makes the
integral locally uniformly convergent, and the identity theorem
extends the already retained equality; no new heat-convolution proof
is needed.

For $\Re s\ge1+\eta/2$, factor the two polynomial factors out of
$\gamma$. The imaginary part of the log derivative of $\Gamma(s/2)$
is uniformly bounded on $\Re(s/2)\ge1/2$, by the same fixed-sector
DLMF expansion and its compact remainder. Consequently, for an
absolute $C_0$,

$$
|R_s(v)|\le C_0\eta^{-1}(1+|v|)^2e^{C_0|v|},\qquad
|\zeta(s+iv)|\le C_0\eta^{-1}.
\tag{VE4}
$$

The possible small denominator $s-1$ is paid by $\eta^{-1}$;
it is not integrated into an $e^{C|v|/\eta}$ envelope.

Put $G_s(v)=R_s(v)\zeta(s+iv)$. On $|v|\le1$,

$$
|G_s''(v)|\le C_1\eta^{-3}.
\tag{VE5}
$$

There are two complementary reasons. If $|s|>4$, the vertical
segment stays uniformly away from both $0$ and $1$. The centered
log-Gamma estimates and their Cauchy derivatives bound
$R_s,R_s',R_s''$ by an absolute constant. The absolutely convergent
series bound $\zeta^{(j)}(s+iv)$ by $C_j\eta^{-j-1}$ for
$j=0,1,2$. If $|s|\le4$, instead use the exact cancellation

$$
G_s(v)=\frac{\xi_0(s+iv)}{\gamma(s)}
 e^{-iv\operatorname{Log}(s/(2\pi))/2}.
$$

The numerator and its first two derivatives are bounded on this
fixed compact set, whereas $|\gamma(s)|\ge c_1|s-1|\ge c_1\eta/2$.
This gives $O(\eta^{-1})$ there, hence (VE5). Treating the Gamma
zero and zeta pole independently on this compact set would not
justify the stated exponent.

Center the Gaussian before taking absolute values. Its linear moment
vanishes and its second moment is $\epsilon/2$. On $|v|>1$, (VE4)
and the affine subtraction at zero pay the full tail by
$O(\epsilon\eta^{-3})$ for $\epsilon\le1/2$. Thus

$$
U_\epsilon(s)-\zeta(s)=O(\epsilon\eta^{-3})
 \quad(\Re s\ge1+\eta/2).
\tag{VE6}
$$

Euler inversion gives $|\zeta(s)|\ge1/\zeta(\Re s)\ge c_2\eta$.
Choosing $c$ sufficiently small in $\epsilon\le c\eta^4$ ensures
$|U_\epsilon(s)|\ge c_2\eta/2$ on this whole half-plane. This pays
the zero-free exterior for the deformed function, rather than applying
an original-zeta zero-free region to different zeros.

### Take logarithmic derivatives with their denominators paid

On $s=b+iy$, $b=1+\eta$, apply Cauchy's estimate to (VE6) on
radius-$\eta/4$ disks. It gives
$U_\epsilon'-\zeta'=O(\epsilon\eta^{-4})$.
The Euler logarithmic derivative satisfies

$$
\left|\frac{\zeta'}\zeta(b+iy)\right|
\le\sum_{n\ge2}\frac{\Lambda(n)}{n^b}
=\frac{-\zeta'(b)}{\zeta(b)}\ll\eta^{-1}.
$$

Here $\zeta(b)\ge1/\eta$ by integral comparison, and
$-\zeta'(b)\ll\eta^{-2}$. Use the identity

$$
\frac{U_\epsilon'}{U_\epsilon}-\frac{\zeta'}\zeta
=\frac{U_\epsilon'-\zeta'}{U_\epsilon}
 +\frac{\zeta'}\zeta\frac{\zeta-U_\epsilon}{U_\epsilon}.
$$

Both terms are $O(\epsilon\eta^{-5})$. The exact normalization has
log derivative $\gamma'/\gamma+
\epsilon\operatorname{Log}(s/(2\pi))/(8s)$. Therefore, with
$H_\epsilon=\xi_{-\epsilon}'/\xi_{-\epsilon}$ and
$K_\epsilon(s)=H_\epsilon(J_\epsilon(s))J_\epsilon'(s)$,

$$
K_\epsilon(s)-H_0(s)=O(\epsilon\eta^{-5}),\qquad
|H_0(s)|\ll\eta^{-1}+\log(|s|+2).
\tag{VE7}
$$

All constants are independent of $A,\eta,\epsilon,y$.

### Transport both complete coefficients near their singularities

Reuse the exact derivative (NH15):

$$
\widehat F_A'(z)=A^{z-1}h_L(z),\qquad
h_L(z)=\frac1{z(1-z)}-\frac1{Lz^2}.
$$

Put $r=|b+iy|$, $\kappa=\epsilon L/4\le1/4$ and
$Q_\epsilon(s)=\widehat F_A(J_\epsilon(s))+
\widehat F_A(1-J_\epsilon(s))$.
On the two unshifted lines, the rational brackets and their derivatives
obey the joint bounds $C\eta^{-2}r^{-2}$ and
$C\eta^{-3}r^{-3}$. Integrate the derivative to the corresponding
imaginary infinity, where (NH2) gives zero, and integrate its
$e^{\pm iLt}$ factor once by parts. Since $L\ge2$, this gives

$$
|Q_0(s)|\ll A^\eta\eta^{-3}r^{-2}.
$$

Each ordinate sign uses its own branch; at $y=0$ take the one-sided
limits. The reflected line has exponential factor $A^{-1-\eta}$,
which is bounded by $A^\eta$.

After reducing $c$ if needed, every segment from $s$ to
$J_\epsilon(s)$ stays in $\Re z>1+\eta/2$. Its ordinate retains
its sign, $|z|\asymp r$, and $|1-z|\ge c_3\eta r$; the reflected
segment pays these same distances with the roles interchanged.
The displacement is $O(\epsilon\log(r+2))$, and the right-hand
exponential factor is at most $CA^\eta r^\kappa$.
The reflected exponential factor is at most $CA^{-1-\eta}$,
using $\epsilon L\le1$ when the real displacement is negative.
Consequently

$$
\begin{aligned}
|Q_\epsilon-Q_0|&\ll
 \epsilon A^\eta\eta^{-2}\log(r+2)r^{\kappa-2},\\
|Q_\epsilon|&\ll
 A^\eta\eta^{-3}\log(r+2)r^{\kappa-2}.
\end{aligned}
\tag{VE8}
$$

The cancellation in $\widehat F_A$ is retained; neither coefficient
is replaced by its leading term.

### Keep the all-height contour, slit and pole corrections

The injectivity, boundary-graph and properness argument in (NH17)
applies unchanged to the line $\Re s=b$: $\Re s>1$ is enough
for its positive secant real part. Equation (VE6) now pays its
entire right-hand exterior. Functional reflection pays the left-hand
exterior. With $b_\epsilon=J_\epsilon(b)>1$, the exact balance is

$$
Z_\epsilon(A)=\frac1{2\pi i}\int_{b-i\infty}^{b+i\infty}
 Q_\epsilon(s)K_\epsilon(s)\,ds
 +\log\frac{\xi_{-\epsilon}(b_\epsilon)}{\xi_{-\epsilon}(1)}
 -\frac{H_\epsilon(0)}{AL}.
\tag{VE9}
$$

The principal cut jump remains $+2\pi i$ on $x>1$, and the
coefficient residue at zero remains $1/(AL)$. The real logarithms
are valid by positivity of the original Fourier kernel. No cut or
pole term is absorbed into an unspecified main trace.

Reuse the complete deformed zero count, Hadamard logarithmic derivative
and good-height construction from (NH10), (NH17). At each fixed
$A,\eta,\epsilon$, the two boundary curves still have real width
$O(\log T)$, and the complete coefficients have the same
$T^{\kappa-2}$ bound. Their horizontal ends therefore tend to zero
with the retained $O_{A,\eta,\epsilon}(T^{\kappa-1}\log^2T)$
allowance. No new zero trajectories, simplicity hypothesis or finite
spectrum truncation is introduced. The vertical integrals are
absolutely convergent by (VE7)–(VE8).

Subtract (VE9) at zero time, on the same line. Equations (VE7)–(VE8)
give

$$
\left|\frac1{2\pi i}\int
 [Q_\epsilon K_\epsilon-Q_0H_0]\,ds\right|
\ll\epsilon A^\eta\eta^{-8}
 \int_{\mathbb R}r^{\kappa-2}\log^2(r+2)\,dy
\ll\epsilon A^\eta\eta^{-8}.
$$

Here $1<b\le3/2$ and $\kappa\le1/4$, so the last integral has
an absolute uniform bound. The slit and pole differences are
$O(\epsilon)$ uniformly in $\eta$: $b\in[1,3/2]$,
$b_\epsilon-b=O(\epsilon)$, and the positive Fourier values,
their first real derivatives and their time derivatives have common
bounds on a fixed real compact interval. These are exactly the
kernel-moment and denominator inputs already used in (NH18).
Also $1/(AL)\le1$. This proves (VE1) with all corrections paid;
$A^{1/L}=e$ gives (VE2).

### A broader common time, without a signed Robin conclusion

Choose one time for the whole spectrum at each clock,

$$
\epsilon(A)=\min\{(c/2)L^{-4},\ A^{-1/2}L^{-10}\}.
$$

Then (VE2), with the unchanged positive elementary correction
$r_A$ from (G9), gives

$$
\boxed{-\sqrt A L I_\psi(A)
=\sqrt A L Z_{\epsilon(A)}(A)+r_A+O(L^{-1}).}
\tag{VE10}
$$

The implicit constant is absolute. For sufficiently large $A$ the
second branch is selected, so this comparison allows an asymptotically
larger common negative time than $A^{-3}$. It never selects a
different time per zero.

The original conditional least integer attaining the global Robin-ratio
maximum under a violation remains the source, with
$A=\log N>(7/2)10^{46}$; it is not replaced by a least counterexample.
The complete original coefficients, actual real parts, both signs,
all heights and multiplicities return through (VE1), and $r_A$ and
the strict core remain required. No numerical $c,C$ or finite-clock
slack has been certified. The signed upper bound for
$\sqrt A L Z_{\epsilon(A)}(A)$, the complete Robin target and RH
remain unproved. The original response and its accepted (NH1)–(NH18)
supplier are preserved verbatim in the Nicolas note.

## The same negative-time prime filter has different absolute budgets on different cuts

The common-time comparison (VE10) does not restore coefficient
positivity. The precise issue is the *total* negative coefficient
budget, not only the already checked negative coefficient at index
$6$. The joint estimate below keeps the same finite prime support,
the same time and the same Dirichlet coefficients throughout.

Reuse Dobner's damped Dirichlet series from (NH7)–(NH8) in
[the Nicolas note](nicolas2025comparison.md#the-subcritical-full-spectrum-absolute-boundary),
and the finite Euler coefficient definition inspected in
[Planat, arXiv:2609.37164v2](https://arxiv.org/html/2609.37164v2),
Lemma 8.1. The latter's nonnegative-head statement assumes
nonnegative heat time and a finite head; neither assumption is
extended here. Its divisor convolution and the previously checked
two-prime sign identity are reused directly. Euler products,
Dirichlet norm inequalities and the classical prime number theorem
are `literature-attested` inputs. The growing-support aggregate
budget below is a `repo-derived` paper application, without a
priority, exhaustive literature, numerical-constant or Lean claim.

For $\epsilon>0$, write $a_\epsilon(n)=
\exp[-\epsilon(\log n)^2/4]$. For a finite set of primes $P$, define

$$
\mathcal C_{\epsilon,P}(s)=D_\epsilon(s)
 \prod_{p\in P}(1-a_\epsilon(p)p^{-s})
=\sum_{n\ge1}c_{\epsilon,P}(n)n^{-s},
$$

$$
c_{\epsilon,P}(n)=
 \sum_{d\mid(n,\prod_{p\in P}p)}\mu(d)
 \prod_{p\mid d}a_\epsilon(p)\,a_\epsilon(n/d).
\tag{VF1}
$$

This coefficient formula agrees with the inspected finite filter
when $P=\{2,3,5\}$. For fixed $\epsilon>0$ and finite $P$, the
series is absolutely convergent on every vertical line: Gaussian
damping makes $\sum_n a_\epsilon(n)n^{-\sigma}$ finite for every
real $\sigma$, and the finite divisor convolution preserves that
property. Thus the full negative mass

$$
\mathcal N_{\epsilon,P}(\sigma)=
 \sum_{n\ge1}[-c_{\epsilon,P}(n)]_+n^{-\sigma}
\tag{VF2}
$$

is finite at each fixed time. No infinite positive-time Dirichlet
series is asserted.

### The right-of-Euler budget is uniformly small

For every finite $P$, every $0<\eta\le1/2$ and every $\epsilon>0$,

$$
\boxed{\mathcal N_{\epsilon,P}(1+\eta)
 \le C\epsilon\eta^{-4}.}
\tag{VF3}
$$

To pay the coefficient norm, use
$\|\sum b_nn^{-s}\|_\sigma=\sum|b_n|n^{-\sigma}$, which is
submultiplicative for absolutely convergent Dirichlet series.
At zero time the coefficient of
$\zeta(s)\prod_{p\in P}(1-p^{-s})$ is the nonnegative indicator
$\mathbf1_{(n,\prod P)=1}$. The negative part in (VF2) is bounded
by the coefficient norm of the difference from that zero-time
series.

Let $E_\epsilon=\prod_{p\in P}(1-a_\epsilon(p)p^{-s})$ and
$E_0=\prod_{p\in P}(1-p^{-s})$. On $\sigma=1+\eta$, Euler
products and $1-e^{-x}\le x$ give

$$
\begin{aligned}
\|E_\epsilon\|_\sigma&\le\prod_{p\in P}(1+p^{-\sigma})
 \le\zeta(\sigma)\ll\eta^{-1},\\
\|D_\epsilon-\zeta\|_\sigma&\le
 (\epsilon/4)\zeta''(\sigma)\ll\epsilon\eta^{-3},\\
\|E_\epsilon-E_0\|_\sigma&\le
 (\epsilon/4)\zeta(\sigma)
 \sum_p(\log p)^2p^{-\sigma}\ll\epsilon\eta^{-3}.
\end{aligned}
$$

For the last bound, keep the Euler logarithmic derivative:

$$
\sum_p(\log p)^2p^{-\sigma}
\le(\log\zeta)''(\sigma)
\le\frac{\zeta''(\sigma)}{\zeta(\sigma)}
\ll\eta^{-2}.
$$

The last inequality uses $\zeta''(1+\eta)\ll\eta^{-3}$ and
$\zeta(1+\eta)\ge1/\eta$. Subtract the two series as
$(D_\epsilon-\zeta)E_\epsilon+
\zeta(E_\epsilon-E_0)$. Both products have norm
$O(\epsilon\eta^{-4})$, independently of $P$, proving (VF3).
This uses a coefficient norm; a small function-value error alone
would not pay it.

### Every finite filter containing 2 has a large interior budget

Fix $0<\sigma<1$ and put $d=1-\sigma>0$. Suppose only that
$2\in P$. For every prime $q\ne2$, the already checked two-prime
coefficient identity gives

$$
c_{\epsilon,P}(2q)=a_\epsilon(2)a_\epsilon(q)
 \bigl(e^{-\epsilon\log2\log q/2}-1\bigr)<0.
\tag{VF4}
$$

If $q\notin P$, the two divisor terms are
$a_\epsilon(2q)-a_\epsilon(2)a_\epsilon(q)$. If $q\in P$, the
four terms are
$a_\epsilon(2q)-2a_\epsilon(2)a_\epsilon(q)+
a_\epsilon(2)a_\epsilon(q)$, giving the same coefficient.
No other prime of $P$ divides $2q$. Adding more primes to the
same filter therefore cannot remove this entire negative family.
These are actual distinct integer indices, not independently
chosen phases.

Let $X=e^{2d/\epsilon}$ and
$J=\lfloor\epsilon^{-1/2}\rfloor$. Use the disjoint prime bins
$[2^jX,2^{j+1}X)$ for $0\le j<J$. The classical prime number
theorem gives one absolute $b>0$ such that every bin starting at
$Q\ge X$, for sufficiently small $\epsilon$, contains at least
$bQ/\log Q$ primes. This is the uniform all-$Q$ consequence of
that theorem, not a short-interval or RH-dependent estimate.
Every one of these primes supplies (VF4), regardless of membership
in $P$; no support deletion or bound on $\max P$ is needed.

Write $h=\log2$, $u_j=\log(2^jX)=2d/\epsilon+jh$.
For every prime in that bin,

$$
1-e^{-\epsilon h\log q/2}\ge1-2^{-d},\qquad
q^{-\sigma}a_\epsilon(q)\ge
2^{-\sigma}e^{-\sigma u_j-\epsilon(u_j+h)^2/4}.
$$

Combining this with the bin count, $2^{-\sigma}a_\epsilon(2)$
from (VF4), and the exact exponent identity

$$
d u_j-\frac\epsilon4(u_j+h)^2
=\frac{d^2}\epsilon-\frac\epsilon4(jh)^2
 -\frac\epsilon2u_jh-\frac\epsilon4h^2
$$

shows that every bin contributes at least
$b_\sigma\epsilon e^{d^2/\epsilon}$, for a constant
$b_\sigma>0$ independent of $P,j,\epsilon$. Indeed,
$j<\epsilon^{-1/2}$ bounds all subtracted exponents by constants,
and $u_j\le(2d+h)/\epsilon$ for $\epsilon\le1$. For
$\epsilon\le1/4$, $J\ge1/(2\sqrt\epsilon)$. Hence

$$
\boxed{\mathcal N_{\epsilon,P}(\sigma)
 \ge b_\sigma'\sqrt\epsilon\,
 e^{(1-\sigma)^2/\epsilon}}
\tag{VF5}
$$

for sufficiently small $\epsilon$, uniformly over every finite
$P$ containing $2$.
Only a negative subfamily was used; all other coefficients remain
in (VF2).

### Apply both budgets at the same common Robin clock

At an actual integer $N$ with $2\mid N$, set
$P=P_N=\{p:p\mid N\}$ and $A=\log N$. The same selected
least global Robin-ratio maximizer has initial prime support,
and hence $2\mid N$, by the
[retained selected-source reduction](../Analytic/polak2026finiterobinca.md#application-at-the-same-critical-source-and-clock).
No separate maximizing integer or artificial prime profile is
substituted. The uniformity in (VF5) permits this actual support
without a cardinality, largest-prime or additional resource
assumption.

For the common time already chosen in (VE10),
$\epsilon(A)=\min\{(c/2)L^{-4},A^{-1/2}L^{-10}\}$, the time tends to zero. The two budgets for that
*same* filtered series are

$$
\begin{aligned}
\sqrt A L\,\mathcal N_{\epsilon(A),P_N}(1+1/L)
 &\le CL^{-5}\longrightarrow0,\\
\mathcal N_{\epsilon(A),P_N}(\sigma)
 &\ge b_\sigma'\sqrt{\epsilon(A)}
 e^{(1-\sigma)^2/\epsilon(A)}\longrightarrow\infty
 \quad(0<\sigma<1\text{ fixed}).
\end{aligned}
\tag{VF6}
$$

Thus the full raw negative-coefficient cost cannot be treated as a
vanishing soft correction on a fixed interior cut merely because
the common negative time tends to zero. It *can* have a small
coefficient budget on the paid right-of-Euler cut. The Gaussian
saddle, prime density and full-filter invariance of the two-prime
coefficient are the joint inputs beyond the isolated sign witness.
These are uniform eventual estimates over the allowed integer
family, without assuming an infinite sequence of selected global
maximizers or certifying the bound at the standing finite clock.

This is an absolute coefficient budget, not a signed trace bound.
For every real $\sigma>0$ the same filtered value is in fact
$D_\epsilon(\sigma)\prod_{p\in P}(1-a_\epsilon(p)p^{-\sigma})>0$;
large negative mass coexists with compensating positive mass.
Finite-head statements, different groupings, extra kernels and
paid signed cancellation are not excluded. In particular (VF5)
does not refute the positive-time source, contradict (VE10),
establish negative signed divergence, or give a Robin counterexample.

The original full $I_\psi(A)$ target, complete zero coefficients,
actual real parts, both signs, infinite heights and multiplicities,
elementary correction and strict core remain unchanged and unproved.
No bound for the signed main trace in (VE10) or the actual
$D_a$ lower allowance is obtained. The constants and asymptotic
starting clocks have not been numerically certified; RH remains
unproved.
