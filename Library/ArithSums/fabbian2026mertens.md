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

## A uniform shrinking-time cutoff for the complete signed trace

The fixed-parameter tail after (NH11) in
[the Nicolas note](nicolas2025comparison.md#the-subcritical-full-spectrum-absolute-boundary)
does not state a bound uniform as the clock and heat time change together.
The following supplies that interface using the already paid near-Euler
exterior in (VE6). The complete coefficient, heat convolution, positive
Fourier kernel, Jensen theorem, contour balance and original response
comparison are reused; none is reconstructed as a new source theorem.
This is a `repo-derived` paper-level parameter application, without an
exhaustive literature, mathematical-priority, numerical-constant or Lean
claim.

Keep exactly the complete principal continuation $\widehat F_A$ and
actual multiset of $\xi_{-\epsilon}$ zeros used in (VE1)–(VE10).
Assume

$$
A\ge e^2,\qquad L=\log A,\qquad 0<\eta\le\tfrac12,
\qquad 0<\epsilon\le c\eta^4,\qquad \epsilon L\le1,
\qquad \kappa=\epsilon L/4.
$$

Use the absolute $c$ from (VE1), chosen small enough that
$\epsilon\le1/2$ throughout this domain. There is an absolute $C<\infty$
such that, for every $T\ge2$,

$$
\boxed{
\sum_{\substack{\xi_{-\epsilon}(w)=0\\|\Im w|>T}}
 |\widehat F_A(w)|
\le \frac{C A^\eta}{L}
 T^{\kappa-1}\log(T+2).
}
\tag{VG1}
$$

The sum includes both ordinate signs, every actual real part and every
multiplicity. Its constant is independent of $A,\eta,\epsilon,T$.
This strengthens the parameter scope of the fixed-parameter tail;
it gives no sign to the retained head.

### The existing exterior confines every height uniformly

Put $b=1+\eta$ and write the right boundary from (VE9) as
$J_\epsilon(b+iu)$. Its ordinate and real part are

$$
y=u+\frac\epsilon4\arctan(u/b),\qquad
x=b+\frac\epsilon4\log\frac{\sqrt{b^2+u^2}}{2\pi}.
$$

The ordinate is strictly increasing and has the sign of $u$, so
$|u|\le|y|$. The zero-free exterior and reflected boundary already
proved for (VE9) enclose **all** zeros, including bounded heights.
As $1<b\le3/2$, their actual coordinates $w=\beta+iy$ obey

$$
\boxed{
-\eta-\frac\epsilon4\log(|y|+2)
\le\beta\le
1+\eta+\frac\epsilon4\log(|y|+2).
}
\tag{VG2}
$$

No asymptotic exceptional set or new zero trajectory is used.
The weaker denominator-free upper envelope follows from
$\sqrt{b^2+u^2}/(2\pi)\le|y|+2$; functional reflection gives the lower
one. In particular $A^{\beta-1}\le A^\eta(|y|+2)^\kappa$.

The positive-kernel Jensen argument of (NH10) also has a common center
lower bound on this small-time interval:

$$
\xi_{-\epsilon}(1/2)\ge\xi_{-1/2}(1/2)>0,
\qquad
\max_{|s-1/2|\le R}|\xi_{-\epsilon}(s)|
\le2\xi_0(1/2+R).
$$

These are inequalities for the deformed function itself. Real Stirling
growth and Jensen at radii $R$ and $2R$ therefore give a disk count
$C R\log(R+2)$ with an absolute constant. By (VG2), for $T\ge2$ and
$|y|\le T$,

$$
|\beta-1/2|\le1+\tfrac18\log(T+2)\le T.
$$

Thus these zeros lie in $|w-1/2|<2T$, and the complete count satisfies

$$
\boxed{
\#\{w:\xi_{-\epsilon}(w)=0,\ |\Im w|\le T\}
\le C T\log(T+2),\qquad T\ge2.
}
\tag{VG3}
$$

Multiplicity is retained in both Jensen and this count. No original-zeta
zero-count theorem has been assigned to different zeros.

### Keep the cancellation in the complete coefficient

Reuse (NH15), with

$$
\widehat F_A'(z)=A^{z-1}h_L(z),\qquad
h_L(z)=\frac1{z(1-z)}-\frac1{Lz^2}.
$$

For every real $\beta$, $t\ge2$ and $L\ge2$,

$$
|h_L(\beta+it)|\le\frac{1+1/L}{t^2},\qquad
|h_L'(\beta+it)|\le\frac{2(1+1/L)}{t^3}.
$$

On either fixed ordinate sign, the complete coefficient tends to zero
at the corresponding imaginary infinity by (NH2). Integrate the exact
derivative along that vertical ray and integrate its $e^{\pm iLt}$
factor once by parts. Its endpoint and derivative integral give

$$
|\widehat F_A(\beta+iy)|
\le\frac{A^{\beta-1}}L
\left[\frac{1+1/L}{|y|^2}
 +\int_{|y|}^\infty\frac{2(1+1/L)}{t^3}\,dt\right]
\le\frac{3A^{\beta-1}}{L|y|^2},\qquad |y|\ge2.
$$

This bound is uniform in $\beta$ and $L$. The two principal branches
are kept separately; the positive-height ray crosses no cut, and
conjugation supplies the same bound at negative height. Neither the
$A^{z-1}/(zL)$ term nor $E_1((1-z)L)$ is estimated alone.

Combine this bound with (VG2)–(VG3) on the dyadic bands
$2^jT<|y|\le2^{j+1}T$. Since $0<\kappa\le1/4$, their entire absolute
mass is at most

$$
\frac{C A^\eta}{L}
\sum_{j\ge0}(2^jT)^{\kappa-1}\log(2^{j+1}T+2)
\le\frac{C A^\eta}{L}T^{\kappa-1}\log(T+2).
$$

The geometric sums, including their $j$ factors, have common bounds
because $2^{\kappa-1}\le2^{-3/4}<1$. This proves (VG1) over all omitted
heights, rather than on a selected subsequence.

### One common time now gives a finite signed head

Use the **same** time already chosen for the full spectrum in (VE10):

$$
\epsilon(A)=\min\{(c/2)L^{-4},\ A^{-1/2}L^{-10}\},
\qquad \eta=1/L,\qquad T(A)=\sqrt A\,L^3.
$$

Here $A^\eta=e$. Moreover $\epsilon(A)\le e^{-L/2}L^{-10}$,
$\log T=L/2+3\log L$, and $\log L\le L$ for $L\ge2$ give
$\kappa\log T\le(7/8)e^{-L/2}L^{-8}<1$.
Also $\log(T+2)\le4L$. Hence (VG1) yields the joint bound

$$
\boxed{
\sqrt A L
\sum_{\substack{\xi_{-\epsilon(A)}(w)=0\\|\Im w|>T(A)}}
 |\widehat F_A(w)|\le C L^{-2}.
}
\tag{VG4}
$$

It holds throughout the stated parameter domain with an absolute
constant, without asserting that the second time branch is selected at
one numerical clock. Define the finite, real signed head

$$
Z^{\rm head}_{\epsilon(A)}(A)=
\sum_{\substack{\xi_{-\epsilon(A)}(w)=0\\|\Im w|\le T(A)}}
 \widehat F_A(w).
$$

Positivity of the original Fourier kernel excludes real zeros at this
negative time. The head is real by conjugation; its complete multiplicity
count is at most $C\sqrt A L^4$ by (VG3). Finiteness is not a claim of a
practical algorithm, computed zeros or certified numerical constants.

The exact signed tail has absolute normalized bound (VG4). Combining
it with the unchanged complete comparison (VE10) gives

$$
\boxed{
-\sqrt A L I_\psi(A)
=\sqrt A L Z^{\rm head}_{\epsilon(A)}(A)+r_A+\rho_A,
\qquad |\rho_A|\le C_1L^{-1}+C_2L^{-2}.
}
\tag{VG5}
$$

The $L^{-1}$ term is the existing whole-trace transport allowance; the
$L^{-2}$ term pays the entire omitted deformed spectrum. The original
positive elementary correction $r_A$ is still present. The principal
cut and pole compensation remain paid by the reused (VE9)–(VE10);
no additional correction is silently discarded by the head cutoff.

For the same conditional least integer attaining the global Robin-ratio
maximum under a violation, $A=\log N>(7/2)10^{46}$, this supplies a finite
head with a joint tail allowance. Its **signed upper bound** remains
unproved. To reach the original sufficient target one still needs to
control the head together with $r_A$ and $\rho_A$ against
$\mathcal E(L)$; the strict core remains required. An asymptotic tail
allowance is not a numerical finite-clock certificate or a uniform
positive margin. The original real parts, both signs, all heights and
multiplicities return through the complete response comparison.
No RH conclusion or superiority to the already retained original-zero
cutoffs is asserted.

## Original density can be transported to a smaller negative-heat head

The common-time head in (VG5) need not retain the full height
$\sqrt A L^3$. The additional interface below transports the existing
original-zero density and zero-free tail to the actual negative-heat
zeros on a growing finite band. No density theorem is assumed for a
different function, and no simple-zero trajectory is used.

Reuse [Lagarias, arXiv:math/0404394v4](https://arxiv.org/pdf/math/0404394v4),
Theorem 2.1(4), printed p.7, and Lemma 6.1, equation (6.8), printed p.27.
The former gives the usual counting formula with an $O(\log T)$
remainder, hence $O(\log(y+3))$ original zeros in a fixed-length height
interval, with multiplicities. The latter supplies the local
logarithmic-derivative expansion in a fixed strip. Its Riemann
specialization is used at heights at least $10$, away from the zeta
pole and trivial zeros. The Gamma logarithmic derivative, vertical
Stirling bounds, fixed-strip polynomial zeta growth, exact negative-time
Gaussian convolution, Rouché theorem, and the complete (VE)–(VG)
interfaces are also reused. The cached original Lagarias text and the
already inspected Dobner convolution are the source inputs; their
proofs are not reconstructed or independently certified here.

This is a `repo-derived` paper-level joint transport application. No
exhaustive literature, mathematical-priority, Lean, computed-zero or
numerical finite-clock claim is made.

### Relative heat control away from the original zero multiset

Write $\xi=\xi_0$, and let $\mathcal Z_0$ be its actual zero multiset.
There are absolute $c,C>0$ with the following property. For $Y\ge10$,
put $q=\log(Y+10)$. Assume

$$
-1\le\Re s\le2,\qquad 10\le\Im s\le Y,\qquad
\operatorname{dist}(s,\mathcal Z_0)\ge\delta,
$$

$$
e^{-q}\le\delta\le1/10,
\qquad 0<\epsilon\le c\delta^2/q^2.
$$

Then the actual, unshifted heat functions satisfy

$$
\boxed{
\left|\frac{\xi_{-\epsilon}(s)}{\xi(s)}-1\right|
\le C\epsilon q^2/\delta^2.
}
\tag{VH1}
$$

The denominator is paid below; an absolute function-value error is
not substituted for this relative estimate.

Put $y=\Im s$. The cited local formula and the Gamma factor give
$|\xi'/\xi|\le Cq/\delta$ on the radius-$\delta/2$ neighborhood of
$s$; on radius-$\delta/4$ disks there Cauchy gives
$|(\xi'/\xi)'|\le Cq/\delta^2$, with harmless changes to these radii.
More explicitly, at a point $s+iu$, $|u|\le\delta/2$, the
radius-$\delta/4$ disk stays at distance at least $\delta/4$ from every
zero and in the fixed wider strip of Lemma 6.1. The local count is
$O(q)$, and the remaining Gamma and local-formula terms are $O(q)$.
Consequently, for $G(v)=\xi(s+iv)/\xi(s)$ and $|v|\le\delta/2$,

$$
|G(v)-1-iv(\xi'/\xi)(s)|
\le Cq^2\delta^{-2}v^2 e^{Cq|v|/\delta}.
\tag{VH2}
$$

To pay the whole Gaussian tail, remove the original local factors

$$
P_y(z)=\prod_{\substack{\rho\in\mathcal Z_0\\|\Im\rho-y|<2}}(z-\rho),
\qquad g_y(z)=\xi(z)/P_y(z).
$$

Repeated factors retain multiplicities. Their number is at most $Cq$.
In $-1\le\Re z\le2$, $|\Im z-y|\le1/2$, the source local formula,
with the extra factors of ordinate distance at least one bounded
separately, gives $g_y'/g_y=O(q)$. This function is analytic and
nonzero throughout the indicated rectangle. Compare its modulus along
the horizontal segment from $2+iy$ to $s$. Every numerator local factor
at $s$ has modulus at least $\delta$, and every factor at $2+iy$ has
modulus at most $3$. Thus

$$
|\xi(s)|\ge|\xi(2+iy)|\exp[-Cq\log(3/\delta)].
$$

The Euler inverse bound at $\Re s=2$ and vertical Stirling supply a
uniform lower bound for $|\xi(2+iy)|$. Fixed-strip polynomial zeta
growth and vertical Stirling supply a uniform upper bound for
$|\xi(\sigma+i(y+v))|$; compact heights include the removable Gamma
singularities of the completed function. As
$\log(3/\delta)\le q+\log3$, these bounds combine, for every real $v$,
to give fixed absolute $B,C$ with

$$
|G(v)|\le C e^{Cq^2}(1+|v|)^B e^{\pi|v|/4}.
\tag{VH3}
$$

The existing exact vertical Gaussian identity is

$$
\frac{\xi_{-\epsilon}(s)}{\xi(s)}
=\frac1{\sqrt{\pi\epsilon}}\int_{\mathbb R}
 e^{-v^2/\epsilon}G(v)\,dv.
$$

Subtract $1+iv(\xi'/\xi)(s)$ before estimating: its Gaussian average
is exactly one. On $|v|\le\delta/2$, (VH2) and square completion give
$C\epsilon q^2/\delta^2$, since $\epsilon q^2/\delta^2\le c$.
On the complement, (VH3) gives

$$
C\exp[Cq^2-\delta^2/(8\epsilon)].
$$

The polynomial and $e^{\pi|v|/4}$ factors are integrated against the
remaining half-Gaussian, with a common bound for $\epsilon\le1/2$.
Choose $c$ small enough to absorb $Cq^2$ into half the negative exponent.
Then $e^{-\delta^2/(16\epsilon)}\le16\epsilon/\delta^2$ pays this
part. The subtracted affine tail has the same bound using
$|\xi'/\xi(s)|\le Cq/\delta$. This proves (VH1) with constants
independent of $Y,s,\delta,\epsilon$.

### Small clusters transport multiplicities without separation assumptions

Return to $L=\log A$ and the same common $\epsilon(A)$ from (VE10).
Set

$$
U=\sqrt A L^3,\qquad h=L^{-2},\qquad
Y=U+2,\qquad q=\log(Y+10),\qquad \delta=\frac h{Kq},
$$

where the fixed absolute $K$ is larger than a suitable multiple of the
original local-count constant. For sufficiently large $A$, the domain
conditions of (VH1) hold and

$$
\epsilon(A)q^2/\delta^2
=K^2\epsilon(A)q^4h^{-2}
\le C A^{-1/2}L^{-2}\longrightarrow0.
\tag{VH4}
$$

Here $q\asymp L$, $\delta\asymp L^{-3}$ and $\delta\ge e^{-q}$
eventually. No particular numerical starting clock is certified.

Take the union of radius-$r$ disks about every distinct original zero,
with one common $\delta\le r\le2\delta$. Repeated zeros are single
centers but retain their multiplicities in counting. Choose $r$ to
avoid tangencies and multiple boundary intersections for the finite
collection of disks in the working band. The relevant union components
are finite and have diameter at most $h$.

Here is the bound that prevents a long chain. For a component meeting
an interior point of the working band, a chain of neighboring centers
has successive distances at most $4\delta$. Before a chain could leave
the unit neighborhood of its first center, its centers have ordinates
in one fixed-length interval, containing at most $Cq$ original zeros.
It cannot travel a unit distance because $4\delta Cq<1/2$ for large
$A$. It therefore stays in that neighborhood. Its complete center count
is at most $Cq$, and its disk-union diameter is at most
$4\delta(Cq+1)\le h$, by the fixed choice of $K$.
Thus no unproved minimum spacing or simplicity is needed. Components
meeting the working band remain at least $10$ in height and below $Y$;
there is no artificial truncation boundary through a cluster.

At the boundary of each such component, distance from every original
zero is at least $r\ge\delta$. Equation (VH1), with (VH4), makes
$|\xi_{-\epsilon(A)}-\xi|<|\xi|$ on that complete boundary.
Rouché, or the argument principle for the finite disk union including
any hole boundaries, gives the same total zero multiplicity inside.
Outside all these disks, (VH1) excludes deformed zeros in the working
band. Hence the original and deformed multisets in each component
can be matched, with

$$
\boxed{|w-\rho|\le h=L^{-2}.}
\tag{VH5}
$$

This is a multiplicity-preserving matching inside small clusters,
not an assertion of simple trajectories or an inherited global density
law. Conjugation supplies the lower-height version. The matching need
not itself be used as a numerical algorithm.

### Reuse the original weighted tail in the correct direction

The existing smaller-cut calculation in
[the Nicolas note](nicolas2025comparison.md#a-smaller-moving-cut-from-joint-density-and-zero-free-support)
uses the actual original spectrum, Chourasiya–Simonič's inclusive
density estimate and Johnston–Yang's stated zero-free region. Reuse
that already paid calculation, including its weighted intermediate
quantity, rather than re-proving the density theorem or reassigning it
to deformed zeros. With

$$
R=57.54,\qquad \Omega=(L/\log L)^{1/3},\qquad
\kappa_*=(28R)^{-1},\qquad T_0=A^{1/4}e^{-\kappa_*\Omega},
$$

it supplies, for sufficiently large $A$,

$$
B_2(A;T_0):=
\sum_{\substack{\rho=\beta+i\gamma\in\mathcal Z_0\\\gamma>T_0}}
\frac{A^{\beta-1/2}+A^{1/2-\beta}}{\gamma^2}
\le C b(A),
$$

$$
b(A)=L A^{-1/8}e^{\kappa_*\Omega}
 +L^3e^{-\Omega/(14R)}+L^3A^{-1/14}.
\tag{VH6}
$$

This is the positive weighted-zero upper bound produced by the existing
layer calculation, not a reverse inference from its signed-response
upper bound. Reflection and conjugation preserve every multiplicity.

Put $S(A)=2T_0$. Work at sufficiently large $A$ that
$S>12$, $U>S$ and $h<1$. The working band for (VH5) is
$S<|\Im w|\le U$. By (VG2), its deformed real parts are in $[-1,2]$.
Every relevant cluster stays in the high fixed strip and away from the
outer height limits needed for (VH1). The matching assigns every such
$w$ to a distinct original zero occurrence with
$|\Im\rho|>T_0$, since $S-h>T_0$. The factor two in $S$ pays the
lower-cut boundary without assuming a zero-free cutoff ordinate.

Use the complete-coefficient bound proved for (VG1), not a leading-term
replacement. For each matched occurrence,

$$
\sqrt A L|\widehat F_A(w)|
\le\frac{3A^{\Re w-1/2}}{|\Im w|^2}
\le\frac{12 A^h A^{\Re\rho-1/2}}{|\Im\rho|^2}.
$$

Here $|\Im w|\ge|\Im\rho|-h\ge|\Im\rho|/2$. The matching is injective
on the retained occurrences. For the complete original multiset,
reflection followed by conjugation identifies the sum of
$A^{\beta-1/2}/\gamma^2$ over both signs with $B_2(A;T_0)$.
Since $A^h=e^{1/L}$, the whole matched middle costs at most
$C b(A)$. Beyond $U$, the unchanged (VG4) costs $CL^{-2}$.
Consequently the **entire** deformed suffix obeys

$$
\boxed{
\sqrt A L
\sum_{\substack{\xi_{-\epsilon(A)}(w)=0\\|\Im w|>S(A)}}
 |\widehat F_A(w)|
\le C b(A)+CL^{-2}=O(L^{-2}),
\quad S(A)=2A^{1/4}e^{-\Omega/(28R)}.
}
\tag{VH7}
$$

For the last equality, $\Omega/\log L\to\infty$ and $\Omega/L\to0$
give $b(A)=o(L^{-2})$. All constants are independent of $A$; the bound
is eventual, with no certified numerical threshold. The actual common
time is unchanged and is not chosen separately for a zero or a cluster.

### The reduced head still needs its signed bound

Let $Z^{\rm small}_{\epsilon(A)}(A)$ be the same complete finite signed
zero sum as in (VG5), with inclusive height $S(A)$ in place of $U$.
It is real by conjugation. The unchanged uniform count (VG3) gives
$O(A^{1/4}L e^{-\Omega/(28R)})$ zero occurrences in this head.
Combining the complete suffix bound with (VE10) yields

$$
\boxed{
-\sqrt A L I_\psi(A)
=\sqrt A L Z^{\rm small}_{\epsilon(A)}(A)+r_A+\widetilde\rho_A,
\qquad
|\widetilde\rho_A|\le C_1L^{-1}+C_2b(A)+C_3L^{-2}.
}
\tag{VH8}
$$

The elementary correction remains the positive original $r_A$.
The original complete coefficients, actual real parts, both signs,
all heights and multiplicities, and the already paid cut and pole
compensation return through (VE10). The smaller head pays no new
signed main upper bound.

The original source is still the conditional least integer attaining
the global Robin-ratio maximum under a violation, with
$A=\log N>(7/2)10^{46}$. That standing lower clock alone is not a
certificate that this source exceeds the unspecified eventual threshold
of (VH7)–(VH8). The earlier all-clock (VG) interface remains available.
A proof still must control the same head and corrections against the
original $\mathcal E(L)$ and retain the strict core, including any
uncovered finite clock range. No Robin or RH conclusion is supplied.

## One positive heat time pays a further finite signed Robin window

The smaller negative-time head above still needs its signed upper bound.
A separate finite payment is available from the already retained
positive-time resolvent (HR1) and exact real-parameter explicit formula.
This payment uses the actual original zeros throughout. It does not
require the eventual eligibility threshold of (VH7), transfer original
zero density to another function, or assume RH above the verified height.

Reuse the complete coefficient remainder (H1), the original positive
elementary correction after (G9), and the strict core (G6)–(G7) in
[the Nicolas note](nicolas2025comparison.md). The existing finite payment
(GL3)–(GL4) already excludes the same selected source through
$A\le(7/2)10^{46}$. The new interval is

$$
\frac72\,10^{46}<A\le4\cdot10^{46},\qquad
L=\log A,\qquad H=3\cdot10^{12},\qquad
U=\frac7{2\cdot10^{24}}.
$$

The source is the conditional least integer $N>5040$ attaining the
global Robin-ratio maximum under a violation, with $A=\log N$.
It is not the least counterexample. The earlier verified-height and
complete reciprocal-square inputs are unchanged:

$$
c_0:=\sum_\rho\frac{m_\rho}{\rho(1-\rho)}<0.05,
\qquad
S_2(H):=\sum_{\gamma>H}\frac{m_\rho}{\gamma^2}
<1.48\cdot10^{-12}.
\tag{VI1}
$$

Every zero with $|\gamma|\le H$ is on the critical line under the
same cited finite-verification premise. All sums below retain actual
real parts and multiplicities, and include both ordinate signs.
This is a paper-level application of existing analytic inputs, with
no new source theorem, zero computation, mathematical-priority claim
or Lean certification.

### Split the whole rational response at one common time

Put $d_\rho=\rho(1-\rho)$ and write the normalized original response as

$$
\sqrt A L Z_{\rm orig}(A)
=(1+1/L)\sum_\rho m_\rho\frac{A^{\rho-1/2}}{d_\rho}
 +R_A.
$$

This is the full (H1) coefficient, not a leading-term replacement:

$$
|R_A|\le\frac{2(L+2)}{L^2}
 \sum_\rho m_\rho
 \frac{A^{\beta-1/2}}{|\rho||1-\rho|^2}.
\tag{VI2}
$$

The exact existing heat-resolvent identity gives

$$
\sum_\rho m_\rho\frac{A^{\rho-1/2}}{d_\rho}
=\sum_\rho m_\rho
 \frac{A^{\rho-1/2}e^{-Ud_\rho}}{d_\rho}
 +A^{-1/2}\int_0^U\mathcal H(u,u-L)\,du,
\qquad
\mathcal H(u,v)=\sum_\rho m_\rho e^{u\rho^2-v\rho}.
\tag{VI3}
$$

Here $\Re d_\rho=\gamma^2+\beta(1-\beta)>0$.
The absolute integral per occurrence is at most
$\sqrt A/\gamma^2$, and the full reciprocal-square sum is finite.
Thus the whole-zero sum and heat integral interchange absolutely.
There is no height truncation, exceptional zero or value inserted at
$u=0$. Reflection and conjugation make these complete expressions real.

### Use the signed prime formula before taking an upper bound

Reuse Kamiya–Suzuki, *An asymptotic formula for a sum involving zeros
of the Riemann zeta-function*, Publications de l'Institut Mathématique
76(90) (2004), 81–88,
[Lemma 2.1, printed p.83, and Lemma 3.1, printed p.84](http://elib.mi.sanu.ac.rs/files/journals/publ/96/n090p081.pdf).
Their exact formula holds for every $u>0$ and real $v$; no fixed-frequency
asymptotic is used. At $v=u-L$, its pole terms are $A+1$.
Both prime sums, the $\log\pi$ Gaussian term and the convolution
$E*\mathcal G_u$ are subtracted nonnegative quantities; the latter lies
between zero and one. They retain their stated signs when taking the
following upper bound.

After multiplication by $A^{-1/2}$, the remaining Gamma term is exactly

$$
J_\Gamma(u,L)=\frac{e^{-u/4}}{2\pi}
 \int_{\mathbb R}\log|1/4+it/2|\,e^{-ut^2+itL}\,dt.
$$

In particular, its prefactor is not $A^{-1/2}$: the raw source formula
contains $e^{u/4-v/2}=\sqrt A e^{-u/4}$.
An explicit integrable allowance pays this term. For $x\ge0$,
$\log(1+x)\le\sqrt x$, and hence

$$
|\log|1/4+it/2||
\le\log4+\log(1+2|t|)
<2+\sqrt2\,|t|^{1/2}.
$$

The ordinary Gaussian integral and Gamma integral, with
$3<\pi<4$ and $\Gamma(3/4)<2$, give

$$
|J_\Gamma(u,L)|
\le\frac23\bigl(u^{-1/2}+u^{-3/4}\bigr),
\qquad
\int_0^U|J_\Gamma(u,L)|\,du
\le\frac43\sqrt U+\frac83U^{1/4}<6\cdot10^{-6}.
$$

For the last bound, $\sqrt U<2\cdot10^{-12}$ and
$U^{1/4}<2\cdot10^{-6}$. The elementary bound
$\Gamma(3/4)<4/3+e^{-1}<2$ follows directly by splitting its
positive integral at one. Thus the exact source formula, with all
favorable terms kept in its direction, yields

$$
\boxed{
A^{-1/2}\int_0^U\mathcal H(u,u-L)\,du
\le\sqrt A\,U+\frac U{\sqrt A}+6\cdot10^{-6}.
}
\tag{VI4}
$$

This is a signed upper estimate, not the source-pressure lower bound
(PH4). No absolute prime-error envelope is required. Integration of
the upper inequality uses the absolute zero-integrability in (VI3)
and the displayed Gamma allowance; it does not assume separate
infinite-time pole integrability or a value at the initial heat time.

### Pay the damped head and the complete coefficient error together

For the verified critical head, the absolute damped rational sum is
at most $c_0$. Indeed $\Re(1/d_\rho)>0$ for every actual zero,
so the verified subset's positive reciprocal sum is at most the full
identity (VI1). For every unverified occurrence,
$|d_\rho|\ge\gamma^2$, $\Re d_\rho\ge\gamma^2$ and
$A^{\beta-1/2}\le\sqrt A$. Consequently

$$
\left|\sum_\rho m_\rho
 \frac{A^{\rho-1/2}e^{-Ud_\rho}}{d_\rho}\right|
\le c_0+2\sqrt A\,S_2(H)e^{-UH^2}
<0.05+0.0148=0.0648.
\tag{VI5}
$$

Here $UH^2=63/2$, $\sqrt A\le2\cdot10^{23}$ and
$e^{63/2}>4\cdot10^{13}$. One exact elementary certificate for the
exponential is

$$
e>163/60,\qquad e^{1/2}>79/48,\qquad
163^{31}\cdot79>
4\cdot10^{13}\cdot60^{31}\cdot48.
$$

The first two inequalities follow from positive Taylor partial sums.
This retains both signs and all infinite heights; it does not assign
criticality to the unverified tail.

On the same interval $L>100$, since $e<11/4$ and
$11^{100}<4^{100}10^{44}<4^{100}A$.
On the verified head $|1-\rho|\ge1/2$, and on the complete high tail
$|1-\rho|\ge|\gamma|>H$. Applying (VI2) separately on these two
ranges gives

$$
|R_A|\le\frac{4(L+2)}{L^2}
 \left[c_0+\frac{\sqrt A\,S_2(H)}H\right]
<0.0408\left[0.05+\frac{2(1.48)}{30}\right]
<0.0061.
\tag{VI6}
$$

No remainder below $H$ or above $H$ is omitted, and no correction from
(RC1) is added to this alternative use of the full (H1) bound.

### Return to the original signed integral and strict core

Keep the exact original identity
$-\sqrt A L I_\psi(A)=\sqrt A L Z_{\rm orig}(A)+r_A$,
where $0<r_A\le\log(2\pi)/\sqrt A<3/\sqrt A$.
The same chosen time satisfies $\sqrt A\,U\le0.7$.
With $1+1/L<1.01$, (VI2)–(VI6) therefore pay the complete response:

$$
\boxed{
-\sqrt A L I_\psi(A)
<(1.01)(0.0648+0.7+0.000006)
 +0.0061+10^{-20}<0.779.
}
\tag{VI7}
$$

The $10^{-20}$ allowance covers both the positive $r_A$ and the pole
term $(1+1/L)U/\sqrt A$ on this actual interval. The other polar, prime,
trivial and Gamma contributions have already been preserved in the
exact source formula and its directed upper bound (VI4).

The existing increasing function $\mathcal E(L)$ from (G7) obeys
$\mathcal E(L)>0.789$ for $L>100$. For example, its value at $100$
is bounded below using $\sqrt2>1.414$, $\sqrt2<1.415$,
$\log2<0.7$, $e^{100/6}>2^{16}$ and $e^{50}>2^{50}>10^{15}$;
the negative exponential terms are respectively below $0.00005$ and
$0.000001$. Dropping the positive $6.78/L^2$ term still leaves
$2.828-0.038205-2.00014-0.00005-0.000001>0.789$.
The strict core (G6) and $\Delta(N)=I_\psi(A)+D^*(A)$ now give

$$
\boxed{
\sqrt A L\Delta(N)>0.01,
\qquad \frac72\,10^{46}<A\le4\cdot10^{46}.
}
\tag{VI8}
$$

Together with the existing (GL4) and its preceding intervals, this
forces $\log N>4\cdot10^{46}$ for the same hypothetical least global
maximizer. It is a finite selected-source exclusion with a signed
normalized margin. It is not a least-counterexample bound or
all-integer finite Robin verification. The verified height, classical
core and exact explicit-formula premises remain external inputs.

The fixed time has costs growing with $\sqrt A$ beyond this finite
window. The original unbounded signed Robin estimate and RH remain
unproved. This payment neither supplies that uniform estimate nor
certifies eligibility for the separate eventual smaller negative-time
cut. No Lean or new numerical experiment is supplied.
