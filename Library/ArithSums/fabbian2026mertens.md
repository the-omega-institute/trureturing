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
