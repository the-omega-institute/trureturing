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
