---
slug: tebni355257-logcoef
bibkey: luschnytebni2022a355257
doi: null
url: https://oeis.org/A355257
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/TebniA355257Divisibility.result
---

# Tebni's logarithmic coefficient divisibility conjecture

## Problem

> Conjecture: Let n >= 0, k >= 1 and k != 4. Then k divides A(n, k) if and only if k is not prime.

The settling declaration is `D5/S3/Arith/Congruence/TebniA355257Divisibility.result`, proving its literal `claim`.

### Statement echo

The claim quantifies every natural $n,k$, assumes $1\le k$ and $k\ne4$, and produces an integer $z$ equal to the rational $A(n,k)$ with $(k\mid z)\leftrightarrow\neg\operatorname{Prime}(k)$. Both directions and the zero row are retained.

The source NAME gives $A(n,k)=k![x^k]\log((1-x)/(1-2x))/(1-x)^n$. The public definitions `L` and `A` use that formal rational power-series expression. The COMMENTS quantifiers apply the same expression to all natural rows and columns required by the conjectures. The definitions `T` and `Z` are the integer summand and finite sum derived in Route, rather than additional source conventions.

## Motivation

The source is OEIS A355257, revision 37, NAME and COMMENTS, attributed to Peter Luschny and Mélika Tebni. Its Library acknowledgement is `Library/RecurrenceComposition/luschnytebni2022a355257.md`. The source has no DOI. The indices are natural numbers and include zero; rational coefficients are represented by equal integers before integer divisibility is asserted.

## Gap

Preregistrations #18639 and #18640 give the source statements and a bounded literature screen. Fried's arXiv:2607.24832 addresses the $n=3$ prime-residue case A355372. The screen also read arXiv:2410.07237 and arXiv:2606.09913, the relevant OEIS entries, Epoch OEIS Open, AlphaProof Nexus and formal-conjectures results. No complete proof of these two assertions was found in that searched scope. Literature completeness is `ASSUMED-UNVERIFIED`; this is not a priority claim.

## Route

The logarithmic coefficient is $(2^j-1)/j$. Convolution with the integral inverse power of $1-X$ gives the representing integer $Z(n,k)=\sum_{j=0}^{k}T(n,k,j)$. For positive $k$, every term below $j=k$ is divisible by $k$, leaving $(k-1)!(2^k-1)$ modulo $k$. Wilson's theorem and the finite-field power identity give residue $-1$ at prime columns. For composite $k\ne4$, factorial divisibility gives residue zero, and $k=1$ is included.

For $p\ge2$, reduction modulo $p-1$ leaves $p(p-2)!(2^{p-1}-1)n$. When $p$ is prime and $n$ is even this vanishes: composite factorial divisibility handles $p\ge7$, the even factor $n$ handles $p=3,5$, and $p=2$ has modulus one. Writing $Z(n,p)=(p-1)q$ and using its residue $-1$ modulo $p$ gives $q\equiv1\pmod p$.

## Falsifier

The divisibility assertion would fail at natural $n$ and positive $k\ne4$ with a different prime/nonprime classification. The quotient assertion would fail at even natural $n$ and prime $p$ with a nonintegral quotient or a residue different from one. Finite agreement alone establishes neither universal assertion.

## Evidence

The kernel statements are in `D5/S3/Arith/Congruence/TebniA355257Divisibility.lean` and `D5/S3/Arith/Congruence/TebniA355257Quotient.lean`, with their corresponding Blueprint Scribes. Their public theorem targets are `A_eq_Z`, `prime_residue`, `even_pred_divides` and `result` in the divisibility module and `result` in the quotient module. Their axiom closures are contained in `{propext, Classical.choice, Quot.sound}`.

The corroborating [experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/43e699d21346a1c6156fbac2901ce602af85ccd9/docs/reports/oeis-a355257-a355407-a355414-log-egf-congruences) is pinned to commit `43e699d21346a1c6156fbac2901ce602af85ccd9`. Command: `python3 check.py 30 200` from that directory; exit 0. Script `check.py` SHA-256: `3b4ea949d0ef742d98627cd45c7a436d1721f7ad03eb1351f9455f0d9c0937c2`. The series comparison covers $0\le n\le6$, $0\le k\le12$; the data comparisons cover the published prefixes of A355257, A355407 and A355414. Prime residues cover $0\le n\le30$, primes $p\le200$; the divisibility equivalence covers $0\le n<16$, $1\le k\le200$, $k\ne4$; quotient congruences cover even $0\le n\le30$, primes $p\le200$; the predecessor reduction covers $0\le n\le30$, primes $2<p\le200$. All checks pass. At $k=4$, the eight residues for $0\le n\le7$ are all two.

## Triage

The two settling modules have admission bases `open-problem-resolution (#18639; Proved)` and `open-problem-resolution (#18640; Proved)`, generality `I` and utility `none`. Their theorem proof shapes are `bind-only`. Every auxiliary theorem has a mathematical consumer. Four-slot escape registration is unfinished for all five public theorem targets, tracked together in [issue #25143](https://github.com/the-omega-institute/trureturing/issues/25143); no `declared_validated` registration is asserted.

### What the settlement shows

- **Integrality — proved, kernel-checked:** `TebniA355257Divisibility.A_eq_Z` gives an equal integer for every $n,k$, including $n=0$ and $k=0$.
- **Prime residues — proved, kernel-checked:** `TebniA355257Divisibility.prime_residue`, together with `A_eq_Z`, gives residue $-1$ for every natural row and every prime column.
- **Divisibility classification — proved, kernel-checked:** `TebniA355257Divisibility.result` proves divisibility independent of $n$ for every positive $k\ne4$, equivalent to nonprimality.
- **Prime quotients — proved, kernel-checked:** `TebniA355257Quotient.result` proves integrality and residue one for every even $n$ and prime $p$. The private `TebniA355257Divisibility.pred_reduction` proves the predecessor reduction for every $n$ and every $p\ge2$.
- **Excluded column — computed:** the pinned experiment in Evidence gives $A(n,4)\bmod4=2$ for precisely $n=0,\ldots,7$. **Uniform exclusion — proved in prose:** the reduction in Route gives $3!(2^4-1)=90\equiv2\pmod4$ independently of $n$, so $k=4$ is a genuine exception for every row. The uniform statement is an arithmetic consequence explained here, rather than a separately exported Lean theorem.
- **A355259 — open:** the separate polynomial-column conjecture is outside these results.

### Sharpness and neighbouring consequences

**Proved in prose:** for primes $p\ge7$, $p-1\ge6$ is composite and differs from four, so $(p-1)\mid(p-2)!$. The predecessor reduction therefore gives divisibility by $p-1$ for every $n$, and the same quotient argument gives residue one without a parity hypothesis. At $p=3$, the predecessor remainder is $9n\equiv n\pmod2$; at $p=5$ it is $450n\equiv2n\pmod4$. Thus evenness is necessary at these two primes, while $p=2$ has no parity restriction. These sharpenings are prose consequences of the displayed reduction, not additional public Lean statements.

The two COMMENTS conjectures are settled and the all-row prime-residue statement includes the $n=3$ case. No other source assertion is claimed settled; the A355259 problem remains open.

## ASSUMED-UNVERIFIED

Completeness of the literature screen is `ASSUMED-UNVERIFIED`. The finite experiment corroborates only the ranges stated in Evidence. Four-slot escape registration remains unfinished under #25143. No worldwide absence, priority or model-diversity claim is made.
