---
slug: allouche-shallit-2021-sixfold-evil-odious
bibkey: allouche2021evilodious
doi: 10.7169/facm/2108
url: https://arxiv.org/abs/2112.13627v3
triage: theorem
motivation_gids:
  - D5/S1/Words/EvilOdious/SixfoldMonotonicity.result
---

# Sixfold evil and odious representation counts

## Problem

Allouche and Shallit, *Additive properties of the evil and odious numbers and similar sequences*, arXiv:2112.13627v3, Section 4, Conjecture 12; Funct. Approx. Comment. Math. 70(1) (2024), 55–69, DOI 10.7169/facm/2108:

> (a) Both $r_6(n)$ and $s_6(n)$ are eventually strictly increasing.
>
> (a) $r_6(n)<r_6(n+1)$ for $n\ge37$.
>
> (b) $s_6(n)<s_6(n+1)$ for $n\ge5$.

The duplicated label (a) is the source's. Equations (2)–(3) count ordered tuples with repetitions allowed. Coordinates range over $\mathbb N=\{0,1,2,\ldots\}$. The Thue–Morse recursion is $t_0=0$, $t_{2n}=t_n$, $t_{2n+1}=1-t_n$; evil and odious coordinates have letters zero and one respectively.

## Motivation

The published sixfold question concerns every index above the stated thresholds. The frozen Thue–Morse word supplies the actual sequence; the kernel-checked first-difference identities connect the tuple counts to dyadic coefficient states. The exact question and conventions are recorded in [#15023](https://github.com/the-omega-institute/trureturing/issues/15023).

## Gap

A finite list of increasing counts does not establish eventual increase. The signed coefficients require uniform bounds at every dyadic scale, combined with the same prefix and the same coefficient recurrences. The identities `r_difference` and `s_difference` require $1\le n$; their zero-extended coefficient states use integer indices. The auxiliary `state` uses truncated natural subtraction, while `stateZ` is the zero-extended source-vector interface.

## Route

Let $U=(1-z)^{-1}$ and $T=\sum_{n\ge0}(-1)^{t_n}z^n$. The signed binomial expansion of $((U\pm T)/2)^6$ gives

$$64\bigl(r_6(n)-r_6(n-1)\bigr)=\binom{n+4}{4}+\operatorname{errorTerm}(1,n),$$

$$64\bigl(s_6(n)-s_6(n-1)\bigr)=\binom{n+4}{4}+\operatorname{errorTerm}(-1,n)$$

for $1\le n$. `SequenceCoefficients.recur_eq_coeff` connects the recurrence to power-series coefficients. The two dyadic-state modules prove the six state steps. `MatrixBounds.c_word_bound` controls matrix products; `CoefficientTableChecker.tableCheck_sound` validates the coefficient tables. `DyadicPrefixBounds.state_dyadic_bound` propagates the state estimates, and its prefix certificates ensure $p^4>24B_p$ for $2048\le p\le4095$. `SixfoldMonotonicity.tail_positive` proves domination for every $n\ge2048$. Kernel-checked initial-range chunks supply the indices below that bound, and `result : claim` includes both eventual and both fixed-threshold clauses.

## Falsifier

An index $n\ge37$ with $r_6(n)\ge r_6(n+1)$, or $n\ge5$ with $s_6(n)\ge s_6(n+1)$, falsifies the corresponding fixed-threshold clause. An incorrect count convention, first-difference identity, zero-extension bridge or finite certificate invalidates this route.

## Evidence

The seven Lean modules and their Blueprint mirrors are under `D5/S1/Words/EvilOdious/` and `Blueprint/D5/S1/Words/EvilOdious/`. The settling declaration is `D5/S1/Words/EvilOdious/SixfoldMonotonicity.result`. Its conclusion is the exact preregistered `claim`, with no theorem hypotheses. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}; finite certificates use kernel reduction and no `native_decide`.

Experiment: [sixfold monotonicity checks](https://github.com/the-omega-institute/trureturing-experiments/tree/5782fa2e5763bc6e2fb9be7674e0135c234c5c89/docs/reports/allouche-shallit-2021-sixfold-evil-odious-monotonicity). Entry: `check.py`; command `python3 check.py` from that directory; exit 0; final reading `ALL_OK`; SHA-256 `a49a4321de233171bcd7500c2a6505af9defaec4f878f0ef8c560452cb9b4f66`. The executed bytes equal the file at that full commit. The independent computations cover direct counts for $n<8192$, first-difference identities for $1\le n<8192$, recurrence coefficients for $n<600$, and prefix lengths 8–13. A separate evaluation of the pinned entry's `cert` function for prefix lengths 1–7 exits 0 and gives the additional numerical readings below.

Escape audit is unfinished: [#15228](https://github.com/the-omega-institute/trureturing/issues/15228). The public settling result is a proof, so it is an audit target. No successful four-slot registration is claimed.

## Triage

- **Mechanism — proved.** `MatrixBounds.c_word_bound` proves the word bound $2\cdot16^m$; `DyadicPrefixBounds.state_dyadic_bound`, `h_dyadic`, `c_dyadic` and `prefixcertificate_checked` supply the common-prefix estimates and the twelve-bit certificate. `SixfoldMonotonicity.tail_positive` proves that $\binom{n+4}{4}/64$ dominates the signed Thue–Morse error at every larger scale; `result` combines this with the finite initial range.
- **Sharpness — computed.** The pinned experiment, `python3 check.py`, exit 0, gives $r_6(36)=12152>11976=r_6(37)$ and $s_6(4)=s_6(5)=0$. Thus neither threshold can be lowered. These equalities are numerical readings, not separate Lean theorems.
- **Prefix length — computed.** The same check gives minima of $p^4-24B_p$ equal to $-1344904727$, $-13132136135$, $-93085057559$, $-211507860935$ for lengths 8–11, and $4300720697905$ at $p=2173$ for length 12. The length-13 minimum is $100857757740265$. The additional evaluation for lengths 1–7 gives $-3647$, $-10383$, $-57311$, $-219663$, $-2093327$, $-14187680$, $-138227303$. Twelve bits is the shortest successful prefix length for this certificate. Both computations use the entry and SHA-256 in Evidence and exit 0.
- **Seven, eight and nine summands — open.** The source calls their status “currently unknown”. No conclusion for these cases is supplied by the sixfold theorem, and whether the same dyadic-norm method settles them remains open.

### What the settlement shows

**Proved:** the first differences have a positive polynomial main term and a uniformly controlled signed recurrence error. A common twelve-bit prefix and the matrix product bounds make the estimate uniform over every larger index; the initial range reaches exactly the source's thresholds. This proves all three clauses of Conjecture 12, including both eventualities, in `result`.

**Computed:** the two threshold failures immediately below the claimed ranges establish sharpness. The shorter-prefix failures distinguish a limit of this certificate from a failure of the conjecture.

**Open:** extension of the dyadic method to seven, eight or nine summands, and a different certificate with a shorter prefix. The sixfold result supplies Conjecture 12; it changes no hypothesis or conclusion of the source's proved fivefold and tenfold results, and does not settle its separate remaining summand questions.

## ASSUMED-UNVERIFIED

The preregistration's literature search found no prior settlement in its stated search scope; this is a literature reading, not a kernel result or a proof that no publication exists. Four-slot escape registration remains unfinished as detailed in #15228.
