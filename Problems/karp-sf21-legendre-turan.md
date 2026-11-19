---
slug: karp-sf21-legendre-turan
bibkey: karp2011sf21legendre
doi: null
url: https://math.nist.gov/~DLozier/SF21/SF21slides/Karp.pdf
triage: theorem
motivation_gids:
  - D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.result
---

# Karp's fractional-degree Legendre Turán conjecture

## Problem

Dmitry Karp, *Log-convexity and log-concavity for series in product ratios of
rising factorials and gamma functions*, SF21 slides, physical PDF page 52
(repeated on pages 53–54), states Conjecture 4:

> Turán inequality is true for all μ>0 and 0<δ<1.

The preceding display is

$$
{}_2F_1(-\mu,1+\mu;1;y)^2>
{}_2F_1(-\mu-\delta,1+\mu+\delta;1;y)
{}_2F_1(-\mu+\delta,1+\mu-\delta;1;y),
$$

with the source clause “for y∈(0,1), μ=1,2,… and δ=1.”
The conjecture extends the degree and shift ranges and retains $0<y<1$.
It includes no positivity or zero-free condition on the function values.
Preregistration: [#23075](https://github.com/the-omega-institute/trureturing/issues/23075).
The source note is [karp2011sf21legendre](../Library/Asymptotics/karp2011sf21legendre.md).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| “for y∈(0,1)” | Real parameter `y`, hypotheses `0 < y` and `y < 1` in `claim` | Same open interval |
| “all μ>0” | Real parameter `μ`, hypothesis `0 < μ` | All positive real degrees |
| “0<δ<1” | Real parameter `δ`, hypotheses `0 < δ` and `δ < 1` | Same strict shift bounds |
| The squared central value and ordered shifted product | `gauss` at the displayed upper parameters and denominator parameter one | Literal source expression; the existing Gauss owner supplies the standard real hypergeometric function |
| Strict greater-than comparison | The conclusion of `claim` | Same direction and strictness |

`claim` is a closed `Prop`; `result` has literal type `¬ claim`.
There are no additional binders or hypotheses. The module has `generality: I`.

## Motivation

The settling declaration is
`D5/S3/Analytic/GaussZeroBalanced/FractionalLegendreTuran.result`.
Its admission basis is `open-problem-resolution (#23075; Refuted)`;
its computational utility is a certified instance with `basis=refutes`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The only public mathematical declarations are `claim` and `result`.

## Gap

The integer-degree, unit-shift comparison in the source does not establish the
fully quantified fractional-shift assertion. A single admissible instance
with the reverse strict comparison suffices to refute that assertion.

## Route

Write $F_\nu(y)={}_2F_1(-\nu,1+\nu;1;y)$ and
$T_{\mu,\delta}(y)=F_\mu(y)^2-F_{\mu+\delta}(y)F_{\mu-\delta}(y)$.
Take $\mu=3/2$, $\delta=63/64$, $y=4095/4096$.
The private checker soundness proofs transport real recurrence enclosures
through the integer certificate. Each certificate has 10,000 steps at scale
$10^{12}$. The coefficient recurrence is reused from
`GaussZeroBalanced.Series.coefficient_recurrence` and the function is
`GaussZeroBalanced.Defs.gauss`.

For the hypergeometric terms $u_n$, once $n\ge\nu\ge0$,

$$
\frac{u_{n+1}}{u_n}
=y\frac{(n-\nu)(n+\nu+1)}{(n+1)^2},\qquad
0\le\frac{(n-\nu)(n+\nu+1)}{(n+1)^2}\le1.
$$

The proof uses the multiplication recurrence even when a term vanishes;
the displayed quotient explains the estimate where the quotient is defined.
The geometric tail estimate combines with the finite enclosure to prove
`minus_enclosure`, `center_enclosure` and `plus_enclosure`.
The private theorem `witness_negative` then supplies the contradiction in `result`.

## Falsifier

The proposed refutation would fail if the witness left any source interval,
if the real hypergeometric series were not connected to the certificate,
or if the certified upper bound for $T$ were nonnegative.
The settling proof checks the source inequalities and establishes strict negativity.

## Evidence

### Kernel evidence

The module proves the following enclosures privately:

$$
-\frac{23}{10}\le F_{33/64}(4095/4096)\le-\frac{227}{100},\quad
\frac{181}{100}\le F_{96/64}(4095/4096)\le\frac{184}{100},\quad
-\frac{153}{100}\le F_{159/64}(4095/4096)\le-\frac{150}{100}.
$$

They occur on the proof path to `witness_negative` and `result`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

### Exact experiment

[Published experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/33f936615612e4644068615c31c8777d6ba67ce5/docs/reports/fractional-legendre-turan).
The script is `docs/reports/fractional-legendre-turan/check.py` at commit
`33f936615612e4644068615c31c8777d6ba67ce5`; its SHA-256 is
`5a108507a05370b53449cfc57e79e8904492499ce05065f3e9136b548b80012b`.
Command: `python3 docs/reports/fractional-legendre-turan/check.py`, exit 0,
executed from the immutable Git blob in a temporary checkout of that directory
with Python 3.14.8 and SymPy 1.14.0. The script reports `ALL_CHECKS_OK`.

The computation checks 936 strict comparisons with central integer degrees
$1\le n\le12$, unit shift, and $y=a/b$ for $2\le b\le13$, $1\le a<b$.
It also encloses 18 exact terminating-series values, and checks three rational
counterexamples: $(3/2,127/128,255/256)$ through term 8192,
$(3/2,63/64,1023/1024)$ through term 32768, and
$(3/2,63/64,4095/4096)$ through term 131072.
At the last point its bound is
$-14914313/100000000\le T\le-1864289/12500000<0$.
These computations are distinct from the module's 10,000-step proof certificate.
The script's symbolic identities do not establish a uniform analytic remainder.

## Triage

### What the settlement shows

| Item | Status and evidence | Result and boundary |
| --- | --- | --- |
| mechanism | Proved, kernel-checked: private `minus_enclosure`, `center_enclosure`, `plus_enclosure`, `witness_negative` | Both shifted values are negative and the central value is positive. The shifted product exceeds the central square. No sign hypothesis occurs in the source claim. |
| extent | Proved, kernel-checked: `result`; non-strict extension proved in prose below | One strict interior rational instance refutes the full quantified strict assertion and its non-strict version. |
| all-degrees-positive | Computed: the exact experiment above, exit 0, with its stated script SHA-256 | The witness degrees are $33/64$, $96/64$ and $159/64$, all positive. |
| integer-unit-shift-neighbour | Computed: the exact experiment above, exit 0, with its stated script SHA-256 | All 936 specified grid comparisons are positive. No universal integer-degree theorem is newly asserted. |
| positive-value-or-zero-free-neighbours | Open | The witness has negative shifted values and does not decide variants imposing positivity or an appropriate zero-free range. |
| moving-shift-family | Open | No uniform continuation remainder, asymptotic family or neighbourhood-of-counterexamples theorem is established. |

For the non-strict variant, the kernel-checked enclosures give

$$
T_{3/2,63/64}(4095/4096)
\le (184/100)^2-(227/100)(150/100)=-97/5000<0.
$$

Thus the same admissible point violates $T\ge0$. This is a consequence proved
in prose from the checked enclosures, not a separately exported Lean theorem.

The closest surviving cases in this delivery are the experiment's finite
integer-degree grid and the source's integer-degree, unit-shift assertion as
a literature statement; the latter is not newly proved here.
The literature screen on #23075 identifies no inspected theorem whose proof
uses Conjecture 4 as a premise. Grabarek's dissertation uses it as motivation.
This is a literature reading with the completeness boundary below, not a
claim about uninspected literature.

## ASSUMED-UNVERIFIED

Literature completeness and priority are `ASSUMED-UNVERIFIED`.
The preregistration records a partial screen of the NIST source, Grabarek's
2012 dissertation §4.2, related gamma-ratio and Turán literature, author
inventories, arXiv searches and citation metadata.
No arXiv identifier or journal version of the SF21 deck was located.

For Baricz–Rudrappa–Singh, DOI `10.1016/j.jat.2026.106319`, the abstract,
introduction and public snippets were inspected as recorded on #23075;
Theorems 2.4–2.5 and the full text remain unread. The partial screen does
not establish that a prior settlement is absent from all literature.
Positive-value variants, a suitable zero-free formulation and a uniform
moving-shift family remain open.
