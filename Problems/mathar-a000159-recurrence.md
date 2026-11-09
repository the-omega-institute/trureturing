---
slug: mathar-a000159-recurrence
bibkey: mathar2015a000159
doi: null
url: https://oeis.org/A000159
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/MatharA000159Recurrence
---

# Mathar's six-step recurrence for three-hit ménage numbers

## Problem

R. J. Mathar's unnumbered first FORMULA conjecture in OEIS A000159 is the
six-step recurrence quoted verbatim in
`Library/RecurrenceComposition/mathar2015a000159.md`. The source is
OEIS-only, with no DOI or arXiv identifier. Preregistration: #24301.

For $n>0$, define

$$
U_n(t)=\sum_{k=0}^{n}\frac{2n}{2n-k}\binom{2n-k}{k}(n-k)!(t-1)^k,
\qquad U_0(t)=1,\qquad a(n)=[t^3]U_n(t).
$$

The A058087 triangle lists coefficients in descending order, so this is
A058087$(n,n-3)$ for $n\ge3$, exactly A000159. The conjecture asserts
$\sum_{j=0}^6 c_j(n)a(n-j)=0$ for every integer $n\ge9$, where

$$
\begin{aligned}
c_0(n)&=2(-252307n+1041077),\\
c_1(n)&=504614n^2-3362985n+5118150,\\
c_2(n)&=1280831n^2-7397886n+6461565,\\
c_3(n)&=746598n^2-2913543n-1336090,\\
c_4(n)&=-405481n^2+6175011n-15469320,\\
c_5(n)&=-375862n^2+4098537n-8846430,\\
c_6(n)&=2(-187931n+560630).
\end{aligned}
$$

### Statement echo

| Source clause | Formal counterpart and boundary |
| --- | --- |
| A058087's displayed finite rook sum | `U`, over rational polynomials, with the literal summand and summation range |
| Maple's explicit zero row | `U 0 = 1` is the zero branch of the definition |
| Descending coefficient order; A000159$(n)=$A058087$(n,n-3)$ | `a n` is the coefficient of degree three of `U n` |
| Mathar's seven terms and equality to zero | `claim` contains exactly these coefficients and shifts |
| Sequence offset three, with six backward shifts | The binder is a natural number with $9\le n$; every shifted argument is at least three |
| Universal conjecture | `result : claim`, with no additional hypothesis |

Rational division preserves the displayed source expression. In every
positive-row summand $k\le n$, hence $2n-k\ge n>0$. Natural subtraction
therefore agrees with integer subtraction both in the sum and in the
recurrence. The definitions totalize $a$ below the source offset; the
settled statement only uses source-domain values.

## Motivation

This is the tier-1 external named OEIS conjecture preregistered in #24301.
The public settling declaration is
`D5.S1.Recurrence.Invariants.MatharA000159Recurrence.result`.
Its admission basis is `open-problem-resolution (#24301; Proved)`.
The module has generality `G` and utility `none`: it proves a recurrence
for every source-domain index and contains no finite numerical certificate
as a D5 theorem. The proof steps are classified `bind-only`; the admission
basis is the named problem settlement.

## Gap

The source and literature screen in #24301 identifies no prior proof or
refutation of this exact degree-three operator within the inspected scope.
The classical rook polynomial and general holonomic methods are existing
mathematics. No new general method or exhaustive priority claim is made.
Literature completeness is `ASSUMED-UNVERIFIED`.

The inspected material includes the OEIS entries, Kaplansky–Riordan's
original scan, Wyman–Moser and Li, together with the identifier and
coefficient searches recorded in #24301. The complete texts of Riordan
1952, Carlitz 1952/1954, Stevens 1981, Gu–Zhao 2021, Bogart–Doyle 1986,
Alayont–Krzywicki 2007, and the restricted Riordan book pages are outside
the verified full-text scope. API limits also leave the citation graph
incomplete.

## Route

Work in formal power series over $\mathbb Q$. Let
$F(z)=\sum_{k\ge0}k!z^k$, $Z=X/(1+X)^2$, $B=F(Z)$ and
$A=\sum_{n\ge0}a(n)X^n$. Coefficient comparison gives

$$
X^2F'+(X-1)F=-1.
$$

The rook decomposition and the degree-three binomial transfer identify
$A$ with a finite combination of Euler derivatives of $F$ evaluated at
$Z$. Eliminating those derivatives gives the cleared identity

$$
3(1+X)^2A=r(X)B+s(X),
$$

where

$$
r(X)=-2(2X^5-3X^4-5X^3-4X^2-3X-2),\qquad
s(X)=2(2X^5-X^4-8X^3-7X^2-5X-2).
$$

The chain rule gives
$X^2(1+X)B'=(1-X^3)B+(X^2-1)(1+X)$.
The private `differential_certificate` combines these two identities into
a second-order differential equation for $A$, with forcing
$1136624X^3-10348X^4+1516100X^5$. Its coefficient at $n\ge9$ is exactly
Mathar's recurrence; `result` applies the coefficient extraction.
This explanation describes the internal proof, not an additional public
identity theorem. There is no convergence assumption and no inversion of
$X$ in the power-series ring; $1+X$ has unit constant coefficient.

The directly consumed repository owner is
`D5.S1.Recurrence.Residue.CompositionalSquareDyadicDenominators.coeff_subst_sum`.
The private `prefactor_subst_coeff` uses it to expand substitution
coefficients; the model coefficient calculation and the settling proof
consume that expansion. No owner is published or re-pinned.

## Falsifier

A source-domain integer $n\ge9$ with nonzero recurrence residual, using the
literal rook-polynomial coefficients, contradicts `claim`. A finite
prefix check alone cannot establish the universal assertion. Indices
$6,7,8$ use the auxiliary zero extension and are outside the theorem's
stated range.

## Evidence

Kernel evidence is the Lean declaration `result` in
`D5/S1/Recurrence/Invariants/MatharA000159Recurrence.lean`, with the Scribe
at the corresponding Blueprint address. Its axiom closure is contained
in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.

The supplemental experiment is
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/2f393349e7d0fa9cc98ab6ea2983df24853f4665/docs/reports/mathar-a000159-six-step-recurrence).
The checked script is `check.py` at that revision. Its SHA-256 is
`02f9a88ec3b2a05936384ca27c16cddf1161cd20677bc761448a7965ccf87e25`.
The exact pinned blob was executed as
`python3 /Users/auric/.sshx/b8ba824c818e7ff9dbd6e974/attempt-1/check.py`,
exit 0, final result `ALL_CHECKS_OK`.

The computation reconstructs $U_0,\ldots,U_5$ coefficientwise and obtains
$a(3),\ldots,a(8)=2,8,20,152,994,7888$. It checks all 292 recurrence indices
$9\le n\le300$ and the zero-extension indices $6,7,8$ exactly. The
independent pullback construction agrees through degree 100; rook
reindexing and theta-weight checks range through 40. The factorial-series,
reduction, chain-rule, differential-certificate and operator identities
are also checked by exact symbolic algebra. These are computations,
not substitutes for the universal kernel proof.

Escape-audit evidence is tracked in
[#24479](https://github.com/the-omega-institute/trureturing/issues/24479).
The typed Reg mirror is
`Reg/D5/S1/Recurrence/Invariants/MatharA000159Recurrence.lean`.
The scoped decoder yields `declared_unresolved` with
`IE-C050 ClosedTruthReadout` at `source.roles` (`unclassified_form`).
The audit is unfinished. Completion requires accepted source-role
reconstruction and the required `current` CI DTR reading; no four-slot
validation is asserted here.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| Mathar six-step recurrence for the exact rook-polynomial coefficient at every $n\ge9$ | proved | Kernel-checked `D5.S1.Recurrence.Invariants.MatharA000159Recurrence.result` |
| Zero-extension indices $n=6,7,8$ pass; the final recurrence theorem is stated only for $n\ge9$ | computed | The pinned `check.py`, exact command, exit 0 and SHA-256 given in Evidence |
| Other fixed-hit diagonals | open | The Euler-derivative reduction is a route; no theorem for these diagonals is delivered |
| van Hoeij's rounded Bessel expression | open | The recurrence premise is discharged by `result`; a separate formula and rounding proof is absent |
| Separate prime-shift divisibility conjecture | open | No divisibility theorem is supplied |

### What the settlement shows

The proved information is the universal recurrence, not just agreement of
initial values. The decisive mechanism is the rational affine pullback
of the factorial series: fixed degree three leads to finitely many Euler
derivatives, then to a cleared differential certificate. This account of
the mechanism is mathematical explanation of the internal proof.

The source-domain lower bound nine ensures all six shifts are defined in
A000159. The computation at six through eight establishes only those
three zero-extension cases; no uniform extension below nine is claimed
as a delivered Lean theorem. Other fixed-hit diagonals remain open.

The result removes the recurrence assumption in van Hoeij's conditional
Bessel comment. It supplies neither that comment's formula and rounding
argument nor the separate prime-shift divisibility claim. Those are
independent open boundaries of this delivery.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are
`ASSUMED-UNVERIFIED` within the limits stated in Gap and #24301.
Source attribution, descending-row identification and correspondence
with OEIS are source-fidelity claims, not facts about the external world
proved by the Lean kernel. Finite experimental scopes do not establish
unbounded extensions. Escape-registration completion requires the
required CI reading linked through #24479.
