---
slug: oeis-a380680-hanna-bilateral-mod-four
bibkey: hanna2025a380680
doi: null
url: https://oeis.org/A380680
triage: theorem
motivation_gids:
  - D5/S0/Certificates/OeisA380680BilateralModFourRefutation
---

# Hanna's square-residue conjecture for OEIS A380680

## Problem

Paul D. Hanna's [OEIS A380680](https://oeis.org/A380680) states:

> G.f. A(x) = Sum_{n=-oo..+oo} x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n.

> Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is nonsquare.

Formula (2) is:

> A(x) = 1 + 2*Sum_{n>=1} x^(n^2) * (2 - x^n)^n/(1 - 2*x^n)^n.

The source's comment says each summand is invariant under sign reversal of
its integer index. The zero summand is one. The citation is
[the Library note](../Library/RecurrenceComposition/hanna2025a380680.md).
Preregistration [#18667](https://github.com/the-omega-institute/trureturing/issues/18667)
classifies this explicitly published conjecture as tier 1.

### Statement echo

All Lean names below are in `D5.S0.Certificates.OeisA380680BilateralModFourRefutation`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Bilateral generating function and formula (2) | `a` takes the rational power-series coefficient of the unilateral expression | The source's equal opposite summands and zero term supply the folding convention. |
| Coefficient at degree $m$ | Finite sum over $1\le n\le m$ in `a m` | The factor $X^{n^2}$ makes larger indices irrelevant to that coefficient. |
| Positive index | `claim` quantifies natural $n$ with $0<n$ | Degree zero is excluded. |
| Congruence of an integer coefficient | Integer $z$ with $(z:\mathbb Q)=a(n)$ | This makes the source's integer congruence explicit; it adds a conclusion, not a hypothesis. |
| Residue two iff square | `z % 4 = 2` iff `IsSquare n` | Both directions use the same integer coefficient. |
| Divisibility at nonsquares | Non-square $n$ implies $4\mid z$ | The second source clause is retained. |
| Refutation | `result` negates all of `claim` | The positive square index one suffices. |

No source clause is dropped. The two public definitions retain the literal
binding expressions from #18667; there is no additional source hypothesis.

## Motivation

The conjecture would locate exactly the positive coefficients with residue
two modulo four. The series with the literal numeral two differs from the
implicit generating equation in OEIS A380060.

## Gap

The source and literature screen in #18667 read A380680 and A380060 and
searched the Epoch OEIS Open benchmark, AlphaProof nexus results, the
formal-conjectures catalogue, S. Fried's OEIS-proof papers and repository
screening material. No prior public refutation was found in that searched
scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

At degree one, the finite sum contains only index one. Its contribution is
$2[X^1]\bigl(X(2-X)(1-2X)^{-1}\bigr)=4$.
Specializing the conjecture at $n=1$ forces the integer coefficient to be
four and its remainder modulo four to be two, a contradiction.

The settling declaration is
`D5/S0/Certificates/OeisA380680BilateralModFourRefutation.result`.
Its proof shape is `bind-only`: singleton-sum, coefficient, inverse, cast
and numeral normalization from pinned Mathlib. Its admission basis is
`open-problem-resolution (#18667; Refuted)`, rather than an escape witness.
No D5 module is imported and there is no anchor atom or coverage operation.

## Falsifier

The proposed counterexample would fail if the literal source series had
$a(1)\ne4$, or if the displayed claim did not require residue two at the
positive square one. The compiled proof checks both the coefficient
normalization and the contradiction against the full claim.

## Evidence

The kernel-checked declaration `result` proves the source conjecture false.
The coefficient equality is a local proof step, not a separate public theorem.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

### Experiment

The [published numerical check](https://github.com/the-omega-institute/trureturing-experiments/tree/fc740d1a2eae7d7933dffcb9dd2422da9a8b26d1/docs/reports/oeis-a380680-bilateral-mod-four)
is pinned to commit `fc740d1a2eae7d7933dffcb9dd2422da9a8b26d1`.
Command: `python3 check.py 120` from that directory; exit 0.
The script's SHA-256 is
`7d74ba30a7cabefcd46097cea5074ceec649e43ed7b1d2714c12435b878c2d2f`.
The implementation seat reran exactly those script bytes. The check matches
the published initial data, computes $a(1)=4$ and $a(2)=6$, and verifies the
corrected residue pattern for every integer $1\le m\le120$. It does not
certify an unbounded extension.

## Triage

### What the settlement shows

| Item | Status and evidence | Boundary |
| --- | --- | --- |
| Published square-residue equivalence | Proved false in Lean by `result`, using $n=1$ | This is the single settlement. |
| Failure mechanism | Source-checked informal analysis in #18667: reducing the numerator modulo two contributes $X^{n^2}$, so its outer factor shifts support to $X^{2n^2}$ | Mathematical explanation below; no additional Lean theorem is asserted. |
| Corrected statement for $1\le m\le120$ | Computed by the pinned experiment: $a(m)\equiv2\pmod4$ exactly at $m=2k^2$ with $k>0$, and $a(m)\equiv0\pmod4$ otherwise | The uniform Lean theorem for all positive $m$ is open here and is a separate candidate. |
| Second coefficient | Computed $a(2)=6$ by the pinned experiment | Not a Lean-certified standalone value in this module. |
| A380060 | Separate existing repository theorem `D5/S1/Recurrence/Invariants/HannaBilateralThetaModFour.result` | States the different implicit-series claim; not on this module's dependency path, imported, rebuilt or changed. |
| Downstream source dependencies | No source claim relying on the conjecture was established in the source screen recorded by #18667 | This is a literature-reading boundary, not a universal absence theorem. |

The informal mechanism writes $A=1+2C$. Each denominator has constant
coefficient one, so its inverse has integral coefficients. Modulo two the
numerator $(2-X^n)^n$ reduces to $X^{n^2}$ and the inverse denominator
reduces to one. Thus the source argument gives
$C\equiv\sum_{n\ge1}X^{2n^2}\pmod2$ coefficientwise. The positive square
map is injective, so each represented exponent occurs once. This explains
the twice-square pattern tested by the experiment; this delivery's Lean
claim remains only the refutation of the original square pattern.

The literal two in A380680 has zero constant residue modulo two. The
constant-one solution in A380060 has a different residue and a different
equation. The A380680 refutation changes no A380060 theorem. No additional
downstream source conclusion is claimed to be invalidated.

## ASSUMED-UNVERIFIED

- Completeness of the literature search and absence of an earlier public refutation.
- The unbounded corrected congruence has no Lean formalization in this delivery.
- The source's bilateral-to-unilateral identity is used as its explicit formula (2), rather than as a separately formalized Laurent-series theorem.
