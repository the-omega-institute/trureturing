---
slug: oeis-a393173-hanna-power-of-two-parity
bibkey: hanna2026a393173
doi: null
url: https://oeis.org/A393173
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity
---

# Hanna's power-of-two parity conjecture for OEIS A393173

## Problem

Paul D. Hanna's [OEIS A393173](https://oeis.org/A393173) states:

> G.f. A(x) satisfies [x^n] 1/(A(x) - n^2*x) = 0 for n >= 1.

> Conjecture: for n > 0, a(n) is odd iff n is a power of 2.

The offset-zero data specify $a(0)=1$.
[Preregistration #18824](https://github.com/the-omega-institute/trureturing/issues/18824)
classifies the published conjecture as tier 1. The source is documented in
[the Library note](../Library/RecurrenceComposition/hanna2026a393173.md).

### Statement echo

Names below belong to `D5.S1.Recurrence.Invariants.HannaA393173PowerTwoParity`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Offset zero, $a(0)=1$ | `IsGF` constant coefficient | Literal normalization. |
| $[x^n](A-n^2x)^{-1}=0$ for $n\ge1$ | `IsGF` inverse coefficient, natural index cast into $\mathbb Q$ | Literal source expression. |
| Positive indices | `claim`, $n>0$ | Zero is excluded. |
| $a(n)$ is odd iff $n=2^k$ | `claim`, integer coefficient witness and both directions of the equivalence | Exponent $k$ is natural. |
| Existence and integrality implicit in the sequence | `claim`, an existing solution and an integer witness for every coefficient of every solution | Explicit strengthened clauses from the preregistration; these prevent vacuity. |

## Motivation

`D5/S1/Recurrence/Invariants/HannaA393173PowerTwoParity.result` proves the complete
preregistered proposition. The normalized rational inverse-diagonal solution
exists, its positive coefficients are integers, and their odd support is exactly
the powers of two. Its admission basis is
`open-problem-resolution (#18824; Proved)`, generality is `I`, and utility is `none`.
The argument is symbolic at all natural degrees.

## Gap

The conjecture is a universal statement about the full formal series. A finite
prefix does not establish it. A normalized integral lift and uniqueness of the
coefficient recursion connect reduction modulo two to every rational solution.

The [escape audit #19804](https://github.com/the-omega-institute/trureturing/issues/19804)
is unfinished for the only public theorem, the full Lean name
`D5.S1.Recurrence.Invariants.HannaA393173PowerTwoParity.result`.
The enrolled existential and iff readouts do not alone supply a readout of its
whole conjunction over the infinite power-series domain. A faithful dependent
family reconstruction, observational dependence and intervention/sensitivity
proofs for this exact telescope have not been supplied. No validated registration
is claimed.

## Route

Let $S=\sum_{j\ge0}x^{2^j}$ over $\mathbb F_2$. The frozen
`CubicFifteenSubstitutionParity.thue_series_equation` supplies $S=x+S^2$.
For normalized series, changing only the coefficient of degree $d$ changes the
inverse's degree-$d$ coefficient by its negative. Thus the correction that adds
the offending inverse coefficient is a strict coefficient contraction.
The frozen `PowerSeriesNormalizedContraction.exists_unique_fixed` supplies its
integral fixed point and uniqueness. The frozen
`QuotientThetaCompositionModFour.map_inverse` transports the equation through
coefficient ring maps.

Put $P=1+S$. Since $P(S/x)=1$, its inverse is $S/x$. At positive even $n$,
$n^2=0$ modulo two and $[x^n]P^{-1}=[x^{n+1}]S=0$: the odd index $n+1\ge3$
is not a power of two. At odd $n$, $P-x=P^2$ in characteristic two, so its
inverse is a square and has zero odd-degree coefficients by
`CubicFifteenSubstitutionParity.prime_power_subst`. Hence $P$ satisfies every
reduced equation. Uniqueness identifies the reduction of the integral fixed
point with $P$. Rational uniqueness and the integer-cast parity equivalence
establish `result`.

### Declaration classification

Every authored declaration has `proof_shape: bind-only` after expanding the
same-module helpers to the frozen owners and pinned Mathlib. Each helper is
consumed; `escape_witness: none`. This classification concerns the proof steps;
the published open-problem settlement supplies the module's admission basis.

| Declaration | `proof_shape` | `escape_witness` | Direct consumers |
| --- | --- | --- | --- |
| `IsGF` | bind-only | none | `claim`, `isGF_iff_fixed`, `result` |
| `claim` | bind-only | none | `result` |
| `inverse_top` | bind-only | none | `step_contract` |
| `binary_quadratic` | bind-only | none | `binary_inverse`, `candidate_fixed` |
| `binary_parity` | bind-only | none | `result` |
| `step` | bind-only | none | `candidate_fixed`, `fixed_iff`, `fixed_map`, `fixed_unique`, `integral_mod_two`, `isGF_iff_fixed`, `normalized_solution`, `result`, `step_contract`, `step_zero` |
| `denominator_zero` | bind-only | none | `fixed_map`, `isGF_iff_fixed`, `step_contract` |
| `step_zero` | bind-only | none | `normalized_solution` |
| `step_contract` | bind-only | none | `normalized_solution` |
| `fixed_iff` | bind-only | none | `candidate_fixed`, `fixed_map`, `isGF_iff_fixed` |
| `fixed_map` | bind-only | none | `integral_mod_two`, `result` |
| `isGF_iff_fixed` | bind-only | none | `result` |
| `binary_inverse` | bind-only | none | `candidate_fixed` |
| `candidate_fixed` | bind-only | none | `integral_mod_two` |
| `normalized_solution` | bind-only | none | `fixed_unique`, `result` |
| `fixed_unique` | bind-only | none | `integral_mod_two`, `result` |
| `integral_mod_two` | bind-only | none | `result` |
| `result` | bind-only | none | External named settlement |

## Falsifier

A positive degree whose integral coefficient violates the power-of-two parity
equivalence would contradict `result`. A rational normalized series satisfying
the source equations without the stated integral coefficients would also
contradict it. The separate modulo-four claim has a different conclusion and
is outside this theorem.

## Evidence

The canonical module and its Blueprint show the full proposition. The public
surface consists of `IsGF`, `claim`, and the sole theorem `result`; all proof
helpers are private. The axiom closure of every public declaration is contained
in {propext, Classical.choice, Quot.sound}.

The numerical experiment is
[oeis-hanna-parity-family-research at 9dfe5bdc210cac281a148e7180239ddb21b0b34b](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research).
Command: `python3 check.py` in that directory; exit 0.
The `check.py` SHA-256 is
`ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`.
For A393173 the first 12 terms agree with the recorded OEIS data; coefficients
through degree 40 are integral and parity agrees for $1\le n\le40$.
The same program reports those finite checks for A382122 and A393850, and tests
an alternate A382122 sign branch. These are finite computations, independent of
the unbounded theorem.

## Triage

### What the settlement shows

- **A393173 — proved, kernel-checked:** `result` establishes existence,
  integrality and parity for every normalized rational solution. The decisive
  reduced series is $1+S$; the even case uses $S/x$ and the odd case uses
  Frobenius. **Uniqueness — proved in prose:** two normalized fixed points agree
  below degree zero; strict coefficient contraction extends agreement below
  degree $d$ to agreement below degree $d+1$. Induction gives coefficientwise
  equality. The private `isGF_iff_fixed` identifies precisely these fixed
  points with the source equation. Uniqueness is not a separate public theorem.
- **A382122 — proved in prose below:** every normalized rational solution of
  its absolute-value equation is integral and has the same positive-degree
  parity. This statement does not assume uniqueness or positivity of the
  inverse coefficients. Its separate preregistration is
  [#18822](https://github.com/the-omega-institute/trureturing/issues/18822);
  it is not a Lean settlement delivered by this module.
- **A393850 — proved in prose below:** the integral Lagrange-root recurrence
  reduces to $B=1+x$, its root $G$ to $x+x^2$, its reversion to $S$, and its
  series $A$ to $1+S$. This is a mathematical consequence of the coefficient
  recurrence and the classical Lagrange coefficient formula, not a new general
  Lagrange or derivative theorem in this module. Its separate preregistration is
  [#18823](https://github.com/the-omega-institute/trureturing/issues/18823).
- **Modulo four and neighbouring entries — open:** the source's separate
  conjecture $a(n)\equiv2\pmod4$ iff $n/2$ is a sum of two distinct powers of
  two is not settled here. A393170, whose diagonal has $n$ in place of $n^2$,
  has no settlement claim in this dossier. No conclusion about another source
  result is inferred without its own hypotheses and proof.

### A382122: absolute values and all solution branches

Write $U=A^{-1}$ and let $C=1+xC^2$ be the Catalan series. The equation is
$\sum_{m\ge0}x^m|U^m|=C$, with absolute values taken coefficientwise.
At degree $n+1$, the $m=1$ term is $|u_n|$; the $m=0$ term is zero and all
$m\ge2$ terms depend only on $u_0,\ldots,u_{n-1}$. Starting from $u_0=1$,
induction therefore shows $|u_n|$ is an integer, so $u_n$ is an integer.
The inverse of a normalized integral series is integral, hence so is $A$.
For every integer $z$, $|z|\equiv z\pmod2$, regardless of sign. Reducing the
whole equation gives $(1-x\bar U)^{-1}=\bar C$. But
$C(1-xC)=1$, so cancellation yields $\bar U=\bar C$. Consequently
$\bar A=\bar C^{-1}=1+x\bar C=1+S$: $x\bar C$ is the zero-constant solution
of $T=x+T^2$, whose coefficients are uniquely determined. Existence follows
by taking $A=C^{-1}$ over $\mathbb Q$: every coefficient of $C^m$ is
nonnegative, so the absolute-value equation is the geometric identity
$(1-xC)^{-1}=C$. This proves the assertions for every solution without
selecting a sign branch.

### A393850: the integral root recurrence

For a normalized rational $A$, let $G=xA(G)$. The classical formal Lagrange
coefficient identity
$[x^m]G^k=(k/m)[t^{m-k}]A(t)^m$ converts the source equation
$[t^n]A^{n+1}=n(n+1)[t^{n-1}]A^{n+1}$ into
$[x^m]G=\binom m2[x^m]G^2$ for $m\ge2$.
Writing $G=xB$ gives $b_0=1$ and
$b_r=\binom{r+1}{2}[x^{r-1}]B^2$ for $r\ge1$. This recurrence depends
only on lower coefficients, so it constructs a unique integral $B$.
The series $G=xB$ has linear coefficient one; its reversion $R$ is integral,
as are $R/x$ and $A=(R/x)^{-1}$. Reversing the Lagrange coefficient identity
shows this construction satisfies the source equation. The coefficient of
$x$ in $A$ is one. Every rational solution gives the same $B$ and hence the
same $A$.

Modulo two, $B=1+x$ satisfies the recurrence: its square is $1+x^2$;
$r=1$ gives one, $r=3$ gives $\binom42=6=0$, and all other positive
coefficients are zero. Coefficient uniqueness identifies the reduction of $B$
with this candidate. Thus $\bar G=x+x^2$, $\bar R=S$, and
$\bar A=x/S=1+S$. The positive-degree parity conclusion follows. This
argument is a prose consequence; this dossier makes no claim of a canonical
Lean proof of the sibling statement.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The preregistration records
reading the OEIS entry and attributes the revision-history and A393170 screen
to the research producer. The supplied screen found no published proof; a
search miss is not a completeness theorem or a claim of original discovery.
The independent bounded reuse queries include heartbeat-limited queries and
do not establish exhaustive coverage of the Lean ecosystem.
The escape audit remains unfinished under #19804.
