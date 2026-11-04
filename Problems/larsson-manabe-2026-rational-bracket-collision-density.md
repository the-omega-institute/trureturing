---
slug: larsson-manabe-2026-rational-bracket-collision-density
bibkey: larssonmanabe2026additive
doi: 10.48550/arXiv.2603.10414
url: https://arxiv.org/html/2603.10414v2#Thmthm20
triage: theorem
motivation_gids:
  - D5/S3/Arith/Density/RationalBracketCollisionDensity.result
---

# Rational collision density of bracket expressions

## Problem

Urban Larsson and Hikaru Manabe, *Additive Subtraction Games*, arXiv:2603.10414v2,
Section 7, Question 20(iii), define the collision density of an arbitrary bracket
expression and separately ask: “Is it always rational?” Section 1 specifies
integer coefficients and positive rational moduli.

For every finite $t$, coefficients $c_i\in\mathbb Z$ and positive
$\alpha_i\in\mathbb Q$, set
$w_n=\sum_{i=1}^t c_i\lfloor n\alpha_i\rfloor$ for $n\geq0$ and
$W=\{w_n:n\geq0\}$. For every positive integer $k$, set
$C(k)=\{x\in W:x+k\in W\}$. The result proves that

$$\lim_{N\to\infty}\frac{|C(k)\cap\{0,\ldots,N\}|}{N}$$

exists and is rational. This is the complete rationality subquestion, including
existence of the limit, rather than the other requests in Question 20.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every finite number of terms, including zero | `t : ℕ` and `Fin t` |
| Integer coefficients of either sign | `c : Fin t → ℤ` |
| Positive rational moduli | `α : Fin t → ℚ` and `∀ i, 0 < α i` |
| Natural sequence indices including zero | `bracket c α n`, `n : ℕ` |
| Actual distinct image values at $x$ and $x+k$ | `collision` has two independent existential indices; the count filters values once |
| Every positive integer shift | `k : ℕ` with `0 < k` |
| Inclusive nonnegative interval | `Finset.range (N + 1)` |
| Denominator $N$ | Real cardinality divided by `(N : ℝ)` |
| Existence and rationality of the whole limit | `∃ a : ℚ, Tendsto … atTop (𝓝 (a : ℝ))` in `claim` |

No monotonicity, injectivity, positive drift or nonnegative-coefficient premise
is imposed. The empty expression, zero coefficients and all drift signs remain
in scope.

## Motivation

The settling declaration is
`D5/S3/Arith/Density/RationalBracketCollisionDensity.result`, admitted on the
`open-problem-resolution` basis. The source definition and question are
literature-attested in `Library/ArithUnits/larssonmanabe2026additive.md`; the proof
is repository-derived. This Tier 1 target is a separately stated question in a
recent paper, with the bounded literature qualification below.

The immutable [preregistration](https://github.com/the-omega-institute/trureturing/issues/23511#issuecomment-6488081160)
has created and updated timestamps `2026-10-29T04:37:53Z`. Its exact event is the
statement in Problem above. The two probabilities are `0.995` and `0.985`, the
mathematical start is `2026-10-29T04:47:55Z`, the absolute deadline is
`2026-10-29T08:00:00Z`, and the total allowance is 7200 seconds. These remain the
original contract; retention and publication do not reset them. A typed proved
claim identifies the mathematical answer, without granting delivery or priority
credit before independent review and required checks.

## Gap

An affine recurrence in the sequence index does not directly count distinct
image values: repeated indices may give the same integer, and signed
coefficients permit nonpositive drift. The required bridge is eventual
periodicity of actual image membership on the nonnegative integers, followed by
the same property for its fixed-shift collision intersection.

## Route

`bracket_affine` clears the finitely many rational denominators to produce a
common positive index period and integer drift. `affine_image_tail` decomposes
the image into finitely many residue rays. It constructs an eventually periodic
nonnegative membership tail for positive drift and an empty tail for nonpositive
drift. `result` transports both image-membership equivalences to `collision`.
`eventual_periodic_density` applies the existing frozen
`D5.S3.ObserverMemory.Prediction.EventualCycleAverage.eventual_cycle_average` to
the indicator sequence, then adjusts the endpoint and denominator to the exact
source convention.

## Falsifier

A finite rational-modulus expression with signed integer coefficients and a
positive shift for which the displayed limit fails to exist or is irrational
would contradict the result. Substituting index multiplicity, dropping negative
drift, changing the interval or assuming density existence would fail the source
contract. Finite numerical tests alone cannot settle the universal limit.

## Evidence

`result : claim` proves the complete quantified proposition. Its declaration
statement identity is
`sha256:f58cccaf4b6a8eb457f79a538ff7c7301f7fe6a174a47ba5083f85b4932726a0`;
its type hash is
`sha256:6ee529e35e0754e5912324a67d5d265b2f0ff4e19400b950626c263b27e3c766`.
The public surface consists of `bracket`, `collision`, `claim` and `result`.
Their complete formulas have typed Scribe mirrors. Canonical freezing uses
`deposit-uncovered`: the bounded corresponding-theory search identified no
volume or atom.

| Declaration | Semantic proof shape | Actual consumer |
| --- | --- | --- |
| `affine_blocks` | bind-only | `bracket_affine`, `affine_image_tail` |
| `bracket_affine` | content: common period and drift construction | `result` |
| `affine_image_tail` | content: actual image-tail construction | `result` |
| `eventual_periodic_density` | bind-only | `result` |
| `result` | content: combines the constructed membership witnesses | The source question |

The four helpers remain private and consumed. These semantic classifications
are review judgments, not machine non-derivability certificates. No independent
resolution is attributed to a helper or definition. The module has `utility:
none`: it delivers an analytic existence theorem, not a finite enumeration,
checker, certified instance or numerical reduction.

After helper expansion the direct frozen D5 supplier is
`D5/S3/ObserverMemory/Prediction/EventualCycleAverage.eventual_cycle_average`,
with declaration statement identity
`sha256:2e3154d85f7181f0927cc78bd2487ecbbef22bbb3b139cd74a7bb868b5c281be`
and type hash
`sha256:06978998ac945255f330445b4d729bf786db752a205ad762133dc5ed35f4d0b6`.
Its frozen membership module pin is
`sha256:fbf7b006297efc737bcba761bafdee1ac321717785f68ef6dc4cf3044e424964`;
that module pin is not the declaration identity. The compiled axiom closure is
limited to `Classical.choice`, `Quot.sound` and `propext`.

The matching Reg source uses `DependentFamily.realize` with the complete original
telescope and the actual real embedding of the rational density value. It
supplies the source equivalence, law, whole-family variation and sensitivity,
and actual observational dependence. Its source-registration evidence reference
is `4b526a73b08522592777206fe9da4b63476da607171888c940667c983cffdbc8`.
The continuation is explicitly open; it claims no undecidability or absence of
further structure.

## Triage

| Item | Evidence and boundary |
| --- | --- |
| Rationality subquestion | Proved by the exact Lean `result`, including existence, signed coefficients, all drift signs and the empty family |
| Decisive mechanism | The compiled private constructions convert a rational floor sum to affine residue rays and then to an eventually periodic actual image tail |
| Collision step | The compiled result intersects the two membership equivalences at the same value and its fixed positive shift |
| Averaging step | Direct reuse of the frozen eventual-cycle average theorem with the exact endpoint and denominator normalization |
| Irrational moduli | Open here; no extension is claimed |
| Closed form and characterisation requests | Open here; no additional result or zero-density formula is delivered |
| Game-theoretic consequences and other questions | No settlement is asserted; the result supplies only the rationality answer requested in Question 20(iii) |
| Literature priority | Bounded qualification only; exhaustive absence of an earlier answer remains unverified |

### Literature qualification

The current arXiv abstract page lists v2 as latest. The v2 primary text has
462659 bytes and SHA-256
`ba317318db8f71382c62bdea468c538f9abfe84ab3c84e31340af1d363b21cd3`.
Section 1 and Question 20(iii) retain the rational-modulus definition and the
explicit rationality question. The body date August 24, 2026 and the arXiv v2
history timestamp March 29, 2026 are distinct readings.

The supplied bounded refresh inspected six MathDB first pages, source metadata,
public alphaXiv content, arXiv metadata search, eight Crossref hits and all-state
GitHub target searches. The delivery refresh inspected the current primary and
version history, the first 20 MathDB results for `"collision density" "bracket"`,
and two all-state GitHub source/target searches. No explicit matching prior
answer or competing exact owner was identified in those scopes; both GitHub
queries returned only #23511 with `incomplete_results=false`.

Woods, arXiv:1211.0020v2, Theorems 1.5 and 1.10, supplies general Presburger
definability/counting results and a concrete reuse lead. No exact-event encoding
and limit bridge was established in this source qualification, and those
statements do not explicitly answer the named question. The original
Ginsburg–Spanier text remains unread. Earlier citing-work observations were not
upgraded into a complete current citation inventory. A verified matching
published answer would exclude new-resolution credit.

## ASSUMED-UNVERIFIED

Global originality, priority and exhaustive literature absence are
`ASSUMED-UNVERIFIED`. Dynamic discussion comments, later MathDB pages, the
original Ginsburg–Spanier text and a complete current citing-work inventory were
not verified. These limits do not replace Lean verification. Draft publication
does not certify post-door independent review, required CI, merge, first dev
push, main-checkout synchronization or research resolution credit.
