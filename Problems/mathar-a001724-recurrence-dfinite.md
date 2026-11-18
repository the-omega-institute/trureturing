---
slug: mathar-a001724-recurrence-dfinite
bibkey: mathar2026a386829
doi: null
url: https://oeis.org/A386829
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/MatharA001724.result
---

# Mathar's recurrence and D-finiteness for OEIS A001724

## Problem

[OEIS A001724, revision 43](https://raw.githubusercontent.com/oeis/oeisdata/87b54f574c5f92e16a7c0f5446596eb42715d0ff/seq/A001/A001724.seq),
**Generalized Stirling numbers, [n+9,9]_5**, contains R. J. Mathar's
formula-field conjecture:

> Conjecture D-finite with recurrence a(n) +5*(-n-6)*a(n-1) +5*(2*n^2+22*n+61)*a(n-2) -5*(n+5)*(2*n^2+20*n+51)*a(n-3) +(5*n^4+90*n^3+610*n^2+1845*n+2101)*a(n-4) -(n+4)^5*a(n-5)=0.

The sequence is Borislav Crstici's full signed first-kind Stirling sum:

$$
s(N,K)=[X^K]\prod_{i=0}^{N-1}(X-i)\in\mathbb Z,\qquad
a(n)=\sum_{k=0}^{n}(-1)^{n+k}\binom{k+4}{4}5^k s(n+4,k+4).
$$

All indices are natural, the empty product is one, and both summation endpoints
are included. Binomial coefficients are natural binomial coefficients cast
to the integers. The signed convention is part of the definition.
The recurrence assertion is

$$
\begin{aligned}
\forall n\in\mathbb N,\quad n\ge5\Longrightarrow{}&a(n)+5(-n-6)a(n-1)
+5(2n^2+22n+61)a(n-2)\\
&-5(n+5)(2n^2+20n+51)a(n-3)\\
&+(5n^4+90n^3+610n^2+1845n+2101)a(n-4)
-(n+4)^5a(n-5)=0.
\end{aligned}
$$

Subtraction in subscripts is natural subtraction; coefficients cast $n$ to
the integers before arithmetic. The source states no onset. Including every
$n\ge5$ is the explicit complete natural-index interpretation of its five lags.

The retained D-finiteness assertion concerns
$O=\sum_{n\ge0}(a(n):\mathbb Q)X^n\in\mathbb Q[[X]]$:

$$
\exists r\in\mathbb N,\ \exists p:\mathbb N\to\mathbb Q[X],\quad
(\exists j\in\mathbb N,\ j\le r\land p(j)\ne0)
\land\sum_{j=0}^{r}\operatorname{inclusion}(p(j))D^{[j]}O=0.
$$

Here inclusion is the polynomial-to-power-series map and $D$ is formal
differentiation, with $D^{[0]}$ the identity. No convergence, finite cutoff,
assumed recurrence or assumed generating-function identity is used.
The source does not specify ordinary versus exponential series. The immutable
preregistered event requires both, an explicit strengthening. The canonical
result and its resolution claim retain recurrence plus the ordinary reading;
the successful exponential/full-conjunction check is transient evidence,
without another retained theorem or resolution member. Neither the onset nor
the BOTH requirement is presented as a verbatim source assertion.

The front-matter URL matches the shared bibliography note; the distinct
A001724 source locator above identifies this problem. Source quotations and
the sequence formula are attributed to Mathar and Crstici through OEIS under
[CC BY-SA 4.0](https://oeis.org/wiki/The_OEIS_End-User_License_Agreement).

## Motivation

The recurrence constrains the full signed sum at every valid index. The
nonzero homogeneous differential operator certifies D-finiteness of the same
ordinary rational formal series, rather than a finite prefix or a different
initial-value definition.

## Gap

The official immutable export labels the assertion a conjecture. The bounded
source, supplier and library scope is qualified in
[issue #31036](https://github.com/the-omega-institute/trureturing/issues/31036)
and its [immutable preregistration](https://github.com/the-omega-institute/trureturing/issues/31036#issuecomment-6902005491).
Roberto Blanco Gómez's *Proofs and corrections of 306 conjectures in the OEIS*,
[DOI 10.5281/zenodo.23112421](https://doi.org/10.5281/zenodo.23112421),
Proposition 7.39 (English PDF p. 33), supplies the exact all-index recurrence
and an EGF operator conditional on Jovovic's logarithmic EGF formula.
The record is dated 2026-10-02; the PDF calls itself Version 6, dated
2026-10-03. The shared literature note records the distinct version labels,
operator and authentication scope. The paper explicitly assumes the EGF
formula; neither it nor the followed entry proves its coefficient equality
with the literal signed sum. Its A001724 passages supply no ordinary operator.
This is conditional prior art, not an authenticated unconditional full supplier.
The [existing source report](https://github.com/the-omega-institute/trureturing/issues/31036#issuecomment-6904309599)
and unread possible suppliers below remain material admission limits.

## Route

The original falling product is reused from `MatharA001722.falling`.
For its Taylor translate at $-5$, multiplied by $(-1)^n$, the Hasse coefficient
formula identifies coefficient four with $a(n)$. Its next factor gives
$B_{n+1}=B_n(n+9-X)$. The five-step polynomial combination specified in the
Blueprint is $-X^5B_m$; taking coefficient four kills that term and gives the
recurrence at $n=m+5$, including the boundary $m=0$.

Formal coefficient extraction transports this recurrence to the explicit
order-six homogeneous operator in `MatharA001724.op`. The boundary coefficients
are handled inside the proof. Its highest coefficient is $p(6)=-X^{10}\ne0$.
These are proof steps of the retained result, not separate claims of new
technique or of minimal differential order.

## Falsifier

A natural $n\ge5$ at which the literal signed sum violates the displayed
recurrence contradicts the first conjunct of
`D5/S3/Combinatorics/BinomialBases/MatharA001724.result`.
A nonzero coefficient of its explicit ordinary differential expression
contradicts the operator identity used in the second conjunct. Failure of a
chosen operator alone would not refute existence of every possible operator.

## Evidence

`D5/S3/Combinatorics/BinomialBases/MatharA001724.lean` defines the signed sum,
ordinary series and exact claim; `result : claim` proves both retained clauses
without external hypotheses. Its accepted axiom closure is `Classical.choice`,
`Quot.sound`, `propext`. The canonical Blueprint attaches `Proved` to the frozen
`result`. The separate exponential check supplies the stronger preregistered
conjunction as transient compiled evidence; the frozen result does not assert
that additional conjunct or the source's logarithmic EGF formula.

The original A001722 `falling` and `falling_degree` are exposed in place with
their bodies and statements preserved and their public identities canonically
repinned. The A001724 consumer uses these originals, without copied proofs or
forwarding wrappers. This is visibility migration, not new mathematical content.

## Triage

Tier 1: an external named OEIS conjecture posed in 2026. The source-core result
uses conditional `admission_basis: open-problem-resolution` under the bounded
source qualification and unchanged preregistration above. That admission
survives the authenticated Proposition 7.39 scope provisionally: its assumed
literal-sum/EGF bridge is not supplied, so it does not establish a complete
prior solution of the retained source core or the fixed BOTH event. This is
not a first-solution, worldwide-novelty, priority or KPI claim; an authenticated
full literal supplier or prior resolution overrides eligibility. All eight authored
theorem proofs are `bind-only`; none supplies an escape witness. Helper
consumption is: `shifted_coeff` and `shifted_step` feed `recurrence_forward`;
`recurrence_forward` feeds `recurrence_rational` and `result`;
`recurrence_rational`, `term_coeff` and `op_expansion` feed `annihilates`;
`annihilates` feeds `result`. The terminal `result` uses the external-problem
exception without an artificial consumer. Utility is `none`: finite initial
arithmetic is internal to an unbounded symbolic proof.

### What the settlement shows

- **Proved:** the literal inclusive signed sum satisfies the recurrence for
  every $n\ge5$ and has an ordinary rational formal series annihilated by the
  displayed nonzero operator, through `MatharA001724.result`. The translated
  falling-product coefficient identity is the decisive mechanism.
- **Proved within that result:** the explicit operator has order six and
  highest coefficient $-X^{10}$. Minimal order, convergence, asymptotics and
  parameterized versions with other weights or coefficient degrees remain
  open here; no sharpness claim or generalization is inferred.
- **Source scope:** the positive transient check also covers the exponential
  reading of D-finiteness. The separately displayed logarithmic EGF identity
  and the source's other formulas retain independent proof obligations.
  The retained proof obtains recurrence and ordinary D-finiteness directly from
  the literal signed sum; it does not prove the identity assumed in Proposition
  7.39. Separate ordinary and exponential D-finiteness statements cannot imply
  equality with Jovovic's formula. No dependency of another named conjecture
  on this assertion is established.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive absence of earlier proofs remain
unverified. The 1962 Mitrinovic original remains unread as a possible complete
supplier: no cover, page 61 or formula pages were authenticated. The 1973 entry
2282/PEF77 page-61 pointer is advisory; the transcription's authorization is
unverified and it is not an authenticated primary mathematical source. The
1995 book remains unread. The M. S. versus R. S. Mitrinovic author discrepancy
remains unresolved without the original cover. No full supplier is certified
absent; an authenticated complete supplier or prior resolution overrides the
conditional external-problem eligibility.

The source-owner four-slot registration audit is unfinished under
[issue #31052](https://github.com/the-omega-institute/trureturing/issues/31052).
Lawful source selection, complete original-telescope reconstruction, the
realization bridge, actual-positive law, whole-family variation/sensitivity,
enrolled-template application and current binding evidence remain missing,
including the newly public A001722 theorem's registration. No new Reg module,
invalid placeholder or `declared_validated` registration is claimed. Canonical
repinning and mathematical compilation do not discharge that audit.
