---
slug: mathar-a001722-recurrence-dfinite
bibkey: mathar2026a386829
doi: null
url: https://oeis.org/A386829
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/BinomialBases/MatharA001722.result
---

# Mathar's recurrence and D-finiteness for OEIS A001722

## Problem

[OEIS A001722, revision 26](https://oeis.org/A001722/internal?fmt=text),
**Generalized Stirling numbers [n+7,7]_5**, contains R. J. Mathar's
July 20, 2026 FORMULA assertion:

> Conjecture D-finite with recurrence a(n) +3*(-n-5)*a(n-1) +(3*n^2+27*n+61)*a(n-2) -(n+4)^3*a(n-3)=0.

Use the entry's full Crstici signed first-kind Stirling sum as the definition:

$$
s(N,K)=[X^K]\prod_{i=0}^{N-1}(X-i)\in\mathbb Z,\qquad
 a(n)=\sum_{k=0}^{n}(-1)^{n+k}\binom{k+2}{2}5^k s(n+2,k+2).
$$

Here $N,K,n,k$ are natural numbers, the empty product is one, and the sum
includes both endpoints. Binomial coefficients are natural binomial
coefficients cast into the integers. The signed coefficient convention is
part of the definition; unsigned Stirling numbers are not substituted.

The first clause is

$$
\forall n\in\mathbb N,\quad 3\le n\Longrightarrow
 a(n)+3(-n-5)a(n-1)+(3n^2+27n+61)a(n-2)-(n+4)^3a(n-3)=0.
$$

Subtraction in sequence indices is natural subtraction. Each coefficient
casts $n$ to the integers before arithmetic. The source gives no explicit
onset: $n\ge3$, including $n=3$, is the entire natural-index domain of the
four recurrence terms.

The second clause concerns the same ordinary rational formal series

$$
G=\sum_{n\ge0}(a(n):\mathbb Q)z^n\in\mathbb Q[[z]].
$$

There exist $r\in\mathbb N$ and $p:\mathbb N\to\mathbb Q[z]$ such that

$$
(\exists j\in\mathbb N,\ j\le r\ \land\ p(j)\ne0)
\quad\land\quad
\sum_{j=0}^{r}\operatorname{inclusion}(p(j))D^{[j]}G=0.
$$

The inclusion is the canonical polynomial-to-power-series map; $D$ is formal
differentiation and $D^{[0]}$ is the identity. There is no convergence,
exponential generating function, cutoff, zero-operator certificate,
assumed alternative representation or extra hypothesis.

The front-matter URL matches the shared Mathar bibliography note, which
covers both A386829 and A001722. The A001722 source and its distinct verified
locator are the ones specified above.

## Motivation

The two clauses control every coefficient of the sequence defined by the
signed sum. A recurrence alone would leave the requested differential
certificate unstated; the ordinary formal-series identity supplies that
certificate for the identical all-index object.

## Gap

The official source labels the joint assertion a conjecture. The bounded
source and literature qualification in
[the preregistration](https://github.com/the-omega-institute/trureturing/issues/27903)
found no exact full published settlement in its stated scope. Identifier
queries A001722, A1722, M5061 and N2191 returned zero issue/PR matches in the
recorded all-state title/body search, with limit 100 and no incomplete flag.
The inspected generalized-Stirling hits concern other claims, including the
monic-annihilator transform and Maier's boson-ordering formula. The recorded
Janjic, Plouffe and Niu readings do not provide a verified specialized bridge
or proof of this complete conjunction. These are bounded findings, without
an exhaustive worldwide openness or priority claim.

## Route

Define the translated polynomial

$$
B_n(X)=(-1)^n\prod_{i=0}^{n+1}(X-5-i).
$$

The Taylor/Hasse coefficient formula derives $[X^2]B_n=a(n)$ from the original
signed sum. The falling-product step gives

$$
B_{n+1}(X)=B_n(X)(n+7-X).
$$

Consequently

$$
B_{m+3}-3(m+8)B_{m+2}+(3m^2+45m+169)B_{m+1}-(m+7)^3B_m=-X^3B_m.
$$

Taking coefficient two eliminates the right side and gives the full
recurrence after $n=m+3$. This includes $m=0$, hence the boundary $n=3$.
The directly evaluated initial coefficients are $1,18,251$; the next is
$3325$, and the first recurrence reads $3325-24\cdot251+169\cdot18-343=0$.

For the ordinary series, take $r=4$ and

$$
\begin{aligned}
p(0)&=-18+254z-1029z^2,\\
p(1)&=1-24z+253z^2-1019z^3,\\
p(2)&=-3z^2+54z^3-289z^4,\\
p(3)&=3z^4-30z^5,\\
p(4)&=-z^6,
\end{aligned}
$$

with all higher $p(j)$ zero. Formal coefficient extraction reduces the
homogeneous operator equation to the recurrence and its initial values.
The polynomial $p(4)$ is nonzero, so the certificate satisfies the complete
existential nonzero-operator condition.

## Falsifier

A natural index $n\ge3$ at which the literal signed sum violates the displayed
recurrence would contradict the first conjunct of
`D5/S3/Combinatorics/BinomialBases/MatharA001722.result`.
A nonzero coefficient of the displayed formal differential expression would
contradict the explicit operator certificate used to prove its second conjunct.

## Evidence

`D5/S3/Combinatorics/BinomialBases/MatharA001722.lean` defines `s`, `a`, `G`
and the full `claim`; its sole public theorem is `result : claim`.
The private statements `falling_degree` and `shifted_coeff` derive the
coefficient bridge; `shifted_step` and `recurrence_forward` establish the
integer recurrence; `recurrence_rational`, `initial`, `term_coeff`,
`op_expansion` and `annihilates` establish the formal-series certificate.
Each helper is used on that result's proof path.

The proof uses pinned Mathlib polynomial degree, Taylor/Hasse coefficient,
finite-product, coefficient-extraction and formal-derivative APIs and
normalization. No frozen D5 mathematical supplier is an input. The accepted
axiom closure is `Classical.choice`, `Quot.sound`, `propext`.
The canonical Blueprint attaches the `Proved` resolution claim to the
frozen public `result`, preserving both original clauses.

## Triage

Tier 1: an explicit external OEIS conjecture posed in 2026, with a full
universal symbolic resolution. The prior registration is
[issue #27903](https://github.com/the-omega-institute/trureturing/issues/27903).
The mathematical event and its two clauses are those of the
[original immutable carrier](https://github.com/the-omega-institute/trureturing/issues/27903#issuecomment-6715378511).
All ten authored theorem proofs are `bind-only` under the repository's
normalization rule. The nine private theorems have actual helper consumers;
the public `result` uses `admission_basis: open-problem-resolution`.
No escape witness, new proof technique or exhaustive novelty claim is made.
Utility is `none`.

### What the settlement shows

- **Proved:** the exact recurrence and D-finiteness hold together for the
  original inclusive signed sum and every required natural index.
  The mechanism is the second-coefficient realization in the translated
  falling product, whose next factor gives the polynomial elimination identity.
- **Proved within the result:** the exhibited fourth-order homogeneous
  operator annihilates the full ordinary rational formal series and has
  highest coefficient $-z^6$. The auxiliary identities are proof steps,
  without additional exported theorem targets.
- **Open here:** minimal differential order, analytic convergence or
  asymptotics, and parameterized versions with other shifts, weights or
  extracted coefficient degrees. The translated-product mechanism suggests
  such questions but supplies no parameterized theorem in this delivery.
- **Source-dependent consequences:** this settles the source's joint
  recurrence/D-finiteness assertion. Other OEIS identities, bracket-to-product
  interpretations and related generalized Stirling conjectures retain their
  separate proof obligations. No dependency of another named open problem on
  this assertion is established by the bounded readings.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive absence of earlier proofs remain
unverified beyond the stated source and literature scope.

The four-slot source-binding audit is unfinished. The complete-family
realization keeps both the recurrence and the ordinary formal-series clause.
Its whole-family intervention and sensitivity obligations do not by themselves
supply the producer-checked source-occurrence selectors. The original theorem
has empty telescope and type `claim`; entering that one definition exposes
only private proposition aliases. Recursive entry into those aliases is not
a supported selector route. The selected D5 and Reg targets compile with only the standard accepted axiom
closure. The current scoped report records `declared_unresolved`, no binding
certificate, and `unclassified_form` with rule `source.selection_missing`.
The concrete exception is
[issue #27927](https://github.com/the-omega-institute/trureturing/issues/27927).
No `declared_validated` audit is claimed. The retained Reg source supplies
complete mathematical family evidence; legal raw source reconstruction and
producer-checked binding remain missing.
