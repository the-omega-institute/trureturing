---
slug: bala-a119370-exponential
bibkey: bala2024a119370
doi: null
url: https://oeis.org/A119370
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo.lagrange_coefficient
---

# Bala's A119370 exponential conjecture

## Problem

The original OEIS A119370 NAME is:

> G.f. satisfies A(x) = 1 + x*A(x)^2 + x^2*(A(x)^2 - A(x)).

Peter Bala's FORMULA conjecture is:

> Conjecture: A(x) = 1 + x*exp(Sum_{n >= 1} g(n, x)*x^n/n), where g(n, x) = Sum_{k = 0..n} binomial(n, k)^2*(1 + x)^k. Cf. A105633 and A167638.

The source is revision 37 at
<https://raw.githubusercontent.com/oeis/oeisdata/65556c7cb2030c806e532786d4e1cb4a0fd57164/seq/A119/A119370.seq>.
The conjecture is attributed to Bala, Sep 10 2024. The entry was authored by Paul D. Hanna.
The full exact question is registered in [#30685](https://github.com/the-omega-institute/trureturing/issues/30685),
with the unchanged common event in [comment 6888849692](https://github.com/the-omega-institute/trureturing/issues/30685#issuecomment-6888849692).

### Exact formal meaning

Work in $\mathbb Q[[X]]$. First construct the unique series $A$ with $A_0=1$ and

$$A=1+XA^2+X^2(A^2-A).$$

For every $n\ge1$ put

$$g_n(X)=\sum_{k=0}^n\binom nk^2(1+X)^k,\qquad
L(X)=\sum_{n\ge1}\frac{X^ng_n(X)}n.$$

Each coefficient of the second sum has finitely many contributions, since its nth
summand is divisible by $X^n$. Thus $L_0=0$. Define

$$\operatorname{Exp}(L)=\sum_{j\ge0}\frac{L^j}{j!},$$

or equivalently substitute $L$ into the formal exponential power series. Its degree-m
coefficient receives only $j\le m$; j=0 contributes the constant series one.
The required identity is the whole-series equality $A=1+X\operatorname{Exp}(L)$,
hence equality at every coefficient m, including m=0. The variable in $(1+X)^k$
is the same X as the outer $X^n$.

The printed branch uses the unique square root S with constant coefficient one:

$$S^2=(1+X^2)^2-4X(1+X),\qquad
A=\frac{(1+X^2)-S}{2X(1+X)}.$$

The numerator must first be proved divisible by X. Removing that factor by
coefficient shifting and multiplying by the inverse of the unit $2(1+X)$ is the
formal meaning of this quotient. No inverse of X is involved.

| Source requirement | Mathematical interface |
| --- | --- |
| Independent normalized quadratic source | `IsSourceSeries`; existence and uniqueness precede use of the exponential. |
| Both finite-row endpoints | `row`, the complete range 0 through n. |
| Positive outer index and local finiteness | `logarithm`, degree m uses only 1 through m. |
| Formal exponential and zeroth term | `formalExp`, admissible substitution into `PowerSeries.exp`. |
| Same variable after specialization | The original polynomial-coefficient `Expansion.diagonal` evaluates Y at 1+X and z at X. |
| Every m including zero | Whole-series equality and its coefficient projections. |
| Printed normalized root | `discriminant`, constant-one root uniqueness, X divisibility, and `printedBranch`. |

## Motivation

The exact all-coefficient equality identifies two independent formal descriptions of
the A119370 source. It also supplies the published square-root normalization. The
native Lagrange theorem is the prior mathematical supplier, not the question's answer.
The intended resolution is `BalaA119370Exponential.result`, with
`admission_basis: open-problem-resolution` under #30685.

## Route

Gessel, *Lagrange Inversion*, arXiv:1609.05988v1, Theorem 2.1.1 and equation (2.2.9),
supply classical Lagrange inversion and its logarithmic specialization. Section 3.4
gives the Narayana family. These are established methods, not a novelty claim.

Construct $C\in\mathbb Q[Y][[z]]$ independently with $C_0=1$ and

$$C=(1+zC)(1+YzC).$$

For each rational y, the existing rational-valued `lagrange_coefficient` applies to
$f=zC_y$ and $R(t)=(1+t)(1+yt)$. Its power-coefficient formula, applied inside the
logarithmic client, gives

$$n[z^n]\log C_y=[t^n]R(t)^n=\sum_{k=0}^n\binom nk^2y^k.$$

Polynomial extensionality lifts the identity from every rational parameter to Q[Y].
The existing continuous diagonal evaluates z=X and Y=1+X. Coefficient m uses only
outer indices n<=m, so this is a formal locally finite evaluation. Its substitution
law identifies $\log D(C)=L$.

Writing $b=D(C)$ gives $b=(1+Xb)(1+X(1+X)b)$. The series $1+Xb$ satisfies the
original quadratic, so original-source uniqueness identifies it with A. Formal
exp/log inversion then gives the required exponential. Finally set
$S=1+X^2-2X(1+X)A$; the source quadratic proves its square and the factorization
$(T-S)(T+S)=0$ proves uniqueness, since T+S has constant coefficient two.

## Falsifier

A normalized rational solution of the original quadratic and a degree at which its
coefficient differs from the displayed exponential would refute the original event.
A failed method or a finite prefix does not settle this universal question.

## Gap

The qualified searches in #30685 found no authenticated prior whole-question proof
in the searched scope. Gessel's generic result and related Hanna assertions in
A105633 and A216604 remain prior suppliers. An exhaustive worldwide literature
inventory, continued openness and publication priority are unverified. The source
correspondence is an explicit mathematical interpretation of the cited entry; Lean
checks the encoded statement rather than the external document.

## Evidence

The exact Lean implementation and its canonical Scribe are the verification surfaces.
The complete source statement has a scoped kernel build and a source-owned Reg mirror.
The original polynomial diagonal is reused by publicizing its existing declarations;
its mathematical proofs are preserved. Canonical Blueprint emission covers both modules.

The continuity supplier's exact source-binding audit remains unfinished: the enrolled
function-operand route rejects the bundled algebra-homomorphism coercion. Its compiled
mathematical audit proofs and the successful source-bound registrations are retained;
[the concrete exception](https://github.com/the-omega-institute/trureturing/issues/30685#issuecomment-6889545983)
is tracked under CLAUDE §3.9. No frozen settlement or publication priority is asserted.
Independent source fidelity and prefreeze review remain required.

## Triage

This is a Tier 1 exact named external question under the preregistered scope of #30685.
The complete original equation, all natural degrees, local finiteness, both row endpoints,
the exponential's zeroth power, and the printed formal branch are required together.
No finite computation, partial identity or generic method alone is a resolution.

The proved mechanism is the logarithmic coefficient identity for the product quadratic
C=(1+zC)(1+YzC), followed by the filtered evaluation Y=1+X, z=X. This explains why the
same variable can occur in both the finite row and its outer power: a coefficient of
fixed degree uses only finitely many outer indices. The parameter identity is an
application of classical Lagrange inversion. Other diagonal substitutions and nearby
OEIS conjectures are not claimed as further external resolutions.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive external literature coverage are unverified. The
external document-to-formal-statement correspondence requires mathematical review.
The continuity supplier's exact source-binding audit is unfinished under the linked
issue exception. Independent external-source correspondence review and frozen settlement
remain outside this implementation candidate.
