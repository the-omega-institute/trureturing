---
slug: fisk10-toeplitz
bibkey: fisk2008determinants
doi: null
url: https://arxiv.org/abs/0808.1850v1
triage: theorem
motivation_gids:
  - D5/S3/Zeros/FiskToeplitzRefutation.result
---

# Fisk Question 10: coefficient-Toeplitz minors

## Problem

Steve Fisk, *Questions about determinants and polynomials*, arXiv:0808.1850v1,
PDF p. 4, Question 10 and matrix (5), asks:

> Suppose f∈P⁺₂, and write f = ∑ f_i(x)y^i. Form the infinite matrix

> Show that the resulting matrix is totally stable. That is, every minor is a stable polynomial.

The matrix has $T_f(r,c)=f_{c-r}$ for $r\le c$ and zero otherwise.
The definitions on PDF p. 1 require upper-half-plane nonvanishing and
positive coefficients on the support, with Hurwitz stability meaning all
roots have nonpositive real part. The related *totally stable matrix
conjecture* is Conjecture 21.84, Section 21.10, printed p. 648 of
arXiv:math/0612833v2. Its input class is defined through real substitution,
homogeneous positivity and coefficient positivity; no equality of the two
source classes is assumed.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Real bivariate polynomial, with outer variable $y$ | `Polynomial (Polynomial ℝ)` | Literal carrier; coefficient variable is $x$. |
| $U_2$: nonzero at every pair in the open upper half plane | `Upper` | Both complex variables quantified; nested `Polynomial.eval₂`. |
| $P_2^+$: upper and positive coefficients | `PositiveUpper` | Strict positivity on support; absent coefficients are zero. |
| Matrix (5) | `toeplitz` | Zero-based upper-triangular coefficient shifts. |
| Every minor | `minor`, `claim` | All natural sizes and strictly increasing row and column maps; no sign reversal. |
| All roots in the closed left half plane | `HurwitzStable` | Roots after mapping coefficients to ℂ. |
| Universal assertion is false | `result` | Negation of the literal `claim`. |

The size-zero determinant is one. Structural zero minors are admitted by
the empty root multiset of the zero polynomial. The exhibited minor is
nonzero, so either convention about structural zero stability gives the
same refutation.

## Motivation

Positive upper bivariate polynomials need not have Hurwitz-stable
coefficient-Toeplitz minors. The obstruction already occurs for a product
of two positive affine factors with unequal slopes.

## Gap

Issue #21768 supplies the source statements, literal conventions and
literature screen. The screen distinguishes upper-half-plane stability
preservers and numerical total positivity from Hurwitz stability of
polynomial determinants. It identifies no settlement in the inspected
material; completeness remains ASSUMED-UNVERIFIED.

## Route

Use $f(x,y)=(4x+y+1)(x+y+4)$. Each affine factor has positive imaginary
part when $\operatorname{Im}x,\operatorname{Im}y>0$, and its product has
six positive nonzero coefficients. Rows $0,1,2,3,4$ and columns
$1,2,3,4,5$ give a tridiagonal minor whose subdiagonal is
$a=4x^2+17x+4$, diagonal is $b=5x+5$, and superdiagonal is one.
Its determinant is $b(b^2-a)(b^2-3a)$.

## Falsifier

**Kernel-checked:** `D5/S3/Zeros/FiskToeplitzRefutation.result` negates
`claim`. Its consumed private lemmas `f_positive`, `minor_matrix`,
`minor_factor`, `z_quadratic`, `minor_root` and `z_re` establish the
admissible input, actual ordered minor, factorization
$5(x+1)(21x^2+33x+21)(13x^2-x+13)$, and root
$z=(1+15i\sqrt3)/26$ with $\operatorname{Re}z=1/26>0$.
The determinant is nonzero, as certified inside `minor_root` by its
nonzero value at zero.

## Evidence

The Lean module has no D5 imports and uses pinned Mathlib. The axiom
closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment: [exact symbolic checker](https://github.com/the-omega-institute/trureturing-experiments/tree/a20982709902f74e70f5111a34629b2afb822f02/docs/reports/fisk-q10-toeplitz).
The committed `check.py` was extracted without modification and run as
`python3 /Users/auric/.op-scratch/fisk10-check.py` (exit 0, SymPy 1.14.0).
SHA-256: `35f5227f0ff9ca5aae3dcdbcfbe0e02f7f375f69d6adf093bb3ea6930f2949b0`.
It checks symbolic identities and positivity certificates for all real
$t\ge4$, exact integer members $4\le t\le40$, and all 330 minors of
the first four rows and seven columns of the repeated-factor example;
264 of these minors are nonzero. It uses exact arithmetic, with no
floating-point root finding.

## Triage

1. **Proved in Lean:** at $t=4$, the input is `PositiveUpper`, the ordered
   $5\times5$ minor has the displayed factorization, and its mapped roots
   contain $z$ with real part $1/26$. Evidence: consumed private lemmas
   `f_positive`, `minor_matrix`, `minor_factor`, `minor_root`, `z_re`,
   and public `result`.
2. **Computed:** the exact SymPy checker verifies symbolic identities
   and positivity certificates for all real $t\ge4$, and separately
   rechecks integer $t=4,\ldots,40$. Evidence: the pinned experiment,
   command, exit code and SHA-256 in Evidence. No general-family Lean
   theorem is claimed.
3. **Computed:** for $(1+x+y)^4$, all 330 minors of the first four rows
   and first seven columns pass; 264 are nonzero and have the form
   $c(1+x)^k$ with $c>0$ and $k\ge0$. Evidence: the same exact checker
   and finite scope. This finite-block neighbour survives.
4. **Open:** no classification of all stable subclasses, minimality of
   the $5\times5$ obstruction, or infinite-minor repeated-factor theorem
   is established here.

### What the settlement shows

The failure mechanism is the fifth continuant's factor
$13x^2-x+13$: positivity of the six input coefficients and upper-half-plane
nonvanishing do not exclude its right-half-plane roots. This statement
is proved for the displayed instance by the Lean lemmas listed above.
The parameter-family extension and finite repeated-factor neighbour have
only the computational evidence stated in items 2 and 3.

**Proved in prose for the book's input class:** fixing either variable
of $(4x+y+1)(x+y+4)$ to any real number leaves a product of two real
linear factors, of degree two in the other variable, with leading
coefficients four and one respectively. Both specialized polynomials
therefore have two real roots counted with multiplicity. Its homogeneous
part is $4x^2+5xy+y^2$, with all three coefficients positive, and all
six coefficients of the full polynomial are positive. Thus the same
nonzero minor refutes Conjecture 21.84 under its own input definition;
no separate Lean theorem identifies the book's class with `PositiveUpper`.

Remark 9 states that Question 10 would imply Question 9. Refuting the
stronger assertion does not refute Question 9. The book's results
conditional on total stability do not apply to this counterexample
and are not contradicted. The source's other questions are unsettled
by this module.

## ASSUMED-UNVERIFIED

Literature completeness and novelty clearance are ASSUMED-UNVERIFIED.
The preregistration records 31 note-citation records and 105 book-citation
records screened by metadata, with selected full texts inspected.
OpenAlex coverage was unavailable; several relevant non-arXiv theses,
problem surveys and later-author records remain unread. The literature
screen is not an exhaustive absence proof. The general real-parameter
family and the infinite collection of repeated-factor minors are not
Lean theorems in this delivery.
