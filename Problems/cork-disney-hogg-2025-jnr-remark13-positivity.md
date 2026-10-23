---
slug: cork-disney-hogg-2025-jnr-remark13-positivity
bibkey: corkdisneyhogg2025jnr
doi: 10.1007/s11040-025-09513-3
url: https://arxiv.org/abs/2505.00075v2
triage: theorem
motivation_gids:
  - D5/S3/Analytic/JNRRemarkThirteenPositivity.result
---

# Positivity of the JNR triple sum

## Problem

Cork and Disney-Hogg, *Locations of JNR skyrmions*, Appendix A, Remark 13,
conjecture:

> The above proof shows that this is positive so long as Σᵢ (λᵢ²/|yᵢ|²) yᵢ = 0, however we conjecture that the sum in (18) is positive for any choice of yᵢ ∈ ℝ³∖{aᵢ}.

The source and equation are recorded in the
[Library note](../Library/Geometry/corkdisneyhogg2025jnr.md).
The exact statement is preregistered in
[#19039](https://github.com/the-omega-institute/trureturing/issues/19039).

### Statement echo

| Source clause | Lean counterpart | Interpretation |
| --- | --- | --- |
| $N+1$ poles, at least two | `N : ℕ`, `1 ≤ N`, `Fin (N + 1)` | Every finite size in the stated range |
| Pure imaginary quaternion positions in $\mathbb R^3$ | `EuclideanSpace ℝ (Fin 3)`, `a`, `x` | The source's Euclidean norm and real inner product |
| $\lambda_i>0$, $\mu>0$ | `∀ i, 0 < lam i`, `0 < mu` | Strict positivity retained |
| Distinct poles | `Function.Injective a` | The source configuration assumption |
| $y_i=a_i-x_*$ and the printed exclusion | `fun i => a i - x`, `∀ i, x ≠ a i` | The off-pole interpretation fixed by #19039 |
| Equation (3) at zero | `rho0` | The full weighted reciprocal-square sum |
| Equation (18) | `S` | All ordered triples, denominator factors and normalization retained |
| Positive without condition (15) | `result : claim` | No balance premise |

No further binder or hypothesis restricts the claim. Division in the definitions
is total real division; the theorem's hypotheses make every relevant denominator
strictly positive.

## Motivation

This is the tier-1 external named conjecture registered in #19039.
The frozen settling declaration is
`D5/S3/Analytic/JNRRemarkThirteenPositivity.result`.
Its admission basis is `open-problem-resolution (#19039; Proved)`.

## Gap

Remark 13 states a general conjecture after describing restricted proofs for
small numbers of poles, equal weights and a common sphere. The literature screen
in #19039 found no general settlement in its searched scope. Its completeness
is `ASSUMED-UNVERIFIED`; it is not a claim of exhaustive literature coverage.

## Route

Write $w_i=\lambda_i^2$, $r_i=\lVert y_i\rVert^2$, $t=\mu^2$ and set

$$
\alpha_i=\frac{w_i}{r_i+t},\qquad
\beta_i=\frac{w_i}{r_i},\qquad
q_i=\frac{w_i}{r_i(r_i+t)}.
$$

All these scalars are positive and $\beta_i=\alpha_i+tq_i$.
Put $A=\sum_i\alpha_i$, $B=\sum_i\alpha_i y_i$,
$C=\sum_i\beta_i$, $D=\sum_i\beta_i y_i$, $m=C^{-1}D$.
Factoring the two outer sums and recentering at $m$ gives

$$
CS=\sum_jq_j\langle Ay_j-B,Cy_j-D\rangle,
\qquad t\sum_iq_i(y_i-m)=Am-B,
$$

and hence

$$
S=A\sum_iq_i\lVert y_i-m\rVert^2+
\frac{\lVert Am-B\rVert^2}{t}.
$$

The private declarations `Algebra.triple_factor`, `Algebra.centered_relation`
and `Algebra.factored_sos` prove these steps. `Algebra.triple_positive` uses
two distinct vectors to obtain one nonzero displacement from $m$; a positive
summand makes the first term strictly positive. `result` specializes these
identities to the literal source expression. All names are in
`D5.S3.Analytic.JNRRemarkThirteenPositivity`.

## Falsifier

An admissible configuration with $S\le0$ would refute the source conjecture.
A mismatch between the literal triple sum and the displayed square identity,
or failure of strictness for two distinct vectors, would invalidate this route.
A finite numerical sample alone settles neither universal assertion.

## Evidence

`D5.S3.Analytic.JNRRemarkThirteenPositivity.result` proves the complete public
`claim`. The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}. The five private helper proofs and
the settling proof are classified `bind-only`; no escape witness is asserted.
The module contains symbolic identities and inequalities, with `utility: none`.

The escape audit of `D5.S3.Analytic.JNRRemarkThirteenPositivity.result` is
unfinished: [#19104](https://github.com/the-omega-institute/trureturing/issues/19104).
No Reg source or validated four-slot registration is claimed. The missing
compiled evidence comprises full source reconstruction, observation equivalence,
actual positive-law and whole-family intervention/sensitivity bridges, and a
lawful typed registration selecting an enrolled template.

### Experiment

The independent finite checks are in
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/7259d8d6c51ea9b5c1a72bc731e94dc9681817a9/docs/reports/cork-disney-hogg-2025-jnr-remark13-positivity).
Command: `python3 /Users/auric/trureturing-experiments/docs/reports/cork-disney-hogg-2025-jnr-remark13-positivity/check.py`.
Exit code: 0. The script's SHA-256 is
`34bc783540f3264fc197e71a603340b23ad130f02f3d9595355bd26e83c299c9`.
The pinned script exists and its bytes match that digest.

Computed scope: 30 random rational instances, dimensions 2–4 with 2–4 points,
verify equality of (18), the scalar closed form and the sum of squares, and
strict positivity. A separate 20,000 random floating configurations in
$\mathbb R^3$, with 2–7 points, have positive $S$; the maximum relative
identity error is $1.61\times10^{-14}$. The script also checks one constant
family with three repeated vectors and obtains $S=0$. These finite checks
support the identities; the universal conclusion is supplied by Lean.

## Triage

### What the settlement shows

1. **Proved — kernel-checked generic identity.** `Algebra.factored_sos`
   quantifies over every finite index type and real inner-product space.
   It assumes $t\ne0$, $\beta_i=\alpha_i+tq_i$ and $Cm=D$.
   Neither dimension three, completeness nor finite dimensionality is used.
2. **Proved — kernel-checked weakened strictness.** `Algebra.triple_positive`
   requires only two distinct vectors, positive $\alpha_i,\beta_i,q_i,t$ and
   the coefficient relation. Pairwise distinctness is sufficient but unnecessary
   for this general positivity statement.
3. **Proved in prose — equality classification.** For a nonempty finite family
   with positive $\alpha_i,\beta_i,q_i,t$ and the coefficient relation, a
   nonconstant family has positive normalized triple sum by
   `Algebra.triple_positive`. A constant family makes both original differences
   zero in every summand, hence the sum is zero. Thus the sum is nonnegative
   and vanishes exactly for a constant family. Substituting the coefficients
   above gives the same conclusion for nonzero source vectors and positive
   source weights and parameter. This classification is a consequence of the
   checked helper and the stated zero-summand argument, not a separate Lean
   theorem. The finite constant-family experiment is labelled computed above.
4. **Open — scope boundary.** `result` settles expression (18). Equality with
   the earlier double sum away from condition (15), and physical realization,
   remain outside the formal statement. The source's other results retain their
   stated hypotheses; this result removes balance only for positivity of (18).
5. **Proved in prose — balance substitution.** The kernel-checked `result`
   has no balance hypothesis. When $D=0$, positivity of $C$ gives $m=0$;
   the second square is then $\lVert B\rVert^2/t$. It need not vanish:
   on a real line take $y_1=1$, $y_2=-2$, $w_1=1$, $w_2=2$, $t=1$.
   Then $D=1-1=0$, while $B=1/2-4/5=-3/10$ and the square equals $9/100$.
   This is an algebraic explanation, not an additional kernel-checked theorem.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The screen recorded in #19039
reads arXiv:2505.00075v2 and identifies correction DOI
`10.1007/s11040-026-09577-9` as correcting another formula, with no settlement
of Remark 13 reported. The search seat reports no matching formal-conjectures
entry and an INSPIRE record with zero citations at its reading. Google Scholar,
Semantic Scholar and native MathDB were not fully accessible. Those bounded
readings do not prove that no independent settlement exists.
