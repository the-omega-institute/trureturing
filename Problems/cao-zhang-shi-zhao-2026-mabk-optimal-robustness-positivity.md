---
slug: cao-zhang-shi-zhao-2026-mabk-optimal-robustness-positivity
bibkey: cao2026sizeindependent
doi: 10.48550/arXiv.2608.30851
url: https://arxiv.org/abs/2608.30851v1
triage: theorem
motivation_gids:
  - D5/S3/QuantumBounds/MabkSelfTestingPositivity.result
---

# Cao–Zhang–Shi–Zhao MABK positivity for the two remaining blocks

## Problem

Shen Cao, Xingjian Zhang, Fei Shi and Qi Zhao, *Size-Independent Robustness
in Multipartite Bell Self-Testing*, arXiv:2608.30851v1, Supplemental Material,
“Efficient Verification of Optimal Lower Bound”, state:

> For $n \le 5$ this bound is already established analytically [20, 23]; for
> $n \geq 6$ the two remaining cases ($h = 1, 2$) are an open conjecture
> supported by the numerical evidence above.

The conjecture is that the five-term expression $\lambda_{\vec a}$ on
PDF p. 37 is nonnegative at every point of $[0,\kappa]^n$, where
$\kappa=1-1/\sqrt2$, for every $n\ge6$ and $h\in\{1,2\}$.
The source has complementary index sets $T$ and $J$, of cardinalities
$h$ and $d=n-h$. Its convention $h\le d$ follows from these hypotheses.
Issue #11561 preregisters the literal expression, full quantifiers,
Tier 1 classification and literature check.

The definition `lambdaA` preserves all five terms, their coefficients,
both complementary products in each paired term, and the real square roots.
The bijection from `Fin n` to the source indices is $i\mapsto i+1$.
The definitions `kappa` and `claim` express the endpoint and complete
conjecture. The theorem `result : claim` proves it.

## Motivation

The conjectured parameters are
$\bar s_n=(1+\sqrt2)/2^{n/2+1}$ and $\bar\mu=-1/\sqrt2$.
The source proves the other block cases analytically, and identifies
$h=1,2$ as the remaining scalar obstruction for $n\ge6$.
`D5/S3/QuantumBounds/MabkSelfTestingPositivity.result` supplies that scalar
inequality for every party number in the stated range, without restricting
the cube to a grid. The operator reductions and extractability statements
are separate, unformalized obligations.

## Gap

The preregistered literature check in #11561 records arXiv v1, zero citing
works in the Semantic Scholar query, and no entry for this statement in
the MathDB queries. Google Scholar and INSPIRE were not reached.
These are bounded, source-reported readings; they do not establish a
worldwide novelty or priority claim. The source TeX explicitly calls
the two cases open. Repository and pinned-library searches find no
owner for the same conjecture in the searched scope.

## Route

Put $r=\sqrt2$, $s=1+r$, $c=s/r$ and, for each coordinate,
$x_i=1-v_i$, $y_i=\sqrt{2v_i-v_i^2}$, $a_i=1-cv_i$, $b_i=cv_i$.
For a finite block $E$, use $A_E,B_E,X_E,Y_E$ for their products.
The cube gives $a_i\ge x_i^2$, $0\le b_i\le1/2$,
$0\le y_i^2\le1/2$, $x_i^2+y_i^2=1$ and $b_i\ge(c/2)y_i^2$.

Let $q=X_J$, $B=B_T$, $Y=Y_T$ and $K=(2+r)BY$.
Retaining the positive cubic term gives

$$\lambda_{\vec a}\ge1-s^2X_T^2Y_J^2+(rB-s^2Y^2)q^2+Kq^3.$$

Finite-set induction proves $Y_J^2\le(1-q^2)2^{1-d}$.
The identity $2q^3-3q^2+1=(1-q)^2(2q+1)$ gives
$q^3\ge(3q^2-1)/2$. Thus

$$\lambda_{\vec a}\ge C(1-q^2)+Fq^2,$$

where $C=1-K/2-s^2 2^{1-d}$ and $F=1-s^2Y^2+rB+K$.
For $h=1$, a denominator-cleared unit-circle factorization proves $F\ge0$.
For $h=2$, $B\ge s^2Y^2/8$ and $0\le Y\le1/2$ give

$$F\ge1-(5/2+13r/8)Y^2+(5/4+7r/8)Y^3
\ge(34-19r)/64>0.$$

The complementary block has $d\ge5$ for $h=1$ and $d\ge4$ for $h=2$;
the respective bounds on $K$ establish $C\ge0$.
Since $q\in[0,1]$, the final lower bound is nonnegative.

## Falsifier

A counterexample to the encoded claim would supply $n\ge6$,
$|T|\in\{1,2\}$ and one point of the whole cube with `lambdaA < 0`.
The kernel-checked theorem excludes such a witness for the stated real
expression. A different coefficient, omitted product, altered square root
or weakened cube would define a different problem. No such substitution
is used in `lambdaA`.

## Evidence

The mathematical source is
`D5/S3/QuantumBounds/MabkSelfTestingPositivity.lean`, with public definitions
`kappa`, `lambdaA`, `claim`, and the sole public theorem `result`.
The two private content theorems are `product_gap` (finite-set induction)
and `block_bound` (one- and two-element scalar estimates).
Both are used on the live path of `result`. The module imports pinned
Mathlib only. The proof uses the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

The Scribe source and its emitted Markdown expose the complete expression,
quantifiers and cube assumptions. The `Proved` resolution claim links this
dossier to the frozen settling theorem. The Reg mirror
`Reg/D5/S3/QuantumBounds/MabkSelfTestingPositivity.lean` declares the
dependent-family realization audit; its residual continuation is `open`.

## Triage

Tier 1: a recent quant-ph conjecture with the full analytic proof for the
other block cases and numerical support for the two remaining cases.
Resolution: `Proved`. Admission basis: `open-problem-resolution (#11561)`.
The public settling theorem and both private helper theorems have
`proof_shape: content`. Utility is `none`: the result is an analytic
inequality over all $n\ge6$ and all real cube points, rather than an
enumeration, checker, numerical reduction or certified finite instance.

### What the settlement shows

- **Proved in this module:** nonnegativity on the entire cube for both
  remaining block sizes and every $n\ge6$. The decisive mechanism is
  the product gap on $J$, preservation of a positive cubic term, and
  the lower bound $C(1-q^2)+Fq^2$. Dependence on the complementary
  dimension enters through the decreasing factor $2^{1-d}$.
- **Proved inside the result's proof:** the one-element unit-circle
  factorization and the two-element cubic lower estimate for $F$.
  The generic product-gap helper applies to any nonempty finite set
  with $u_i+z_i=1$, $u_i\in[0,1]$, $z_i\in[0,1/2]$.
  These are proof components, not additional public settling theorems.
- **Computed:** for the source's boundary configuration $v_T=\kappa$,
  $v_J=0$, the reduced expression is $0$ when $h=1$ and
  $(4-\sqrt2)/8$ when $h=2$. The command
  `python3 -c 'import sympy as s; r=s.sqrt(2); print([s.simplify(1+r*s.Rational(1,2)**h-(1+r)**2/r**(2*h)+(2+r)*s.Rational(1,2)**h/r**h) for h in (1,2)])'`
  returns `[0, 1/2 - sqrt(2)/8]`. This algebra computation is not a
  kernel theorem about equality configurations.
- **Open:** the exact $h=2$ minimum, classification of all $h=1$
  equality points, extension beyond the cube, and optimality of the
  block-size thresholds in this argument. No relaxed-hypothesis
  theorem is delivered.
- **Open as a formalization obligation:** the source's Bell-operator
  reduction, the other block cases and the extractability conclusions.
  Under the source's reductions, the proved scalar conjecture removes
  its remaining obstruction to optimal MABK robustness for all party
  numbers; those reductions are literature conclusions outside this module.

## ASSUMED-UNVERIFIED

Worldwide priority and exhaustive absence of another answer are not
established by the bounded literature searches. The kernel does not
authenticate an external paper or its interpretation. The source's
Bell-operator and extractability implications have not been checked in
Lean here. An `open` audit residual does not prove undecidability or
inexhaustibility.
