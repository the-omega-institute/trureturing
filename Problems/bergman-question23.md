---
slug: bergman-question23
bibkey: bergman2014eggert
doi: 10.1090/conm/609/12101
url: https://arxiv.org/abs/1206.0326v2
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.claim
---

# Bergman's Question 23

## Problem

George M. Bergman, *Thoughts on Eggert's Conjecture*, Section 6, Question 23,
equation (22), printed p.16 of the author final preprint, asks:

> If R is a commutative algebra over a field F, V a finite-dimensional
> subspace of R, and n a positive integer, must
> dim(V/Ann_V V^n) ≤ dim V^n?

The preceding definition is `Ann_V W = {x ∈ V | xW = {0}}`. Convention 2
assumes associativity and does not generally assume an identity. All
dimensions are over the same field. The space `V^n` is the span of all mixed
products of exactly n elements of V, distinct from the set of pure powers.
The following remark only concerns the cases `dim V^n ≤ 4`.

| Source clause | Formal counterpart |
| --- | --- |
| every field F | `F : Type`, `Field F`, with no characteristic hypothesis |
| every associative commutative F-algebra R | `R : Type`, additive group and F-module, with actual bilinear `μ`, associativity and commutativity |
| no identity required | no identity appears in the multiplication interface |
| finite dimensional V | `V : Submodule F R`, `FiniteDimensional F V` |
| every n ≥ 1 | `k : ℕ` represents exponent k+1, including k=0 |
| actual mixed product span | `mixedPower μ V`, recursively using `Submodule.map₂` |
| genuine annihilator quotient | `V ⧸ relativeAnnihilator μ V (mixedPower μ V k)` |
| dimension inequality | `Module.finrank F` on the quotient and mixed product subspace |

The ambient algebra in the universal claim need not be finite dimensional
or nilpotent. A finite dimensional nilpotent counterexample is allowed by
the question; those properties are properties of the witness.

## Motivation

A classical Artinian Gorenstein idealization can have first graded component
larger than its second graded component. The reverse-degree dual summand
retains coefficient separation even when the middle component is smaller.
The full mechanism is attributed to Stanley, *Hilbert Functions of Graded
Algebras*, Example 4.3; see `Library/Certificates/stanley1978hilbert.md`.

## Gap

The mathematical bridge connects the actual multiplication, mixed product
spaces and annihilator quotient. A list of Hilbert-vector entries, an
assumed perfect pairing, or a nondegenerate map on unrelated vector spaces
does not by itself answer the question. All-field coefficient identities
must avoid factorials and characteristic-zero restrictions.

## Route

For a field F and integers `n ≥ 2`, `m ≥ 3`, put `t=n+1`. Use basis labels
`e_a` for `1 ≤ |a| ≤ t` and `f_b` for `0 ≤ |b| ≤ t`, where a,b are monomial
multisets on m variables. The bilinear symmetric multiplication is

$$
 e_a e_c = \begin{cases}e_{a+c}&|a+c|\le t,\\0&\text{otherwise},\end{cases}
 \qquad
 e_a f_b = \begin{cases}f_{b-a}&a\le b,\\0&\text{otherwise},\end{cases}
 \qquad f_b f_c=0.
$$

The e-e rule is truncated polynomial multiplication. The e-f rule is its
transpose, so the action subtracts multiplicities. With two e labels and
one f label, either bracketing is nonzero exactly when the sum of the e
indices is contained in the f index. If the e-e product truncates, this
containment is impossible. Two f factors force zero in either bracketing.

Give `e_a` degree `|a|` and `f_b` degree `t+1-|b|`. The actual homogeneous
degree-one subspace V has generators `e_i` and all `f_b` with `|b|=t`.
For `1 ≤ d ≤ t`, its d-fold mixed product span is the whole degree-d
subspace: an e monomial splits into individual variables, and
`f_b = e_i f_(b+i)` whenever the target degree is at least two. This uses
ordinary products, without polarization or division by factorials.

In particular, `V^n` has basis the `e_a` with `|a|=n` and `f_b` with
`|b|=2`. To test a vector in `Ann_V(V^n)`, multiplication by `e_(n i)`
reads every e coefficient in separate e coordinates. For a top f index b,
choose an occurrence i in b and multiply by `e_(b-i)`. The coefficient of
`f_i` is exactly the coefficient of `f_b` in the original vector. Thus
the relative annihilator is zero.

Stars and bars then gives the formulas

$$
\begin{aligned}
 \dim R&=2\binom{m+n+1}{n+1}-1,\\
 \dim V&=m+\binom{m+n}{n+1},\\
 \dim V^n&=\binom{m+n-1}{n}+\binom{m+1}{2},\\
 \dim(V/\operatorname{Ann}_V(V^n))-\dim V^n
  &=\binom{m+n-1}{n+1}-\binom m2\ge\binom m3>0.
\end{aligned}
$$

Here R is the positive ideal. The entire unital idealization has one more
basis vector; for n=2,m=3 the dimensions are 39 and 40 respectively.
The corresponding V and V² dimensions are 13 and 12.

All nonzero homogeneous degrees lie between one and n+2 and products add
degrees. Hence every product of n+3 elements of R is zero. For fixed F and
fixed n≥2, the real dimension ratio satisfies

$$
 \frac{\dim(V/\operatorname{Ann}_V(V^n))}{\dim V^n}
 \ge \frac{m+n}{2(n+1)}.
$$

Indeed, if `E=binom(m+n-1,n)` and `B=binom(m+1,2)`, then `E≥B>0` and
`(n+1) binom(m+n,n+1)=(m+n)E`. This proves unboundedness as m increases.

## Falsifier

A failure of generic associativity, the mixed product span equality,
coefficient separation, all-field scope, any dimension formula, or the
ratio estimate invalidates the nominated full-family delivery. A verified
single member alone does not complete that delivery. The n=1 instance
remains in the universal assertion and is not separately settled by this
counterexample family.

## Evidence

[Issue 30097](https://github.com/the-omega-institute/trureturing/issues/30097)
preregisters the literal question and the full family before Lean probes.
Its qualified body SHA256 is
`e2c1da29317c32de8a1201fdb33cc32aa765955a665d73cf8a5f6e8e542be63c`.
The admission basis is `open-problem-resolution`. No originality of
Stanley's construction is asserted.

The bounded qualification read the complete relevant primary sections,
the current author versions, the related module-length restatement,
Stanley's example, related Perazzo literature, relevant public and private
D5 code, and overlapping issues. It located no explicit exact Question-23
settlement in that scope. The related module-length question is the same
event under specialization, rather than a second problem.

The implementation directly reuses `Contracted`, `product` and
`contractedCommRing` from the frozen Question-15 module. Pinned Mathlib
supplies `Submodule.map₂`, finite-generation closure under bilinear images,
`Finsupp.supportedEquivFinsupp`, `Sym.card_sym_eq_choose` and
`Sym.equivNatSumOfFintype`. The last interface is available but the
implementation uses multisets directly, avoiding an extra exponent-vector
equivalence.

The unfinished source-bound audit of `family` is tracked in
[issue 30131](https://github.com/the-omega-institute/trureturing/issues/30131).
The typed Reg proof is retained; its field-instance coordinate lacks a
validated source-binding certificate. This audit boundary is separate from
the mathematical declaration.

## Triage

This is a Tier-1 externally named subsidiary question. The formal family is
`D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.family`, and its
application to the complete original assertion is
`D5/S0/Certificates/Algebra/BergmanQuestion23Refutation.result`. The
construction is classical. No external-open-problem credit is asserted here.

### What the settlement shows

The formal `family` exhibits loss of dimension in an interior graded layer
while higher products still separate every degree-one coefficient. Thus
zero relative annihilator does not force the product space to have at
least the dimension of V; the failure ratio is unbounded for every fixed
field and fixed exponent n≥2. The literal `result` refutes the original
universal Question 23.

The exponent n=1 and the restricted range `dim V^n ≤ 4` are not settled by
this module. Bergman's remark reports a belief that he proved the latter
range; this source remark is not a Lean result asserted here. Minimality
of the counterexample is also not asserted. The argument concerns mixed
product spans and the relative annihilator, and makes no inference about
Eggert's pure-power conjecture or the source's other questions.

## ASSUMED-UNVERIFIED

Worldwide absence of an earlier explicit resolution and priority remain
unverified. A classical construction implying the answer is not itself
evidence that an earlier author explicitly settled the named question.
The Lean declarations do not certify worldwide priority or repository
delivery state.
