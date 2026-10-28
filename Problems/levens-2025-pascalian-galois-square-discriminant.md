---
slug: levens-2025-pascalian-galois-square-discriminant
bibkey: levens2025pascalian
doi: 10.48550/arXiv.2511.03082
url: https://arxiv.org/abs/2511.03082v1
triage: theorem
motivation_gids:
  - D5/S3/Factorization/Galois/LevensPascalian.result
---

# A square discriminant refutes the odd clause of Levens Conjecture 6.4

## Problem

Owen Levens, *Polynomials Arising from Sorted Binomial Coefficients*,
arXiv:2511.03082v1, Section 6.2, Conjecture 6.4 states:

> P_n(z) has full Galois group for even n. For n = 2m + 1, the Galois group of P_n(z) is the mth hyperoctahedral group.

The source defines the Pascalian numbers by
$\langle n,k\rangle=\binom n{\lfloor(n-k)/2\rfloor}$ for $0\le k\le n$
and $P_n(z)=\sum_{k=0}^n\langle n,k\rangle z^{n-k}$.
The target is the second sentence, with $m\ge1$. The counterexample is
$m=24$, $n=49$. Preregistration: [#19007](https://github.com/the-omega-institute/trureturing/issues/19007).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Pascalian coefficient and full polynomial | `P` over rational polynomials, summing every index from zero through n | Natural division is the stated floor; the exponent uses natural subtraction in the source range. |
| n = 2m + 1 | `claim` substitutes `2 * m + 1` into `P` | Every natural m with `1 ≤ m` is included; 24 is included. |
| mth hyperoctahedral group | `hyperoctahedral m`, the centralizer of `signFlip m` on `Fin m × Bool` | The two Boolean values represent the signs. These are precisely signed permutations. |
| The Galois group is that group | Existence of an abstract multiplicative equivalence from `Polynomial.Gal` | This weakest isomorphism reading is refuted, hence so is the permutation-group reading. |
| Refutation of the universal odd sentence | `result : Not claim` | No extra mathematical hypothesis. The even sentence is outside `claim`. |

## Motivation

The source's odd-index assertion would give an abstract isomorphism at
$m=24$. A strict cardinality bound on the actual splitting-field
automorphism group rules it out. The polynomial, sign change,
hyperoctahedral group and quantified claim retain the literal binding
conventions of the preregistration.

## Gap

A square discriminant of the degree-24 binomial truncation forces every
induced root permutation to be even. The full hyperoctahedral group allows
all root-pair permutations. Thus the square-discriminant case violates the
claimed group order. The exact Galois group is not determined by this
obstruction.

## Route

Put $c=\binom{49}{24}=63205303218876$ and
$q(X)=\sum_{j=0}^{24}\binom{49}{j}X^j$. The private lemmas `factorization`,
`differential` and `discriminant_square` establish

$$P_{49}(X)=(1+X)q(X^2),\qquad
(1+X)q'(X)-49q(X)=-25cX^{24},$$

$$\operatorname{Disc}(q)=(7\cdot5^{23}c^{11})^2.$$

The private `q_separable` proves separability, and `rational_vandermonde`
produces a rational Vandermonde determinant. Its nonzeroness follows from
the distinct roots in `sign_eq_one_of_vandermonde_sq`, which forces every
induced permutation to have
sign one. The constructed injection in `card_bound_of_root_coordinates`,
used by `cardinal_bound`, gives

$$|\operatorname{Gal}(P_{49}/\mathbb Q)|\le
2^{24}|A_{24}|<2^{24}24!=|B_{24}|.$$

The exact existing prerequisite
`PerfectMatchingCount.involution_iff_cycleType` supplies the cycle-type
characterization used in the hyperoctahedral count. Its mathematical
statement and proof are preserved.

## Falsifier

A source convention excluding m=24, an invalid polynomial or discriminant
identity, or a failure of the root-coordinate injection would invalidate
this route. The formal endpoint checks the full unconditioned negation
under the stated conventions; a numerical calculation alone is not its
proof.

## Evidence

The settling declaration is
`D5/S3/Factorization/Galois/LevensPascalian.result`, with type `Not claim`.
The associated Scribe has one Refuted `OpenProblemResolutionClaim` on
that declaration. The admission basis is
`open-problem-resolution (#19007; Refuted)`, and its computational utility
is the certified instance refuting `claim`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
The publicized prerequisite's escape audit is unfinished:
[#19098](https://github.com/the-omega-institute/trureturing/issues/19098).
No faithful whole-family realization, variation, sensitivity and actual
observational-dependence evidence is supplied, and no Reg mirror or
`declared_validated` status is claimed.

### Independent exact computation

[Experiment directory at commit 17c1c8c89e264f59b33ad7ab83ba82e3da6b33e3](https://github.com/the-omega-institute/trureturing-experiments/tree/17c1c8c89e264f59b33ad7ab83ba82e3da6b33e3/docs/reports/levens-2025-pascalian-galois-square-discriminant).
Command: `python3 check.py` in that directory; exit 0, `RESULT PASS`.
The SHA-256 of `check.py` is
`f9d9cc0190fc8355f57363fa1322d1acc62505e710949a707c8a92100c5b8241`.
This computation is independent evidence, with no role in the Lean axiom
closure or proof dependencies.

The tested scope is the factorization at n=49; the differential identity
for m=1 through 30; the discriminant closed form for m=2 through 30;
the square identity at m=24; square discriminants among m=2 through 40;
and the four Pell-family values listed below.

## Triage

Tier 1, small-case settlement: **Refuted**. The formal witness has m=24,
n=49 and c=63205303218876. The current result is suitable for independent
fidelity and reuse review; a delivered refutation does not certify
literature completeness or priority.

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Odd-index clause of Conjecture 6.4 | **Proved in Lean:** `result` refutes its universally quantified isomorphism assertion at m=24. |
| Witness m=24, n=49, c=63205303218876 | **Proved in Lean:** `result` uses this m; private `c_value` proves the binomial value. |
| Failure mechanism and strict upper bound | **Proved in Lean:** private `discriminant_square`, `cardinal_bound` and `result` supply the square, the bound and the strict order obstruction. |
| Full factorization at 49 | **Proved in Lean:** private `factorization`. |
| Differential identity for m=1..30 | **Computed:** the experiment entry, exit 0 and the script hash above; no uniform Lean family theorem. |
| Discriminant closed form for m=2..30 | **Computed:** the same experiment entry and tested range. The m=24 identity alone is kernel checked here. |
| Square discriminants for m=2..40 | **Computed:** precisely m=24 in that finite interval. This is not a classification outside it. |
| Pell examples m=24, 840, 28560, 970224 | **Computed:** the experiment verifies respectively the pairs (7,5), (41,29), (239,169), (1393,985) for the square roots of 2m+1 and m+1; all four m are zero modulo four. |
| Even-index clause of Conjecture 6.4 | **Open:** not encoded or settled by `result`. |
| Conjecture 6.3 | **Open:** not encoded or settled by this module. |
| Exact Galois group of P49 | **Open:** only a strict upper bound is proved. |
| General Pell family and classification beyond square-discriminant cases | **Open:** the four computed examples and finite scan supply no uniform theorem. |
| Literature status | **ASSUMED-UNVERIFIED completeness:** the source and the bounded screen in #19007 identify no prior settlement; the Laishram–Yadav full text was not accessed. |

The surviving conclusions are the factorization and the signed-root
upper-bound mechanism, with an even permutation on the 24 root pairs.
The source's even-index sentence and Conjecture 6.3 are independent
questions. Any conclusion relying on the universal odd-index group claim
must exclude or handle this counterexample; no other source theorem is
refuted by the present result.

The discriminant formula is classical: Filaseta–Moy,
arXiv:1803.02754v1, Lemma 3. Scherbak, arXiv:math/0409329, Section 6.1,
Lemma 6 records the differential identity in the truncated-binomial
literature. These are literature attestations; neither foreign source is
an imported Lean dependency. The new conclusion is their consequence for
Levens's named conjecture at the displayed instance.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain ASSUMED-UNVERIFIED, including
the inaccessible Laishram–Yadav full text (IJNT 20, 2024). No exact group,
even-index settlement, Conjecture 6.3 settlement, uniform Pell-family
theorem or classification outside the tested square-discriminant cases
is asserted. Bounded library searches do not establish theorem-search
completeness.
