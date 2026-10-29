---
slug: kmvc4-simpleaut
bibkey: kaygorodov2026evolution
doi: 10.48550/arXiv.2610.22248
url: https://arxiv.org/abs/2610.22248v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.result
---

# The simple evolution-algebra automorphism maximum

## Problem

Kaygorodov, Martín González and Viruel, *Evolution algebras: a survey of
results and a list of open problems*, arXiv:2610.22248v1, Conjecture 4,
section 2.3, page 28:

> Over ℂ, the maximal order of the automorphism group of a simple
> n-dimensional evolution algebra is max{n!, n(2ⁿ−1)}.

The dimension is positive. The source's natural-basis condition is zero
mixed products. The product is complex bilinear and commutative, without
associativity or a multiplicative unit. Automorphisms are the entire group
of complex linear multiplication-preserving equivalences.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Every positive dimension | `claim` quantifies over $n\in\mathbb N$ with $1\le n$ |
| Every complex vector space of dimension $n$ | Arbitrary carrier, complex module, finite-dimensional instance and finrank equality |
| Evolution product and natural basis | Bilinear product, arbitrary finite basis, zero mixed products and commutativity |
| Simple algebra | `IsSimple`: $A^2\ne0$ and every complex-linear two-sided ideal is zero or the whole space |
| Full finite automorphism group and upper bound | `Finite (Aut μ)` together with the bound on `Nat.card` |
| Maximum is attained | A product on $\mathbb C^n$ with the dimension, commutativity, natural basis, simplicity, finiteness and exact cardinality |

The simplicity definition is literal: “We recall that an algebra A is
simple if A² ≠ 0 and 0 is the only proper ideal.” This sentence is from
the survey's cited arXiv:1601.01832v2, section 4, page 18. All two-sided
complex-linear ideals are quantified, including those not spanned by
natural-basis vectors. The coordinate representative in the attainment
clause does not restrict the universal clause. `Finite` prevents the
natural cardinality of an infinite group from satisfying a bound through
its value zero. The extra dimension equality in the attaining clause
records that the chosen representative has the required dimension.

## Motivation

The full group has a diagonal kernel and a permutation image constrained
by the same support graph. Simplicity adds strong connectivity to the
invertible structure map. The target is their joint maximum, rather than
the product of separately achievable maxima. Preregistration: #21769.

## Gap

The survey reports small-dimensional verification and two attaining
families. Those assertions alone do not give the uniform upper bound.
The needed structural step is that strong connectivity makes the least
successor-compatible quotient one cycle, and an actual supported
permutation gives all of its fibers the same positive cardinality.

## Route

In the settling module, `simple_perfect` and `simple_support_connected`
derive perfection and strong connectivity directly from the ideal
condition. `connected_beta_cycle` projects paths to successor orbits.
`supported_permutation` extracts a nonzero determinant term.
`equal_fibers` restricts that permutation to consecutive quotient fibers,
so their common size $k$ and the quotient size $h$ satisfy $n=hk$.
The existing `EvolutionAutomorphismControl.automorphism_quotient_bound`
then bounds the actual full group by $h(2^h-1)(k!)^h$.
`factorial_period_bound` bounds this by $(hk)!$ when $h,k\ge2$;
the boundary cases $h=1$ and $k=1$ give the two required alternatives.
`simple_bound` transports the estimate to the arbitrary carrier and basis.

`cyclic_family` proves simplicity and exact full-group order
$n(2^n-1)$ for the cyclic product. `complete_simple` and
`complete_aut_card` give the corresponding facts with order $n!$ for the
product of structure matrix $I+J$. Every coordinate permutation lifts;
loops force the diagonal kernel to be trivial. `result` chooses the
larger family in each dimension.

## Falsifier

A positive-dimensional simple complex evolution algebra with an infinite
full automorphism group, or order above the asserted maximum, would
contradict the universal clause. Failure of either attaining product to
have the required simplicity or exact full-group order would invalidate
attainment. A statement about a coordinate subgroup would not settle
this question about the full group.

## Evidence

The settling declaration is
`D5/S3/QuadraticForms/EvolutionAlgebras/SimpleEvolutionAutomorphismMaximum.result`.
It proves the literal `claim` with both universal bound and attainment.
The conjecture source note is `Library/QuadraticForms/kaygorodov2026evolution.md`; the simplicity definition is recorded in `Library/QuadraticForms/cabrera2016evolution.md`.

The four-slot escape audit is unfinished for `result` and the seven
published owner declarations named in
[issue #22095](https://github.com/the-omega-institute/trureturing/issues/22095).
No completed escape registration is claimed.

### Exact experiment

The experiment is in
[trureturing-experiments at 638f7495de97c6d37ce040add1ab2d8ab6329195](https://github.com/the-omega-institute/trureturing-experiments/tree/638f7495de97c6d37ce040add1ab2d8ab6329195/docs/reports/kmv-c4-simpleaut).
The pinned `check.py` has SHA-256
`e2bde776354a34d528a36e2c19ef073fd45b90b23ca82c86403d74d188654389`.
Command executed on its exact extracted bytes:
`python3 /tmp/op-kmvc4/doors/check.py`,
exit 0. It uses exact integers and rational numbers.

## Triage

### What the settlement shows

1. **Proved in the module:** `result` gives the exact maximum in every
   positive dimension. **Proved in prose from that formula:** in dimension
   four it is $\max\{24,60\}=60$, and in dimension six it is
   $\max\{720,378\}=720$. The previously available all-perfect-algebra
   envelope has values $72$ and $1296$ in these dimensions, as stated by
   `EvolutionAutomorphismMaximum.result`; that comparison theorem is not
   on this module's dependency path. The simple restriction therefore
   sharpens those values to $60$ and $720$.
2. **Proved in the module:** `connected_beta_cycle`, `supported_permutation`
   and `equal_fibers` establish the joint mechanism for the same algebra.
   `coordinate_simple_bound` uses the resulting single quotient cycle and
   common fiber size in the actual kernel/image estimate. Separate
   optima of the two group factors are not combined as if jointly attained.
3. **Proved in the module:** `cyclic_family`, `complete_simple` and
   `complete_aut_card` establish simplicity and full-group orders
   $n(2^n-1)$ and $n!$ of the cyclic and $I+J$ families for all positive $n$.
4. **Proved in the module:** `simple_bound` needs the finite natural-basis
   zero-mixed-product law, simplicity and the dimension, with no separate
   commutativity hypothesis. The public claim retains the source's
   commutativity clause.
5. **Computed by the exact experiment:** admissible labeled supports in
   dimensions $1,2,3,4$ number $1,4,138,24416$; maxima of diagonal order
   times graph-group order are $1,6,21,60$. Independent integer-lattice
   checks cover all $143$ retained supports through dimension three.
   The factorial comparison is checked on exactly $2191$ pairs
   $h,k\ge2$ with $hk\le500$; the Mersenne-gcd identity on exactly $4096$
   pairs $1\le a,b\le64$; both exact attaining families through dimension
   eight; and the singular unequal-fiber and non-lifting-symmetry negative
   controls. These finite checks do not establish a uniform theorem.
6. **Open:** classification of all equality algebras, and optimal
   attainment over fields other than $\mathbb C$. Neither follows merely
   from the maximum formula. The proof settles the two parts of
   Conjecture 4; it does not alter the independent all-perfect-algebra
   result or settle unrelated questions in the survey.

### Literature status

The source ingredients are literature-attested. The combined sharp
simple-algebra bound is a suspected-novel synthesis within the bounded
screen recorded in #21769. The inspected survey, automorphism papers and
repository results supply no prior settlement of this precise assertion.
No publication-priority claim is made.

## ASSUMED-UNVERIFIED

Literature completeness remains ASSUMED-UNVERIFIED. The preregistration's
OpenAlex and Semantic Scholar citation-list requests returned HTTP 429;
a bounded full-text screen cannot certify absence of prior work.
Classification of all equality algebras and extension to other fields
remain open, independently of the proved complex maximum.
