---
slug: bala3634-valuations
bibkey: bala2023sqrtminusthree
doi: null
url: https://oeis.org/A363411
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/BalaA363411.result
---

# Bala's OEIS A363411 and A363412 valuation conjectures

## Problem

P. Bala's OEIS A363411 asks whether the real coordinate of
$$P_n=\prod_{k=0}^{n}(1+k\sqrt{-3})$$
satisfies $v_5(a(n+2))=A079998(n)$, where $a(n)=\operatorname{Re}(P_n)$ and
A079998 is the characteristic function of the multiples of five. The companion
A363411 type-one statement lists the primes at most $101$ that divide no real
term. The companion A363412 statements concern
$b(n)=\operatorname{Im}(P_n)/\sqrt3$: $3\nmid b(3n+1)$ and
$v_3(b(3n))=v_3(b(3n-1))$ for $n\ge1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $P_n=\prod_{k=0}^{n}(1+k\sqrt{-3})$ in $\mathbb Z[\sqrt{-3}]$ | D5.S3.Arith.Congruence.BalaA363411.P | Literal finite product over Finset.range (n + 1) |
| A363411 real coordinate | BalaA363411.a | Zsqrtd.re of P |
| A363412 imaginary coordinate divided by $\sqrt3$ | BalaA363411.b | Zsqrtd.im coordinate |
| $v_5(a(n+2))=1$ when $5\mid n$, and $0$ otherwise | BalaA363411.claim and result | Exact all-$n$ quantifier |
| Type-one primes through $101$ | BalaA363411TypeOne.claim and result | Exact finite prime bound and all-term quantifier |
| $3\nmid b(3n+1)$ | BalaA363412.claim and result | Exact all-$n$ quantifier |
| $v_3(b(3n))=v_3(b(3n-1))$ for $n\ge1$ | BalaA363412Valuation.claim and result | Exact positive-index condition |

## Motivation

These four statements are explicit OEIS conjectures. The settling result
converts the five-adic assertion into a period calculation modulo $25$; the
other three results record adjoining prime-type and three-adic consequences for
the same quadratic product. The literature source is OEIS A363411 revision 18,
A363412 revision 19 and A079998. Literature completeness is
ASSUMED-UNVERIFIED.

## Gap

The four preregistrations map to these exact settling declarations:

| Preregistration | Settling declaration | Settlement |
| --- | --- | --- |
| #18633 | D5.S3.Arith.Congruence.BalaA363411.result | Proved |
| #18634 | D5.S3.Arith.Congruence.BalaA363411TypeOne.result | Proved |
| #18635 | D5.S3.Arith.Congruence.BalaA363412.result | Proved |
| #18636 | D5.S3.Arith.Congruence.BalaA363412Valuation.result | Proved |

The literature screens recorded in those issues and the OEIS entries found no
prior proof of these four exact statements in the searched scope. No
exhaustive priority claim is made. The unfinished escape registrations are
tracked in issue #21978.

## Route

The module D5/S3/Arith/Congruence/BalaA363411.lean defines the product and its
two coordinates, then proves the coordinate recurrence in every commutative
ring. A scalar block gives the period identity; finite residue certificates
modulo $5$ and $25$ show that the real coordinate is divisible by $5$ exactly
in residue class $2$ modulo $5$ and never by $25$. The settling theorem applies
these facts at index $n+2$. The type-one theorem extends finite residue checks
with strong induction. The companion module proves the reflection congruence by
finite-set induction, and the valuation module factors both reflected
identities through the same three-adic valuation.

## Falsifier

A counterexample would be an index violating the five-adic equality, a prime at
most $101$ violating the exact type-one classification, an index with
$3\mid b(3n+1)$, or a positive index at which the two three-adic valuations
differ. The finite residue certificates and the kernel-checked result
declarations rule out each of these within the stated quantifiers.

## Evidence

The primary settling result is D5.S3.Arith.Congruence.BalaA363411.result;
the three sibling results are mapped explicitly in the table above. The axiom closure of every public
declaration is contained in {propext, Classical.choice, Quot.sound}. No sorry
or new axiom is used.

The numerical experiment is in [the pinned experiments directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f06c1e206be09aec0c8733382cae1a6219690f92/docs/reports/oeis-a363411-a363412-bala-sqrt-minus-three-products). The command
`python3 /tmp/op-bala3634/check.py 3000 300` exits 0 with RESULT PASS. check.py has SHA-256
88fcd4332f9c0f65e7ebd18a256f8cde079f8713bf85f142845a9f627d18b992. Its scope
is exactly the published data, the elementary-symmetric divisibility check
through $L=300$, the exact integer checks through $N=3000$, inert odd primes
from $5$ through $101$, and the four target statements within those finite ranges.
The five-adic formula is tested for $0\le n\le2998$, three-adic
nondivisibility for $0\le n\le999$, and the paired valuations for
$1\le n\le1000$. The numerical type-one check uses primes at most $101$
and sequence indices at most $3000$; the unbounded term-index conclusion
comes from `BalaA363411TypeOne.result`.

For $p=2$, the finite block follows directly in prose. In
$\mathbb Z[\sqrt{-3}]/2$, the factors at $k=0$ and $k=2$ are both $1$,
and the factor at $k=1$ is $1+\sqrt{-3}$. Their product has coordinate
pair $(1,1)$, whereas the scalar $2$ has coordinate pair $(0,0)$.
Thus the scalar-two assertion cannot include $p=2$.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| The scalar-two inert-block hint needs an odd-prime restriction; the $p=2$ block is $(1,1)$ modulo 2, while the type-one proof handles 2 with a finite witness. | computed | The explicit three-factor calculation above establishes the finite $p=2$ block; the type-one conclusion is separately kernel-checked by `BalaA363411TypeOne.result`. No standalone Lean declaration is claimed for this prose calculation. |
| The 5-adic valuation is exactly one in indices congruent to two modulo five and zero otherwise. | proved | Kernel-checked BalaA363411.real_mod_five, real_not_dvd_twentyfive and result. |
| The twelve listed primes, and only those primes up to 101, divide no real term; the conclusion quantifies over all term indices. | proved | Kernel-checked BalaA363411TypeOne.result, with nonzero_of_block and finite certificates on its proof path. |
| The coefficient recurrence admits scalar monodromy over every commutative ring when the coefficient block closes to a scalar. | proved | Kernel-checked BalaA363411.seq_shift and seq_period. |
| For every finite coefficient family, shifting all coefficients by $c$ changes the real part by a multiple of $3c$ and the imaginary part by $c$ times the family size modulo $3c$. | proved | Kernel-checked BalaA363412.uniform_shift. |
| The two reflection congruences hold for every natural $m$; for $n\ge1$, both requested imaginary valuations equal $v_3(3n)$. | proved | Kernel-checked BalaA363412.reflection_congruences, BalaA363412Valuation.at_multiple and before_multiple. |
| The exact-integer checker passes through $N=3000$ and odd-symmetric-sum checks through $L=300$. | computed | The pinned experiment command above, exit 0, script SHA-256 recorded; no larger range is asserted. |
| No general theorem about all inert primes, a full type-three classification, or asymptotic split-prime valuations is claimed. | open | Boundary of the four declarations and the experiment scope. |
| The odd elementary-symmetric divisibility lemma and the complete general-d triangular valuation formula were not separately formalized. | open | They are unnecessary for the four checked results and have no delivered declaration. |

### What the settlement shows

Proved: the period-up-to-a-unit mechanism modulo $25$ gives the exact
five-adic formula for every natural index. The finite residue certificates are
sufficient for the unbounded statement, and the same recurrence supplies the
listed type-one and three-adic consequences.

Computed: the exact checker corroborates the finite ranges stated in the
experiment entry. Its finite range does not extend the quantified Lean results.

Open: a general inert-prime classification, a complete type-three
classification, asymptotic split-prime valuations, the odd elementary-
symmetric divisibility lemma, and the general-d triangular valuation formula
remain outside the settlement.

## ASSUMED-UNVERIFIED

Literature completeness and priority are ASSUMED-UNVERIFIED. The experiment is
finite and does not establish any uniform statement beyond the Lean
declarations. Escape registration for the public declarations listed in issue
#21978 remains unfinished; no declared_validated status is asserted.
