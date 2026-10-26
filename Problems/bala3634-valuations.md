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

Issue #18633 preregisters the A363411 valuation question and the shared
conventions; the sibling statements are covered by the same source family.
The literature screen recorded in that issue and the OEIS entries found no
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

The settling declaration is frozen at
Golden/Frozen/state/D5/S3/Arith/Congruence/BalaA363411.lean.json with module
statement sha256:714b0a8a6090b1809800bcfb6ef36eedfcfca248d8cd1831dd663fec245bad06.
The public settling result is
D5.S3.Arith.Congruence.BalaA363411.result. The axiom closure of every public
declaration is contained in {propext, Classical.choice, Quot.sound}. No sorry
or new axiom is used.

The numerical experiment is in the-omega-institute/trureturing-experiments at
commit f06c1e206be09aec0c8733382cae1a6219690f92 under
docs/reports/oeis-a363411-a363412-bala-sqrt-minus-three-products/. The command
python3 check.py 3000 300 exits 0 with RESULT PASS. check.py has SHA-256
88fcd4332f9c0f65e7ebd18a256f8cde079f8713bf85f142845a9f627d18b992. Its scope
is exactly the published data, the elementary-symmetric divisibility check
through $L=300$, the exact integer checks through $N=3000$, inert odd primes
from $5$ through $101$, and the four target statements.

The p=2 block check is a separate exact Lean scratch computation:
bash /Users/auric/trureturing/tools/scripts/agent/lean-exclusive.sh lake env
lean .lake/scratch/inert_two_check.lean exits 0; the scratch file SHA-256 is
1a7a9f494b91a5f26264ab328a3bc3b7fc2acd07d264904439fa8d49f71e306a. It proves
$\operatorname{seq}_{\mathbb Z/2}(2)=(1,1)$.

## Triage

| Item | Status | Evidence |
| --- | --- | --- |
| The scalar-two inert-block hint needs an odd-prime restriction; the p=2 block is $(1,1)$ modulo 2, while the type-one proof handles 2 with a finite witness. | computed | Exact Lean scratch computation above, exit 0, SHA-256 recorded; BalaA363411TypeOne.result handles the type-one conclusion. |
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
