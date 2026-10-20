---
slug: gallardo-rahavandrainy-2023-binary-collatz-3-11
bibkey: gallardo2023binarycollatz
doi: 10.48550/arXiv.2308.01181
url: https://arxiv.org/abs/2308.01181v2
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.result
---

# Gallardo–Rahavandrainy Conjecture 3.11

## Problem

Gallardo and Rahavandrainy, *On Collatz Conjecture for binary polynomials*,
arXiv:2308.01181v2, Conjecture 3.11, p. 15, state:
“If $A=(M^2+M+1)^n$ with $n\ge2$, then $\ell_A$ equals $n+1$.”
Here $M=x^2+x+1$ in $\mathbb F_2[x]$. The source calls a polynomial odd when
it is coprime to $x(x+1)$, removes all powers of these two linear factors to
obtain its odd part, and iterates the odd part of $1+MA$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Binary polynomials and $M=x^2+x+1$ | `Polynomial (ZMod 2)` and `M` | Literal coefficient ring and polynomial. |
| Remove $x^{val_x(S)}(x+1)^{val_{x+1}(S)}$ | `oddPart` | `rootMultiplicity` at 0 and 1; `X-C 1=X+1` in characteristic two. |
| The odd subsequence $A_1,A_3,\ldots$ | `oddSeq A k` | Source index $2k+1$; its initial term is the odd part of $A$. |
| Length counts the initial odd term and terminal 1 | `collatzLength` | First hitting index of 1, plus one. |
| Every natural $n\ge2$ | `claim` | The quantified natural exponent has hypothesis $2\le n$. |
| $\ell_{(M^2+M+1)^n}=n+1$ | `result : claim` | Proved, with no extra hypothesis. |

The total definition of `oddPart` also accepts zero. The proof only transports
nonzero polynomials with the required oddness; this total extension does not
weaken or change the stated conjecture.

## Motivation

The source proves the power-of-two case in Lemma 3.3 and gives examples for
$n=9,\ldots,16$. The exact formula for every $n\ge2$ is a tier-1, externally
named conjecture, preregistered in [#19299](https://github.com/the-omega-institute/trureturing/issues/19299).
The settling declaration is `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.result`.

## Gap

The binding conjecture is proved. Completeness of the literature screen is
`ASSUMED-UNVERIFIED`; no complete classification of binary-polynomial Collatz
lengths, or sharper general bound, is asserted.

## Route

Put $m=1+y$ and $q=1+y+y^2$. Composition with $x(x+1)$ sends $m$ to the
source's $M$ and $q$ to $M^2+M+1$. Polynomial reversal conjugates the resulting
odd-part process to $R(f)=mf+y^{\deg f+1}$. A degree-gap reduction establishes
termination and reduces its first hitting time $h$.

The consumed private declarations `Dynamics.square_doubling` and
`Dynamics.q_square_doubling` prove, for every $f$ with $f(0)=1$,
$h(f^2)=2h(f)$ and $h(qf^2)=2h(f)+1$.
`Dynamics.q_power_height` uses the even and odd cases of the exponent to prove
$h(q^n)=n$. `Dynamics.q_power_hitting_set` identifies the exact hitting sets
under transport, and `Dynamics.length_q_power` proves the source length
$n+1$ for every natural $n$. These declarations are private helpers of the
settling module; the public theorem is `result`.

## Falsifier

A natural $n\ge2$ for which the source process first reaches 1 at a step
other than $n$, or fails to reach it, contradicts `claim`. Failure of the
composition or reversal correspondences would invalidate this route; their
exact identities are proved in the settling module.

## Evidence

The Lean source is `D5/S1/Recurrence/GallardoRahavandrainyBinaryCollatz.lean`,
with its Blueprint Scribe and generated mathematical exposition at the
corresponding paths. Its axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/85b4f93ce636b52cc1f4e4cc18e2dfe763d70fcb/docs/reports/gallardo-rahavandrainy-2023-binary-collatz-3-11).
Command: `python3 docs/reports/gallardo-rahavandrainy-2023-binary-collatz-3-11/check.py`
in that experiments checkout; exit 0, `RESULT PASS`.
Script SHA-256: `86f968206e76be2c8db4d0ce65d68113ff1e64d43beee8bf64c8240fab8b6e12`.
It checks the source lengths for $n=2,\ldots,80$, both doubling identities
for all 1024 odd polynomials of degree at most 10, and $h(q^n)=n$ for
$n=0,\ldots,199$. Its displayed source degree sequences cover
$n=2,\ldots,12$, including $n=9$ with
$[36,32,32,32,32,32,30,30,4,0]$ and length 10.
These finite checks corroborate the proof and do not establish its universal scope.

The escape audit of the sole public theorem `result` is unfinished:
[#19534](https://github.com/the-omega-institute/trureturing/issues/19534).
No validated four-slot registration is asserted.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Binding conjecture | Proved; kernel-checked | Public `result` proves `claim`, for every $n\ge2$. |
| Finite corroboration | Computed | The pinned experiment and command above exit 0 with `RESULT PASS`, on exactly the stated finite ranges. |
| Mechanism: composition and reversal | Proved; kernel-checked | Consumed `Dynamics.transport`, `Dynamics.reversal_conjugacy`, and `Dynamics.q_power_hitting_set` identify the two processes and their hitting sets. |
| Squaring and $q$ times a square | Proved; kernel-checked | Consumed `Dynamics.square_doubling` and `Dynamics.q_square_doubling` apply to every polynomial $f$ with $f(0)=1$. |
| Binary induction | Proved; kernel-checked | Consumed `Dynamics.q_power_height` gives $h(q^n)=n$ for all natural $n$. |
| Stronger length formula, including $n=0,1$ | Proved; kernel-checked | Consumed `Dynamics.length_q_power` states the same length formula for all natural $n$. |
| Nested squaring/$q$ construction | Proved in prose | Starting at $f_0=1$, set $f_{j+1}=q^{\varepsilon_j}f_j^2$ with $\varepsilon_j\in\{0,1\}$. The two identities give $h(f_{j+1})=2h(f_j)+\varepsilon_j$, hence $h(f_k)=\sum_{j<k}2^{k-1-j}\varepsilon_j$. Each $f_j(0)=1$ by multiplication. The height identities supply this consequence; it is not an additional public Lean theorem. |
| Source results depending on Conjecture 3.11 | Open; literature reading | The cited conjecture is settled with the source's conventions; no exhaustive dependency audit of the paper's other results is asserted. Lemma 3.3 is the power-of-two subfamily. |
| General bound and sharpening of Theorem 1.2 | Open | No new general bound or sharpening beyond the exact family is claimed. |
| Literature status | Open; literature reading | The screen below is partial; completeness is `ASSUMED-UNVERIFIED`. |
| Production escape audit | Open | The exact natural-indexed theorem has no validated four-slot registration; issue #19534 states the missing evidence. |

### Literature scope

The screen recorded in #19299 includes source versions v1 and v2 (v2 retains
Conjecture 3.11), the same authors' arXiv:2510.07530 and works
2602.13111, 2412.17850, 2406.10748, 2509.00619 and 2606.08640.
It includes Alon–Behajaina–Paran arXiv:2401.03210 (the cited family covers
power-of-two exponents), Behajaina–Paran arXiv:2312.00390,
Matthews–Leigh, Snapp–Tracy, Nichols arXiv:1610.02545 and Lagarias's bibliography.
These are preregistration-reported literature readings, not Lean dependencies.
The source and the searches in that issue establish the named target and the
searched scope; they do not establish exhaustive absence of prior art.

## ASSUMED-UNVERIFIED

Literature completeness remains `ASSUMED-UNVERIFIED`, including the full text
of Hicks–Mullen–Yucas–Zavislak and detailed Nichols proof passages.
The escape audit remains unfinished under #19534.
