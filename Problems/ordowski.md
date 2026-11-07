---
slug: ordowski
bibkey: ordowski2024a369378
doi: null
url: https://oeis.org/A369378
triage: theorem
motivation_gids:
  - D5/S3/Arith/Primes/OeisA369378FermatCovering.result
---

## Problem

T. Ordowski's [OEIS A369378](https://oeis.org/A369378), COMMENTS (unpaginated), states: "Conjecture: if n > 0, then 2^(2^n+1)-1 + 2^k is not prime for every k < 2^n." The NAME is "a(n) is the smallest k such that 2^(2^n+1)-1 + 2^k is prime, or -1 if no such k exists." The source is revision 40, as recorded in [preregistration #18631](https://github.com/the-omega-institute/trureturing/issues/18631). The [Library note](../Library/ArithUnits/ordowski2024a369378.md) cites the OEIS entry; no DOI or arXiv identifier is supplied by that source.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every $n>0$ | Natural binder `n` and hypothesis `0 < n` in `claim` | Strict positivity is preserved. |
| Every $k<2^n$ | Natural binder `k` and strict bound in `claim` | Includes $k=0$. |
| $2^{2^n+1}-1+2^k$ | The literal expression in `claim` | Natural subtraction agrees with integer subtraction because the subtracted power is at least one. |
| Is not prime | Negation of `Nat.Prime` in `claim` | No auxiliary certificate replaces the source predicate. |
| Entire conjecture | `result : claim` | No additional hypothesis or dropped clause. |

## Motivation

A divisor chosen from the power of two dividing the exponent excludes every prime candidate below the source's proposed lower bound. No primality assumption on Fermat numbers is required.

## Gap

The source and literature checks recorded by the Claude Code orchestrator in #18631 read the OEIS entry in its mirror and on oeis.org. The searched scope comprises the Epoch OEIS Open benchmark list and results, `google-deepmind/alphaproof-nexus-results`, `google-deepmind/formal-conjectures`, the repository's screened-out collections and its development branch. No proof was found within that scope. The probe additionally reports no matching settlement in its recorded Zenodo and GitHub Lean searches. These are attributed search readings, not an exhaustive literature theorem. Completeness is ASSUMED-UNVERIFIED.

## Route

Write $N=2^{2^n+1}-1+2^k$. If $k=0$, then $N=2^{2^n+1}$, with proper divisor two.

For positive $k$, write $k=2^j m$ with $m$ odd. The bound $k<2^n$ gives $j<n$. Let $F_j=2^{2^j}+1$. Modulo $F_j$, one has $2^{2^j}=-1$, and therefore $2^{2^{j+1}}=1$. Since $j+1\le n$, it follows that $2^{2^n}=1$. Oddness of $m$ gives $2^k=-1$. Thus $N$ is congruent to $2-1-1=0$ modulo $F_j$. Finally $2\le F_j<N$, since $2^j<2^n+1$ and $2^k\ge2$. The proper divisor proves nonprimality.

## Falsifier

A natural $n>0$ and $k<2^n$ for which $N$ is prime would refute the claim. Agreement on finitely many exponents alone cannot establish the universally quantified conclusion.

## Evidence

The kernel-checked declaration `D5.S3.Arith.Primes.OeisA369378FermatCovering.result` proves the literal `claim`. The module's anonymous fidelity example checks the primes 11 and 47 at $(n,k)=(1,2)$ and $(2,4)$. Generality is G and utility is none: the delivered result is a universal arithmetic theorem; the convention's anonymous fidelity check supplies no separate numerical-certificate API. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The settlement uses deposit-uncovered with no atom. Its Scribe displays the complete claim and attaches exactly one Proved resolution to `result`. The proof is classified bind-only, with no escape witness; admission is `open-problem-resolution (#18631; Proved)`.

The experiment is [the directory pinned to f06c1e206be09aec0c8733382cae1a6219690f92](https://github.com/the-omega-institute/trureturing-experiments/tree/f06c1e206be09aec0c8733382cae1a6219690f92/docs/reports/oeis-a369378-fermat-number-covering). Command: `python3 /tmp/op-ordowski/check-immutable.py 12 --full`, using exactly the pinned `check.py` bytes; exit 0. Script SHA-256: `a0c02c9d93982b58ce437e7b33e1a63f9292befb906800e9b834cb9e06d8edc6`. It checks the covering for every $1\le n\le12$ and every $k<2^n$, recomputes $a(1),\ldots,a(6)=2,4,16,1968,64,64$, and verifies the boundary primes for $n=1,2$. These finite results do not establish existence of $a(n)$ for $n>6$.

Escape audit unfinished: [#26202](https://github.com/the-omega-institute/trureturing/issues/26202), covering `D5.S3.Arith.Primes.OeisA369378FermatCovering.result`. No lawful enrolled-template application with the required source-reconstruction, realization-bridge and E1–E8 evidence is supplied. No Reg source or declared_validated registration is claimed.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and scope |
| --- | --- | --- |
| Ordowski's conjecture | proved; kernel-checked `D5.S3.Arith.Primes.OeisA369378FermatCovering.result` | Every natural $n>0$ and $k<2^n$ gives a nonprime number. |
| Sharpness at $n=1,2$ | proved; kernel-checked anonymous fidelity example in the settling module | $k=2^n$ gives primes 11 and 47 respectively. Together with `result`, this gives $a(1)=2$ and $a(2)=4$. |
| Published terms and other listed boundary cases | computed; experiment in Evidence, same command, exit 0 and SHA-256 | $a(1),\ldots,a(6)=2,4,16,1968,64,64$. Equality $a(n)=2^n$ holds at $n=6$ and fails at $n=3,4,5$. No untested index is included. |
| Finite covering check | computed; experiment in Evidence, same command, exit 0 and SHA-256 | Every $1\le n\le12$ and $k<2^n$; all checks pass. |
| Decisive mechanism and extent | proved in prose; Route and the derivation below | The odd part of $k$ selects a proper Fermat divisor. Fermat numbers need not be prime. The same congruences exclude every positive $k$ with $v_2(k)<n$. |
| Existence of $a(n)$ for $n>6$ | open | Neither the universal lower bound nor the finite computation establishes a prime-producing exponent for these indices. |
| Dual-Sierpinski conditional remarks | open | The source's conditional remarks about nonexistence are not resolved. |
| Global publication priority | open; literature reading | No priority claim is made; literature completeness is ASSUMED-UNVERIFIED. |
| Single-module settlement | proved; kernel-checked `result` | The sole settling theorem proves the preregistered conjecture. Its proof-shape classification is bind-only; no separate general module or escape witness is claimed. |

For the stated prose extension, take $n>0$, $k>0$ and $j=v_2(k)<n$. The congruences in Route depend on $j<n$ and the odd quotient, rather than the upper bound on $k$. Also $2^k\ge2$ still gives $N>F_j$. Thus every prime-producing exponent must be a positive multiple of $2^n$; if $a(n)$ exists, it has this divisibility. This extension is a prose derivation, not an additional Lean theorem. The source's dual-Sierpinski remarks remain conditional: a lower bound or divisibility restriction supplies no nonexistence result. No other conditional source result is claimed as settled.

## ASSUMED-UNVERIFIED

Literature-search completeness and publication priority are ASSUMED-UNVERIFIED. Source and literature checks are attributed to #18631 and the probe envelope. The unresolved escape audit is tracked in #26202; kernel verification and frozen membership do not complete that audit.
