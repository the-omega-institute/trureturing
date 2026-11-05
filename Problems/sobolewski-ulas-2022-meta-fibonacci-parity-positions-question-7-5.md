---
slug: sobolewski-ulas-2022-meta-fibonacci-parity-positions-question-7-5
bibkey: sobolewskiulas2022metafibonacci
doi: 10.4064/aa220613-19-1
url: https://arxiv.org/abs/2204.04011v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/MetaFibonacci/SobolewskiUlasParityPositions.result
---

# Parity-position sequences in the Sobolewski–Ulas recurrence

## Problem

Bartosz Sobolewski and Maciej Ulas, *Solutions of certain meta-Fibonacci
recurrences*, arXiv:2204.04011v1, Question 7.5, pp. 16–17; journal locator:
Acta Arithmetica 209 (2023), 269–289, DOI 10.4064/aa220613-19-1.

> Let u_i = (u_i(n)) for i = 0, 1 be the increasing sequence of
> nonnegative integers such that r(u_i(n)) = i. Is the sequence u_i is
> k-regular for some k?

Here $h(n)=1$ for $n\leq1$, $h(n)=h(n-h(n-1))+h(n-2)$ for $n>1$,
and $r(n)=h(n)\bmod2$. Section 2 requires $k\geq2$ and defines regularity
as finite generation of the integer span of the $k$-kernel.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| The recurrence $h=h_{1,1}$ | `h` | Both initial values are one. Truncated negative arguments map to zero, also of value one. The termination minimum is inactive. |
| $r(n)=h(n)\bmod2$ | `r` | Natural remainder, values zero and one. |
| Increasing nonnegative occurrence positions | `u` | `Nat.nth`, with zero-based index. Block balance proves both sets infinite. |
| Kernel indices $j\geq0$, $0\leq a<k^j$ | `kKernel` | Literal arbitrary-base subsequences. Binary proofs reuse `twoKernel` from `SparseKernelRank`. |
| Finite generation over $\mathbb Z$ | `IsKRegular` | `Submodule.span` and `Submodule.FG` over integer-valued sequences. |
| Each $i=0,1$, some $k\geq2$ | `claim`, `result` | Full parity family without extra hypotheses; the proof supplies $k=2$. |

All unqualified declaration names below belong to
`D5.S1.Recurrence.MetaFibonacci.SobolewskiUlasParityPositions`.
The six public definitions reproduce the source conventions. The binary
specialization of `kKernel` agrees definitionally with the imported
`D5.S1.Words.Palindromes.PeriodDoubling.twoKernel`.

## Motivation

The settling GID is
`D5/S1/Recurrence/MetaFibonacci/SobolewskiUlasParityPositions.result`.
It answers the externally named question in preregistration #19659 with
`admission_basis: open-problem-resolution (#19659; Proved)`.
There is no digestion atom or coverage claim.

## Gap

The source reports numerical evidence for base two. The missing argument
is an unbounded proof that the occurrence enumerations have finitely
generated binary-kernel spans. Finite samples and stabilized numerical
ranks alone do not establish that conclusion.

The escape audit of the sole public theorem `result` is unfinished:
https://github.com/the-omega-institute/trureturing/issues/21489.
The existential finite-generation conclusion has no compiled faithful
four-slot realization/readout and sensitivity evidence in this delivery.
No `declared_validated` registration is claimed.

## Route

The odd and even recurrence identities give the parity table of each
aligned sixteen-position block. Every such block contains exactly eight
zeros and eight ones. Consequently
$u_i(8q+j)=16q+F_i(r(16q),q\bmod4,j)$ for $0\leq j<8$.

The state $((r(16\lfloor n/8\rfloor),\lfloor n/8\rfloor\bmod4),n\bmod8)$
has $2\cdot4\cdot8=64$ possible values and closes under doubling and
adding a binary digit. The correction $D_i(n)=u_i(n)-2n$ is an output
of this state. Its binary kernel is finite. Every binary-kernel sequence
of $u_i$ lies in the integer span of the correction kernel, the constant
one sequence, and $n\mapsto n$. The proof uses `Submodule.fg_span` and
`Submodule.FG.of_le` to obtain finite generation.

## Falsifier

A parity class without eight occurrences in an aligned sixteen-block
would invalidate the balance lemma. A failed transition under either
binary digit would invalidate the finite-state construction. The Lean
proof establishes both for every natural index. This does not establish
an analogous statement for other recurrence parameters or moduli.

## Evidence

`result` is the kernel-checked public settlement. Private declarations
`block_balance`, `nth_block_selection`, `correction_representation`,
`V_step`, `finite_kernel_of_state` and `finite_correction_kernel` carry
the balance, selection and finite-kernel arguments used by `result`.
The axiom closure of every public declaration is contained in
{`propext`, `Classical.choice`, `Quot.sound`}.

### Independent computation

The experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/a46c16d6036bbca4c463fc397453aa5bf45fa8e9/docs/reports/sobolewski-ulas-2022-meta-fibonacci-parity-positions-question-7-5).
Command: `git -C /Users/auric/trureturing-experiments show a46c16d6036bbca4c463fc397453aa5bf45fa8e9:docs/reports/sobolewski-ulas-2022-meta-fibonacci-parity-positions-question-7-5/check.py | python3 -`.
Exit code: 0. Script SHA-256:
`0c79162256218d2b5bdf452f56b647c147646f8741f86c632342bc7a0f08e68f`.

Exact-integer checks use the first $N=2^{18}$ recurrence values.
Theorem 3.1 is checked for $0\leq n<N/2-1$. Theorem 3.9 relations use
$0\leq n<N/8$, $N/16$ or $N/32$, according to their largest argument.
All $N/16$ aligned blocks have eight ones and are determined by the
stated two coordinates. The occurrence-selection formula is checked
for both parities, $0\leq q<N/16-1$ and $0\leq j<8$.
All these checks return true. The six floating-point kernel-matrix ranks
are 12: both parities, depths 6, 7 and 8, each restricted to 200 terms.
These ranks are numerical observations, not an exact or unbounded rank
proof. The computation is auxiliary to the Lean proof.

## Triage

### What the settlement shows

- **Proved, kernel-checked:** the externally named regularity question is
  answered by `result`; its proof chooses base two for both parities.
- **Proved, kernel-checked:** `block_balance` gives eight occurrences of
  each parity in every aligned sixteen-block. This is the decisive
  balance mechanism, with no finite-index cutoff.
- **Proved, kernel-checked:** `nth_block_selection` and
  `correction_representation` give $u_i(n)=2n+D_i(n)$ for $i<2$;
  `finite_correction_kernel` gives a finite binary kernel for $D_i$.
- **Proved in prose:** $D_i$ is bounded because it is the image of a
  finite 64-element state space under the integer output function `out`.
  Finite binary kernel is the automaticity criterion used here. Thus
  the bounded automatic correction is stronger structural information
  than regularity alone. No minimal-state or sharp-bound claim is made.
- **Computed:** the source's Theorems 3.1 and 3.9, aligned block balance,
  state-determined blocks and occurrence selection pass in exactly the
  finite ranges of the experiment entry. The finite kernel-matrix ranks
  are 12 at depths 6, 7 and 8 for both parities and 200 sampled terms.
- **Open:** exact integer kernel rank, its unbounded equality to 12,
  minimal automata, sharp correction bounds, and analogous results for
  other recurrence parameters or moduli are not settled here.
- **Literature reading:** the source's numerical prediction receives an
  unbounded mathematical proof for $h_{1,1}$ and its two parity classes.
  No other source question or parameter family is counted as settled.
  Journal-version agreement and completeness of the prior-art screen
  are `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The source reading is arXiv v1. The journal text has not been obtained,
so agreement of its Question 7.5 with v1 is unverified. The bounded
literature screen recorded in #19659 includes Campbell–Cloitre
arXiv:2602.23395, the authors' arXiv:2412.11319 and 2211.16622, and
Carpi–Maggi (2001); it is not an exhaustive citation or later-publication
screen. A previously unpublished or worldwide-priority resolution is
not established. Escape registration remains unfinished as linked above.
