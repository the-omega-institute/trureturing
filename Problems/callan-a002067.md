---
slug: callan-a002067
bibkey: callan2017a002067
doi: null
url: https://oeis.org/A002067
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian
---

# Callan's two A002067 conjectures

## Problem

David Callan's two unnumbered COMMENTS headed “Conjectures” in OEIS A002067 state that the sequence with name

> a(n) = Sum_{k=0..n-1} binomial(2*n,2*k)*a(k)*a(n-k-1)

is both the hafnian of the triangular array with $u(i,j)=i$ for $1\le i<j\le 2n$ and the total weight of Dyck $n$-paths, where each upstep contributes its one-based position times the height of its upper endpoint. Empty products are one and the assertions include $n=0$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The recurrence and initial value | `D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck.IsSourceSequence` | Exact shifted form with $a(0)=1$ and $k<n+1$. |
| Every nonnegative index | `n : ℕ` in `claim` and `result` | Includes the empty case. |
| Hafnian of the constant-row triangular array | `hafnian n` | Complete-graph perfect matchings, with each edge weighted by its smaller one-based endpoint. |
| Weighted Dyck paths | `weightedDyckSum n` | Mathlib Dyck words and the position/upper-height product. The agreed `pathWeight` filter is `fun j => p.toList.getD j DyckStep.D = DyckStep.U` rather than the literal `p.toList[j]? = some DyckStep.U`; the predicates agree at every `j`, as proved by `D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck.getD_up_iff` (private; `CallanA002067Dyck.lean:59`). See the [binding convention](https://github.com/the-omega-institute/trureturing/issues/23975#issuecomment-6558192984). |
| Existence and every recurrence solution | `claim` | The existential conjunct and the universal implication are both present. |
| Both equalities | `result : claim` | Kernel-checked conjunction for every `n`. |

## Motivation

Issue [#23975](https://github.com/the-omega-institute/trureturing/issues/23975) preregistered this external OEIS problem. The settling module carries `admission_basis: open-problem-resolution (#23975; Proved)` and `utility: none`.

## Gap

The source proposed the two identifications without an unbounded proof. Callan's 2009 survey supplies the constant-row hafnian and Dyck-path correspondence, while Dominici's 2006 paper supplies the derivative-polynomial recurrence. The remaining bridge is the uniform Lean proof connecting the recurrence, matching involutions and weighted returning paths.

## Route

The proof encodes perfect matchings as fixed-point-free involutions and extends an involution by either adding a fixed point or joining the new endpoint to an existing fixed point. The resulting polynomial satisfies derivative plus $(r+1)X$ multiplication. Its constant term at even length counts perfect matchings and returning weighted paths. The crossing factorial invariant equates the products of downstep starting heights and upstep upper heights, and the even constant terms satisfy the source convolution. Strong induction gives uniqueness of the source recurrence.

## Falsifier

A natural index, a recurrence solution, or a perfect matching or Dyck path whose computed weight violates `result` would falsify the formal claim. A statement restricted to noncrossing matchings, a finite numerical check, or a different recurrence is outside this result.

## Evidence

The kernel-checked settling theorem is `D5.S3.Combinatorics.PerfectMatchings.CallanA002067Hafnian.result : claim`. The public definitions are `hafnian` and `claim`; the Dyck definitions and auxiliary theorems are in `D5.S3.Combinatorics.PerfectMatchings.CallanA002067Dyck`. The Hafnian module state record is `Golden/Frozen/state/D5/S3/Combinatorics/PerfectMatchings/CallanA002067Hafnian.lean.json` with module statement id `sha256:59da44a2aa33e2ee46ae0abc8a4ba3eea9dd41eb0cb6b71080570e84dc263eb4`.

The escape audit for the public theorem remains unfinished under [#24743](https://github.com/the-omega-institute/trureturing/issues/24743). No `declared_validated` registration is asserted; the missing evidence is a faithful four-slot source reconstruction, realization bridge, whole-family variation and sensitivity, and actual observational dependence.

The finite checker is in [the-omega-institute/trureturing-experiments, pinned directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ede6b6892ce521e56d35b28caade853ebcbb0e3a/docs/reports/callan-a002067). The command is `python3 docs/reports/callan-a002067/check.py`; it exited 0 with final line `ALL_CHECKS_OK`. Script SHA-256: `cc9adc528f7985a0a37d2ca2602b4b00ef6177cf961e90f6f15d4bc5081f63b1`. It reproduces source terms through $n=10$, checks all matchings through $n=6$, checks all walks through length 12, and verifies the example weight $480$.

## Triage

### What the settlement shows

- **Proved — both original assertions hold for every $n$, including the empty cases.** Evidence: kernel-checked `result` and its full claim proposition.
- **Proved — polynomial coefficients enumerate weighted partial involutions for every length; evaluation at zero selects perfect matchings.** Evidence: the involution recurrence and constant-term argument on the live proof path of `result`.
- **Proved — the word formula is valid for every U/D word, with a zero polynomial whenever a prefix is negative.** Evidence: the word-polynomial induction and returning-word lemmas in the Dyck module, used by `source_eq_dyck`.
- **Proved — the factorial crossing invariant establishes equality of upstep upper-height and downstep starting-height products for returning nonnegative unit-step paths.** Evidence: `crossing_factorial`, `crossing_products` and `dyck_height_products` in the Dyck module.
- **Computed — the checker reproduces source terms through $n=10$ and verifies the example weight $480$.** Evidence: `python3 docs/reports/callan-a002067/check.py`, exit 0, script SHA-256 `cc9adc528f7985a0a37d2ca2602b4b00ef6177cf961e90f6f15d4bc5081f63b1`; scope is exactly $n=0,ldots,10$ for terms and the stated path example.
- **Open — no Lean formalization of the analytic inverse-error-function interpretation or the formal ODE is included.** The source recurrence is proved directly by derivative convolution and Pascal; no theorem about the analytic interpretation is claimed.
- **Open — the arbitrary-row-weight extension from Callan 2009 is prior art and is not formalized here.** The current involution and walk recursion uses opener weight $j+1$ only.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The source OEIS entry, Callan's arXiv:0906.1317v1 survey, Dominici's arXiv:math/0607230v2 paper, and the bounded searches recorded in #23975 were inspected, but rate limits, inaccessible full text and unread citation records leave the screen incomplete. No originality or worldwide-priority claim follows.
