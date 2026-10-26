---
slug: kimb341249-bound
bibkey: kimberling2021a341249
doi: null
url: https://oeis.org/A341249
triage: theorem
motivation_gids:
  - D5/S0/Certificates/KimberlingA341249BoundRefutation.result
---

# Kimberling's A341249 strict bound is false

## Problem

Clark Kimberling's OEIS A341249, NAME and COMMENTS, revision 10, states:

> a(n) = floor(r*floor(s*n)), where r = 2 + sqrt(2) and s = sqrt(2).

> Conjecture:  1 < r*s*n - a(n) < 2 for n >= 1.

This is the tier-1 external conjecture preregistered in
https://github.com/the-omega-institute/trureturing/issues/18673.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| r = 2 + sqrt(2) | r | Real constant $2+\sqrt 2$. |
| s = sqrt(2) | s | Real constant $\sqrt 2$. |
| a(n) = floor(r*floor(s*n)) | a | Natural index; both floors integer valued; products real. |
| for n >= 1 | claim | All natural $n$ satisfying $1\le n$. The formula-defined value at zero imposes no extra condition. |
| 1 < r*s*n - a(n) < 2 | claim | Conjunction of both strict inequalities, with integer values cast to real. |
| Refutation | result | Negation of that complete universal conjunction. |

The namespace is `D5.S0.Certificates.KimberlingA341249BoundRefutation`.

## Motivation

The settling GID is
`D5/S0/Certificates/KimberlingA341249BoundRefutation.result`.
The counterexample $n=2$ tests the literal formula and agrees with the entry's
second term. The delivery contains exactly the four definitions needed to state
this conjecture and its single refutation theorem.

## Gap

The source and literature screen in #18673 found no settlement in the OEIS
entries, the Epoch OEIS Open benchmark list and results, AlphaProof Nexus
results, formal-conjectures, S. Fried's OEIS-proof papers, or the repository's
screening records. This is a bounded literature reading; completeness is
`ASSUMED-UNVERIFIED`.

Pinned Mathlib supplies `Real.one_lt_sqrt_two`,
`Real.sqrt_two_lt_three_halves`, `Real.sq_sqrt`, and `Int.floor_eq_iff`.
These declarations are used by the settling proof. The new conclusion is the
refutation of the named external conjecture; no non-binding escape content is
claimed.

## Route

The following exact-value derivation is proved in prose. The same calculations
occur as local facts on `result`'s proof path, rather than as separate public
identity theorems.

From $1<\sqrt 2<3/2$, one has $2<2\sqrt 2<3$, so
$\lfloor 2\sqrt 2\rfloor=2$. Also $6<4+2\sqrt 2<7$, hence
$a(2)=\lfloor 4+2\sqrt 2\rfloor=6$. Using $(\sqrt 2)^2=2$ gives

$$r s\cdot 2-a(2)=(2+\sqrt 2)\sqrt 2\cdot2-6=4\sqrt 2-2>2.$$

The strict upper bound in the universal conjunction therefore fails at $n=2$.
The Lean theorem `result` proves the negation of that conjunction using the
Mathlib bounds, floor characterization, and arithmetic normalization.

## Falsifier

A discrepancy between the source's nested-floor convention and `a`, or an error
in the exact floor intervals or square-root identity, would invalidate the
proposed witness. The compiled refutation checks those conventions and
calculations within Lean's real-number model. Finite decimal experiments alone
do not certify universal corrected bounds.

## Evidence

The source is `D5/S0/Certificates/KimberlingA341249BoundRefutation.lean`;
its Blueprint Scribe renders all four definitions and the full negated
universal proposition. The module has no D5 imports. Its proof shape is
`bind-only`, with `escape_witness: none` and
`admission_basis: open-problem-resolution (#18673; Refuted)`.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Finite experiment

The independent program is [the pinned Kimberling experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/7f5a4efd2ec60be0409ae3c41ee383f488f47fd6/docs/reports/oeis-a341239-a341249-kimberling-nested-floor-bounds).
Its `check.py` has SHA-256
`bb1fd71470413099ad83772c10e9757dcb30660a95806daa178fd1106a792445`.
A byte-identical copy extracted with `git show` was executed by the implementation
seat as `python3 /Users/auric/.sshx/2cc6e57c053a8d81a6d12693/attempt-1/experiment-check.py 20000`,
exit 0. The program uses 80 decimal digits. It compares the supplied first
23 A341249 values and first 24 A341239 values; its bound and decomposition
checks range over all $1\le n\le20000$; decomposition comparisons use
absolute tolerance $10^{-60}$.

## Triage

| Item | Status and evidence | Exact scope |
| --- | --- | --- |
| The conjectured upper bound fails at $n=2$. | Proved: kernel-checked `D5.S0.Certificates.KimberlingA341249BoundRefutation.result`. The identities $a(2)=6$ and error $4\sqrt2-2>2$ have the prose derivation in Route and are live local calculations in this theorem. | Literal #18673 conventions. |
| First eight indices below 40 with error at least 2: $2,4,7,9,11,12,14,16$. | Computed: the pinned finite experiment, command, SHA-256 and exit 0 in Evidence. | Indices $1\le n<40$; no infinite-family theorem. |
| A341249 supplied data match; error lies in $(1,4)$ and equals $2f+c$. | Computed: the same experiment. | Data: first 23 terms; bounds and decomposition: $1\le n\le20000$, 80 digits. |
| A341239 supplied data match and $1<\mathrm{error}<3$. | Computed: the same experiment. | Data: first 24 terms; bounds: $1\le n\le20000$, 80 digits. No A341239 theorem is delivered. |
| Universal corrected A341249 bounds, the two-interval gap, fractional-part criterion, and infinite counterexample families. | Open: not formalized or certified by this delivery. | The issue's decomposition is a candidate route; finite readings do not settle a uniform claim. |

### What the settlement shows

The failure mechanism is the nested-floor error at $n=2$: it exceeds the
conjecture's strict upper endpoint. The lower inequality at this particular
index survives, by the exact-value derivation in Route. This is a prose
consequence, not a separate Lean theorem.

The nearest tested weaker A341249 bounds are $1<\mathrm{error}<4$ on the
finite range in Evidence. Their universal extension, the proposed exclusion of
$[1+\sqrt2,2+\sqrt2]$, the fractional-part condition for failure, and an
infinite family remain open in this delivery. The A341239 finite experiment
remains a separate computed result. Any argument assuming the literal universal
A341249 upper bound loses that premise; the retrieved revision-10 entry names no dependent theorem. No other
source result is asserted to be refuted by this theorem.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded searches recorded
in #18673 do not rule out every unindexed publication or independent settlement.
The finite decimal computations are not universal theorems. This delivery
asserts no result about the listed open extensions.
