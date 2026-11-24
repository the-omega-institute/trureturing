---
slug: naimi-2026-cyclic-compatible-word-replacement
bibkey: naimi2026swapping
doi: 10.48550/arXiv.2610.31967
url: https://arxiv.org/html/2610.31967v2#S8.p1
triage: theorem
motivation_gids:
  - D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result
---

# Cyclic replacement of adjacent-compatible words

## Problem

Ramin Naimi asks in the opening paragraph of §8 of *Swapping Compatible
Words*, arXiv:2610.31967v2, p. 33.

> It is natural to ask whether one can generalize this work to $n\geq 3$
> words instead of starting with a pair $\{p,q\}$ of compatible words.
> For example, given a sequence $(p_{0},\cdots,p_{n})$, with $p_{n}=p_{0}$,
> what can be said if $\{p_{i},p_{i+1}\}$ is compatible? Can we bijectively
> replace every $p_{i}$ inside any given word $\Omega$ with $p_{i+1}$,
> without creating any new instances of any $p_{i}$?

The quote is attributed to Ramin Naimi. [Versioned source](https://arxiv.org/pdf/2610.31967v2#page=33) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

Let $B(x,y)$ consist of the lengths at which a suffix of $x$ equals a
prefix of $y$, including length zero and permitting full length. Let
$\sigma(i)=i+1\bmod n$. For every finite alphabet and every cycle of
$n\geq3$ patterns with
$B(p_i,p_i)=B(p_{\sigma(i)},p_{\sigma(i)})$ and
$B(p_i,p_{\sigma(i)})=B(p_{\sigma(i)},p_i)$ at every label, the proposed
answer asks for a bijection on all hosts of each length $L$. For every host,
label and start, the input occurrence of $p_i$ must be equivalent to the
output occurrence of $p_{\sigma(i)}$ at the same start. Equal self-border
sets force the pattern lengths to agree. The pattern labels may repeat.
In §2.1, a positional occurrence occupies a nonempty interval, so the
all-empty pattern cycle has vacuous occurrence requirements.
[§2.1](https://arxiv.org/html/2610.31967v2#S2.SS1) · [§2.4](https://arxiv.org/html/2610.31967v2#S2.SS4)

## Motivation

The question tests whether compatibility of consecutive pattern pairs
controls all overlapping substitutions in a larger cycle. Replacing every
occurrence at its original start requires the new patterns to agree at
every shared host coordinate.

## Gap

The bounded literature check found the question in v2 and found no exact
settlement in the sources examined. The checked single-pattern avoidance
bijection and overlap enumeration results address different conclusions.
The preregistration gives the version comparison, supplier search and
coverage limits. [Issue #33746](https://github.com/the-omega-institute/trureturing/issues/33746)

## Route

Use the alphabet `{0,1,2}` and the cycle `001, 002, 011, 021`. Rows in
the directed border table give suffix owners and columns give prefix owners.

| | `001` | `002` | `011` | `021` |
|---|---|---|---|---|
| `001` | {0,3} | {0} | {0,2} | {0} |
| `002` | {0} | {0,3} | {0} | {0,2} |
| `011` | {0} | {0} | {0,3} | {0} |
| `021` | {0} | {0} | {0} | {0,3} |

The diagonals agree and the two directed sets of every adjacent pair
equal `{0}`. The host `0021` contains `002` at zero-based start 0 and
`021` at start 1. The required successors are `011` at start 0 and
`001` at start 1. Their offsets 1 and 0 force, respectively, 1 and 0
at the same output coordinate.

## Falsifier

Any differing directed border entry, missing input occurrence, or
agreement of the successor letters at the shared coordinate would
invalidate the corresponding step of this certificate.

## Evidence

`D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result` proves the
literal `Not claim`. The Lean proof checks every entry of the border
table, proves that the adjacent pairs are compatible, and applies both
forward occurrence implications to one output. The theorem's axiom
closure contains `Classical.choice`, `Quot.sound`, and `propext`.

## Triage

### What the settlement shows

- **Proved.** The finite-linear universal assertion is false. The overlapping
  labels 1 and 3 use a length-two border `02`, which their successors lack.
  The contradiction already follows from forward preservation on the single
  host. The same certificate satisfies the alternative condition of equal
  self-border sets and one common directed forward-edge set, since every
  forward edge has set `{0}`. [Lean result](../D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.lean)
- **Computed.** The printed alternative example `01110, 10011, 11001`
  has forward sets `{0,2}`, `{0,1,2}`, and `{0,2}`. These are obtained by
  comparing the suffix and prefix at each length from 0 through 5.
  In particular, `10011` and `11001` share the length-one border `1`
  in the forward direction. [Section 8](https://arxiv.org/html/2610.31967v2#S8.p1)
- **Open for separate formalization.** Invariance of all ordered border sets
  under simultaneous label rotation is a candidate condition. It governs
  every shared interval, including those between nonadjacent labels. The
  preregistration gives a finite counting argument for the corresponding
  bijection criterion. [Issue #33746](https://github.com/the-omega-institute/trureturing/issues/33746)
- **Scope.** The result addresses the universal $n\geq3$ positional claim
  over finite linear hosts. The source's two-pattern theorem has its own
  hypotheses and host class. Circular, countably infinite, bi-infinite
  and uncountable hosts are separate questions in §8.
  [Theorem 28](https://arxiv.org/html/2610.31967v2#Thmtheorem28) · [Section 8](https://arxiv.org/html/2610.31967v2#S8)

## ASSUMED-UNVERIFIED

The literature check has no Semantic Scholar citation coverage or
Guibas–Odlyzko full-text coverage. Priority beyond the surfaces checked
remains unverified. [Issue #33746](https://github.com/the-omega-institute/trureturing/issues/33746)
