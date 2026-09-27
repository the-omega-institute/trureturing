---
slug: shieh-yang-yu-dotted-machine-fixed-point-convergence
bibkey: yangshiehyu2025dotted
doi: null
url: https://arxiv.org/abs/2411.11914v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.result
---

# Convergence of the Shieh-Yang-Yu dotted-pattern machine

## Problem

Michael Yang, Hansen Shieh, and Ashley Yu, *Stack-Sorting with
Dotted-Pattern-Avoiding Stacks*, arXiv:2411.11914v2, Section 6, printed
page 11, state:

> Conjecture 6.2. All permutations in Sₙ for all n ≥ 1 are eventually mapped to a fixed point of the 21̇-machine after a finite number of iterations through the machine.

The preceding sentence asks whether this machine has any cycle of length
at least two. The machine applies the dotted-pattern map first and West's
stack-sorting map second.

## Motivation

Issue #8639 preregisters this first-tier external named conjecture with its
source, full quantifiers, and literature-search boundaries. The public
statement is `∀ n ≥ 1, ∀ w ~ List.range' 1 n, ∃ t : ℕ,
(M^[t + 1]) w = (M^[t]) w`, where `M w = s (r w)`.

## Gap

The source proves the fixed-point characterization and enumeration
(Lemma 4.3 and Theorem 4.4), but does not prove that every periodic point
is fixed. The arXiv API searches recorded in #8639 found no settlement;
those searches are bounded and do not establish publication priority.

## Route

A valley is an entry strictly smaller than every preceding entry. A valley
run starts at a valley and ends immediately before the next valley.
The map `r` reverses each valley run, preserving the order of the runs.
The map `s` implements West's pop/push/flush stack algorithm.

For every word without repeated entries, the reversed word is
lexicographically no larger than the reversal of its image under `M`.
The proof uses strong induction on word length and decompositions at
minimal and maximal entries. Both component maps preserve the multiset
of entries. The reachable orbit is therefore contained in a finite set
of permutations. At a reachable word with maximal reversed word, weak
monotonicity forces equality of potentials. Injectivity of reversal then
forces equality of successive iterates.

## Falsifier

A permutation whose orbit under the stated operational machine contains
a cycle of length at least two would contradict the conclusion. A
mismatch between the formal maps and the source's maps would invalidate
the transfer to the source conjecture, independently of kernel checking.

## Evidence

The theorem `D5/S1/Words/Patterns/ShiehYangYuMachineConvergence.result`
proves the fully quantified eventual fixed-point statement. Its five
public definitions are `IsValley`, `valleyRuns`, `r`, `s`, and `M`.
The live monotonicity lemma is private `potential_weak`; the result is
unbounded and uses no finite enumeration or numerical certificate.
The Scribe resolution kind is `Proved`.

## Triage

`theorem`. This resolves Conjecture 6.2 for the source's Proposition 3.5
model of the 21̇-machine. Conjecture 6.1 is outside the result.

## ASSUMED-UNVERIFIED

DEFINITION BOUNDARY — the source defines s_{21̇} through Baril's dotted patterns and PROVES the closed form of Proposition 3.5; this module takes that proved right-hand side (reverse each valley run) as the definition of `r`; the identification of the dotted-pattern stack with valley-run reversal is the source's theorem and is not formalized here.

No citation index was retrieved — whether a later paper settles
Conjecture 6.2 is `ASSUMED-UNVERIFIED` beyond the arXiv API searches in
#8639 and a ChatGPT Pro literature seat that found no citing work.
