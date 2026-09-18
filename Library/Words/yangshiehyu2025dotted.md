---
bibkey: yangshiehyu2025dotted
authors: Michael Yang, Hansen Shieh, Ashley Yu
year: 2025
title: Stack-Sorting with Dotted-Pattern-Avoiding Stacks
doi: null
url: https://arxiv.org/abs/2411.11914v2
claim: "Valley runs, Proposition 3.5, and Conjecture 6.2 for the 21-dot machine."
strata_touched:
  - D5/S1/Words/Patterns/ShiehYangYuMachineConvergence
license: citation-only
triage: anchor
---

# The Shieh-Yang-Yu machine

The following quotations are from arXiv:2411.11914v2, with printed page numbers.

Section 1, p. 1:

> West’s stack-sorting map s processes the input permutation through a stack in a right greedy manner such that elements of the stack always increase from top to bottom (see for example, Figure 1).

Section 1, p. 2:

> Similarly, inspired by Cerbai, Claesson, and Ferrari’s [6] σ-machines, we establish τ̇-machines, which consist of the dotted pattern-avoiding map sτ̇ followed by s, and are to be denoted by s ◦ sτ̇.

Section 2, p. 3:

> Similarly, a valley of π is an entry πᵢ of π such that πᵢ is less than each π₁, π₂, . . . , πᵢ₋₁.

> Similarly, a valley run is defined as a maximal sequence of consecutive entries such that the first entry is a valley and no other entry is a valley.

The source example 24315 has valley runs 243 and 15. Its notation
π = V₁V₂ . . . Vₖ denotes the unique partition into valley runs.

Proposition 3.5, p. 6:

> Let π = V₁V₂ . . . Vₖ ∈ Sₙ. Then, s₂₁̇(π) = rev(V₁)rev(V₂) . . . rev(Vₖ).

Conjecture 6.2, p. 11:

> All permutations in Sₙ for all n ≥ 1 are eventually mapped to a fixed point of the 21̇-machine after a finite number of iterations through the machine.

The source defines s_{21̇} through Baril's dotted patterns and PROVES the closed form of Proposition 3.5; this module takes that proved right-hand side (reverse each valley run) as the definition of `r`. The identification of the dotted-pattern stack with valley-run reversal is the source's own theorem and is NOT formalized here.

In Lean, words are `List ℕ`, membership in Sₙ is
`w.Perm (List.range' 1 n)`, and `M w = s (r w)`. The operational map `s`
pops while the stack top is smaller than the next input, pushes otherwise,
and flushes at end of input. The theorem gives a natural t with
`(M^[t + 1]) w = (M^[t]) w` for every n ≥ 1 and every permutation w in Sₙ.
The convergence proof is derived here; the citation credits the conjecture
and definitions, not a published proof. Conjecture 6.1 is outside this result.
