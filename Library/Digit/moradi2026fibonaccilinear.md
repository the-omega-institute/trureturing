---
bibkey: moradi2026fibonaccilinear
authors: Delaram Moradi; Narad Rampersad; Jeffrey Shallit
year: 2026
title: "Complexity of Linear Subsequences of Fibonacci-Automatic Sequences"
doi: 10.48550/arXiv.2603.21645
url: https://arxiv.org/abs/2603.21645v1
claim: "Problem 1 asks whether the number of states in a minimal automaton generating (t(i+c))_{i≥0} is Θ(c)."
strata_touched:
  - D5/S1/Digit/ZeckendorfProblem1Refutation
license: CC BY 4.0
triage: anchor
---

# Complexity of linear subsequences of Fibonacci-automatic sequences

Delaram Moradi, Narad Rampersad, and Jeffrey Shallit, *Complexity of Linear
Subsequences of Fibonacci-Automatic Sequences*, arXiv:2603.21645v1.

## Problem 1

The source states: “We suspect that the number of states in a minimal automaton
generating `(t(i+c))_{i≥0}` has a linear lower bound too. The following is left
as an open problem. Problem 1. Prove the number of states in a minimal automaton
generating `(t(i+c))_{i≥0}` is `Θ(c)`.” The sequence `t` is the paper's
Fibonacci-Thue-Morse sequence: `t(i)` is the number of ones in the canonical
Fibonacci representation of `i`, modulo two. Theorem 14 gives the `O(c)` upper
bound; Problem 1, in Section 4 (Linear Subsequences), asks for `Θ(c)`.

## Model convention

Section 2.1 defines a DFA with a partial transition function to handle dead
states, and says that dead states are not counted or displayed. Section 2.2
uses msd-first Fibonacci (Zeckendorf) representations for Fibonacci-DFAOs and
assumes that an automaton reaches no state on an invalid Fibonacci
representation. Section 2.1 also requires invariance under arbitrary leading
zeros and a zero self-loop at the initial state. The formalization keeps these
conventions and makes the valid padded-word domain, undefined invalid execution,
counted zero-loop start, omitted sink, reachability of every counted state, and
attained minimum explicit. The empty word and every all-zero word represent zero
and output `t(c)` for the shifted sequence.

Writing `s(c)` for that minimum, the full eventual uniform statement is
`∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c →
a * c ≤ s(c) ∧ (s(c) : ℝ) ≤ b * c`.
The formal result proves its literal negation. It constructs correct reachable
partial machines for every shift and an unbounded Fibonacci family whose state
counts divided by the shifts tend to zero. This family contradicts every
positive uniform eventual lower bound. The paper's upper-bound result is
compatible with this failure of the lower bound.

## Verified locator

- DOI: 10.48550/arXiv.2603.21645
- URL: https://arxiv.org/abs/2603.21645v1
- HTML URL: https://arxiv.org/html/2603.21645v1
- TeX source URL: https://arxiv.org/src/2603.21645v1
- License: CC BY 4.0; the abstract page links to http://creativecommons.org/licenses/by/4.0/ and the HTML page labels the paper CC BY 4.0.
- Scope: Section 2.1 partial DFA, padding and initial zero-loop conventions; Section 2.2 msd-first Fibonacci-DFAO convention; Section 4, Theorem 14 and Problem 1.
