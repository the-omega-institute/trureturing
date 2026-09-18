# Shieh–Yang–Yu Conjecture 6.2 isolated probe

## Falsifiable predictions (registered before checks)

1. An independent Python implementation of West's stack map composed with reversal of each valley run reproduces Theorem 4.4 fixed-point counts for n = 1,...,8: 1,1,2,4,9,23,65,199, and Theorem 4.2 sortable counts 2^(n-1).
2. There is no cycle of length at least two among permutations of 1,...,n for 1 <= n <= 8.
3. At every non-fixed permutation in that range, the reversed output word is strictly larger in lexicographic order than the reversed input word.

These are predictions, not measured results. The source fidelity check precedes execution of the Python experiment. The preregistration defines the barred-pattern stack map by the proved right-hand side of Proposition 3.5; that boundary is retained explicitly.

## Status

Unverified: source fidelity, numerical predictions, library reuse, and Lean proof. No mathematical conclusion is claimed yet.

## Source fidelity

Checked arXiv:2411.11914v2 directly (PDF downloaded only to runner scratch), against issue #8639. The clauses agree:

- The machine is the dotted-pattern stack map followed by West's map, composition `s ∘ s_{21-dot}` (printed p. 2).
- A valley is strictly smaller than every earlier entry; the first entry is a valley vacuously. Runs are maximal consecutive blocks beginning at valleys (printed p. 3). The example is `243 | 15`.
- Proposition 3.5 states reversal of each valley run. Using that proved expression as the definition retains the preregistered source-level identification; this probe does not formalize the dotted-pattern operational map or Proposition 3.5's identification with it.
- West's stack is increasing from top to bottom, operating right greedily. On distinct entries, popping while top < input, then pushing, has exactly that behavior.
- Conjecture 6.2 quantifies over all permutations in S_n and every n >= 1 and asserts eventual arrival at a fixed point. The requested consecutive-iterate equality is exactly that assertion; it does not assert sorting to the identity.
- The numerical anchors are Theorem 4.2 (one-pass sortable count 2^(n-1)) and Theorem 4.4 (fixed points, A007476).

Locator correction only: in the fetched v2, Proposition 3.5 is on printed p. 6, not p. 5. Conjecture 6.2 is on printed p. 11 after its introduction on p. 10. This changes no mathematical clause and does not require a statement revision.

## Independent exhaustive Python result

`python3 probe/check_syy.py > probe/python_results.json` exited 0. All 46,233 permutations in S_1 through S_8 were inspected. Fixed-point counts were `1,1,2,4,9,23,65,199`; one-pass sortable counts were `1,2,4,8,16,32,64,128`. Both preregistered anchors match. Functional-graph traversal found 0 nontrivial cycles; direct comparison found 0 reversed-lex potential violations. Every image preserves its input multiset. The source examples `243 | 15` and West's `3124 -> 1234` also match. This is finite experimental evidence, not a proof of Conjecture 6.2.
