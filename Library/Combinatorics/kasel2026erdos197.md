---
bibkey: kasel2026erdos197
authors: William Kasel
year: 2026
title: "Structural rigidity in the Erdős–Graham two-set permutation problem"
doi: null
url: https://arxiv.org/abs/2609.02939v1
claim: "The full order gadget is nevertheless conjectured infeasible at every M ≥ 16."
strata_touched:
  - D5/S3/Combinatorics/ErdosGrahamOrderGadget
license: citation-only
triage: anchor
---

# Kasel, the order gadget of the Erdős–Graham two-set problem

The preprint studies Erdős Problem 197, whether the positive integers can be split into two sets
each of which admits a permutation with no monotone three-term arithmetic progression. It shows that
the canonical dyadic partition fails, by reducing the question on each dyadic block to a finite
order problem on one interval.

## Verified locator

- URL: https://arxiv.org/abs/2609.02939v1 (v1, 2026-08-31; the only version at the time of reading).
- Locator: Definition 15, "the order gadget OG(M) asks for a linear order ≺ of the interval (M, 2M]
  such that (i) (no monotone AP) for every arithmetic progression a < b < c inside (M, 2M], neither
  a ≺ b ≺ c nor c ≺ b ≺ a holds; and (ii) (guards precede bottoms) for x ∈ {15, 16} and
  1 ≤ j ≤ x/2, the guard t_{x−2j} = 2M + 2j − x precedes the bottom b_j = M + j."
- Locator: Remark 30, "The full order gadget is nevertheless conjectured infeasible at every M ≥ 16
  (machine-verified for 16 ≤ M ≤ 200 and M = 512, Proposition 18); … a proof beyond the swept scales
  would need per-residue analogues of Theorems 27–28 built from the same flood toolkit."
- Theorem 22 proves the case M ≡ 0 (mod 8) through the three guards t_5 ≺ b_5, t_3 ≺ b_6,
  t_10 ≺ b_3; Proposition 19 reports that these three are satisfiable together with (i) at the other
  residues.
- The author's repository https://github.com/Wkasel/erdos197 lists the full conjecture as the first
  open item in `STATUS.md`; its last push is 2026-09-06.

## Reading of the statement

Write `b_j = M + j` and `t_i = 2M − i`. A linear order of the block is AP-free when on every in-block
progression `a < b < c` with `a + c = 2b` the middle term precedes both ends or follows both. The
conjecture asserts that for every `M ≥ 16` no AP-free linear order of `(M, 2M]` satisfies all fifteen
guard relations of (ii).

## Scope of the recorded answer

The conjecture holds. Four guards suffice in each parity: for even `M` the guards
`t_11 ≺ b_2, t_7 ≺ b_4, t_14 ≺ b_1, t_10 ≺ b_3` (the instances `(x, j) = (15,2), (15,4), (16,1), (16,3)`),
and for odd `M` the guards `t_13 ≺ b_1, t_9 ≺ b_3, t_12 ≺ b_2, t_8 ≺ b_4` (the instances
`(15,1), (15,3), (16,2), (16,4)`), are already inconsistent with AP-freeness. The proof uses the
paper's zigzag, phase dichotomy and flood lemmas, splits once on the order of two adjacent tops,
and in each branch forces `c ≺ d ≺ c` for two centers `c, d = c + 2` just below `3M/2`.

## Bounded prior-resolution evidence

The erdosproblems.com pages for Problem 197 (problem page, forum thread and proof-claims page, read
2026-09-23) show the problem open, no proof claims and nobody listed as working on it. The
formal-conjectures repository states only the parent problem. Searches by title, arXiv number and
"order gadget" returned no later proof. Citation indices were not exhaustively reachable, so this is a
bounded negative finding.
