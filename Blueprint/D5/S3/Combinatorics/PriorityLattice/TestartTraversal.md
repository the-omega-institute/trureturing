# Decreasing-Child DFS and Minimum-First Cycles

## Abstract

Fixed native increasing-tree and strict-excedance permutation maps, with their operational certificates.

**Definition 1.1 (Insert a new maximum).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.splice`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.splice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Insert a letter immediately after the selected parent in a distinct-label word. A missing parent leaves the word unchanged.

**Definition 1.2 (Decreasing native children).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.children`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.children` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Enumerate child labels in strictly decreasing order. Parent codes are read through the existing native parent-field interface.

**Definition 1.3 (Literal root-first DFS).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.preorder`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.preorder` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Read the root, then recursively read each child subtree in decreasing child-root order. The result theorem proves this defining recursion for the insertion implementation.

**Definition 1.4 (Delete root zero).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.componentWords`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.componentWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Read the preorder of each child component of the removed zero root. No planar or binary structure is stored or assumed.

**Definition 1.5 (Keep each cyclic direction).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.cycleProduct`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.cycleProduct` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Use the pinned List.formPerm on every component word and multiply the disjoint cycles. Singleton words remain present and give fixed points.

**Definition 1.6 (Certified actual cycle words).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.CycleWords`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.CycleWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

The flattened words permute exactly labels 1 through n. Every word starts at its unique minimum. Every actual permutation value equals the next letter, with the final letter returning to the first, by the upstream directed-cycle successor theorem.

**Definition 1.7 (Last smaller entry).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.previousSmaller`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.previousSmaller` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Scan the preceding letters from left to right, replacing the accumulator whenever a letter is strictly smaller than the queried letter. Zero is the initial sentinel.

**Definition 1.8 (Rightmost preceding smaller letter).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.wordParent`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.wordParent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Stop strictly before the queried letter and select the final smaller entry. For a minimum-first cycle its first entry receives zero.

**Definition 1.9 (Select the containing cycle).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.parentLookup`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.parentLookup` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Use the unique cycle word containing the queried positive label and apply wordParent. The cycle partition prevents conflicting containing words.

**Definition 1.10 (All parent attachments).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.reconstructCode`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.reconstructCode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Perform the prescribed attachment at every positive label. Every selected parent is strictly smaller, so the code belongs to the existing unrestricted parent-code family.

**Definition 1.11 (Minimum-first directed decomposition).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.permutationWords`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.permutationWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Compute words by inverse maximum insertion. The CycleWords certificate independently checks that these are actual minimum-first cycles of the supplied permutation in its original direction, including all singleton cycles.

**Definition 1.12 (Restore the native root).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.reconstructTree`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.reconstructTree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Decode all rightmost-smaller attachments through the existing treeEquivCode, retaining the actual native parent fields and root zero.

**Definition 1.13 (Exact last-entry certificate).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.RightmostSmaller`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.RightmostSmaller` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Either no preceding letter is smaller and the parent is zero, or the prefix splits at the selected smaller parent and every later preceding letter is at least the query.

**Definition 1.14 (The fixed forward map).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.F`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.F` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Delete zero, traverse each component root first with decreasing child roots, turn each word into a cycle in that direction, and apply D. The definition uses insertion for execution; ForwardSpec certifies exactly these operations.

**Definition 1.15 (The fixed inverse map).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.H`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.H` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Apply D, take its certified minimum-first cycles without reversing their direction, attach every later letter to the rightmost preceding smaller letter, and attach each cycle minimum to restored zero.

**Definition 1.16 (Native forward specification).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.ForwardSpec`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.ForwardSpec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

Child membership is equivalent to actual native parent incidence. Child order strictly decreases; preorder satisfies the root-first DFS equation. The component words partition all positive labels and give the actual directed cycles. The reflected position and complemented value formulas are the sealed D formulas.

**Definition 1.17 (Native inverse specification).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.ReverseSpec`

*Formalization.* `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.ReverseSpec` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

The supplied words are actual minimum-first directed cycles of D. Every reconstructed native parent equals the cycle lookup and satisfies the explicit rightmost-smaller certificate. The restored root has no parent.

**Theorem 1.18 (The full fixed-map theorem).**

Lean statement: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result` (`✓ std3`). ∎

*Resolves.* `Problems/testart-2026-question-one-type-c-tree-bijection` (proved) by `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"testart-2026-question-one-type-c-tree-bijection","declaration_gid":"D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benjamin Testart (2026). *On minimal pattern-containing inversion sequences*. URL: <https://arxiv.org/abs/2602.12130v2>.

*Commentary.*

For all positive integers a,b, set n=a+b-1. The source consists of all unordered increasing trees on labels 0 through n with root zero, internal labels exactly 0 through a-1, and leaves exactly a through n. The target consists of all actual permutations of labels 1 through n whose strict excedance positions are exactly 1 through b-1; fixed points are allowed. F and H satisfy their literal operational specifications, F lands in the target, H lands in the source, H(F(t))=t for every source tree, and F(H(s))=s for every target permutation. There is no bound on n, no planar or binary restriction, and no omitted a=1, b=1 or n=1 case.

The proof inserts the current maximum immediately after its parent, or as a singleton cycle when its parent is zero. Induction proves that this insertion has the literal decreasing-child DFS recursion, the exact directed cycle successor relation, and the rightmost-smaller parent reconstruction. The individual-label statistic identifies every positive internal vertex with a strict excedance position. The fixed involution D exchanges the required prefix statistics, yielding both restricted landings and inverse identities.

Testart, arXiv:2602.12130v2, Sections 6 and 7 Question 1, supplies the source family and question. Bényi and Hajnal, arXiv:1602.08684v1, Section 3.2 Theorem 12(ii), supplies the published interpretation of the target by C(a,b-1). The count interpretation is attributed to that paper; it is not a newly formalized counting theorem here. The construction answers the tree side of the source disjunction at the mathematical level. No priority claim is made here.

## References

- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.CycleWords`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.F`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.ForwardSpec`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.H`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.ReverseSpec`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.RightmostSmaller`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.children`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.componentWords`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.cycleProduct`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.parentLookup`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.permutationWords`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.preorder`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.previousSmaller`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.reconstructCode`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.reconstructTree`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.result`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.splice`
- Truth anchor: `D5/S3/Combinatorics/PriorityLattice/TestartTraversal.wordParent`
- Dependency: [D5/S3/Combinatorics/PriorityLattice/TestartTreeCode](TestartTreeCode.md)
