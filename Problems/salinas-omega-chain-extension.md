---
slug: salinas-omega-chain-extension
bibkey: salinasschmeis2026omega
doi: null
url: https://arxiv.org/abs/2610.29056v1
triage: theorem
motivation_gids:
  - D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.result
---

# Least omega-chain-partitionable extensions need not exist

## Problem

Remi Salinas Schmeis, *General Criterion for a Poset to Admit a Partition Into omega-Chains*, arXiv:2610.29056v1, page 14, Question 2.32:

> Let P be a poset. Does there exist a minimal extension Q of P which can be partitioned into ω-chains? Here by minimal we mean that if Q′ is any extension of P which can be partitioned into ω-chains, then Q is order-isomorphic to a subposet of Q′.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A poset P | `claim` quantifies `P : Type` and `pOrder : PartialOrder P` | All carriers in the fixed ambient universe; empty carriers are allowed. |
| An extension Q of P | `IsExtension P Q` | A nonempty type of order embeddings preserves and reflects the induced order; no requirement that comparison embeddings fix P. |
| Partitioned into ω-chains | `OmegaPartitionable Q` and `IsOmegaChain` | `Setoid.IsPartition` covers the entire carrier with disjoint nonempty parts, each order-isomorphic to the naturals with inherited order. |
| Every admissible extension Q′ | The last universal quantifier and two implications in `claim` | No countability, nonemptiness or additional compatibility hypothesis is imposed. |
| Q is order-isomorphic to a subposet of Q′ | `Nonempty (OrderEmbedding Q Q′)` | An embedding identifies Q with its induced image. |
| Negative answer | `result : ¬ claim` | Refutes the entire universally quantified assertion using one finite base. |

The public definitions preserve the preregistered expressions. `PartialOrder`, `OrderEmbedding`, `OrderIso` and `Setoid.IsPartition` are reused Mathlib notions. The source does not separately define extension; its induced-order interpretation is the binding convention in [#23817](https://github.com/the-omega-institute/trureturing/issues/23817).

## Motivation

The question asks for a least admissible extension in the embedding preorder, rather than an inclusion-minimal extension. The connected fork with bottom r and incomparable points a,b has two individually admissible extensions whose upper-bound structures are incompatible with any common admissible predecessor containing the fork.

The settling module has `generality: I`, `utility: none`, and `admission_basis: open-problem-resolution (#23817; Refuted)`. The argument concerns arbitrary embeddings of infinite orders and supplies no finite certificate or numerical-reduction result. Its public theorem is `D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisOmegaChainExtensionRefutation.result`.

## Gap

The source gives Question 2.32 among its future questions. The partial literature screen recorded in #23817 inspected the primary source and version history, successful arXiv author/text queries, MathOverflow and Zenodo searches, public formal-conjecture snapshots and repository results. No matching settlement was identified in the inspected scope. Citation enumeration was unavailable, several Zenodo endpoints were blocked, and the original MacNeille completion article was not independently read. This is not a claim of worldwide novelty or exhaustive literature coverage.

## Route

Let $R=\{0,1\}\times\mathbb N$. Its order is
$x\le_R y$ iff $x=(0,0)$ or $x_1=y_1$ and $x_2\le y_2$.
The fork maps to $(0,0),(0,1),(1,0)$. The two full rays are disjoint omega-chains covering R. Two points below a common upper bound in R are comparable.

Let T be the natural numbers with their usual comparison except that $1\le 2$ is removed. The fork maps to $0,1,2$. The even and odd numbers are disjoint omega-chains covering T. Its only incomparable unordered pair is $\{1,2\}$, and every strict successor of either incomparable point is above the other.

If Q is omega-chain partitionable, every x has a strict successor: take its containing part, transport x to n under the part's order isomorphism, and use $n+1$. Suppose Q contains the fork and embeds into both R and T. The fork images remain incomparable. A strict successor z of the first branch becomes an upper bound of the other branch in T. Reflection transfers this upper bound to Q, and preservation transfers it to R. The common-upper-bound comparison in R contradicts incomparability. A least admissible extension would have to embed into both R and T, which proves the negative answer.

## Falsifier

A failure of either induced-order embedding, either covering disjoint partition, the strict-successor implication, or either upper-bound property would invalidate this construction. The settling theorem has no assumed mathematical hypotheses and proves the literal negation of `claim`. Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Evidence

### Formal evidence

The Lean module and its Blueprint Scribe are at `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.lean` and the corresponding `Blueprint/D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.scribe.cs`. Its private theorems are `omega_successor`, `rays_upper_comparable`, `tail_forced_bound`, `partition_of_two`, `rays_partition`, `tail_partition`, and `incompatible`; each is consumed by the settling proof. The public settling theorem and these helpers are `proof_shape: bind-only` after same-delivery expansion. The external named-problem resolution is the admission basis; no escape witness is claimed. There are no D5 imports or direct frozen prerequisites.

Escape audit unfinished: [#28004](https://github.com/the-omega-institute/trureturing/issues/28004) names the public `result`. Because the symbolic argument has `utility: none`, it has no utility-refutation audit exemption. No Reg mirror or validated four-slot registration is claimed. A lawful source reconstruction, enrolled readout and the family bridge, variation, sensitivity and observational-dependence evidence are missing.

### Finite supporting experiment

[Immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d453d72ed364991569e954374859a20b9f829664/docs/reports/salinas-omega-chain-extension).
The program is `docs/reports/salinas-omega-chain-extension/check.py` at commit `d453d72ed364991569e954374859a20b9f829664`, SHA-256 `4f43ac92d490c5b143c4098c57e71ad77e82fa5c0b233f9f5777fb97b37d571c`.
The implementation seat executed `python3 /Users/auric/.sshx/0b11d7c8eb5cd6e8017985fa/attempt-1/stageb/check.py` on those exact bytes, exit 0, `ALL_CHECKS_OK`.

Naturally labelled posets of sizes $1,\ldots,5$ have counts $1,2,7,40,357$ (407 total); greatest-element counts are $1,1,2,7,40$. The merged-tail partition checks use tail indices $0,\ldots,6n-1$, with strict successors also tested beyond that window. The program checks 868 maximal assignments, 912 lower-cone-plus-ray cases and 337295 merged-tail escape witnesses. For stars with $2,\ldots,6$ maxima at ray heights $1,\ldots,8$, it checks 7140 separated-ray incomparable pairs and 15120 merged-tail forced-upper-bound triples. These exact finite computations do not establish any infinite universal assertion or formal classification.

## Triage

### What the settlement shows

1. **Proved (kernel-checked):** `result` refutes the universal assertion for the connected three-element fork; `rays_partition` and `tail_partition`, with `intoRays` and `intoTail`, establish that both displayed extensions are admissible. The failure is leastness. The fork is connected (proved in prose): its root is below each branch, giving a path between all three vertices in the undirected Hasse diagram.
2. **Proved in prose:** The obstruction only needs the strict-successor property of Q. For incomparable fork images x,y, choose z with $x<z$. Reflection under the Tail embedding keeps their images incomparable; `tail_forced_bound` places y below z. Preservation under the Rays embedding and `rays_upper_comparable` contradict their incomparability. Neither comparison embedding must fix the fork. The kernel-checked `incompatible` states the omega-partitionable case; this weaker-premise generalization is the displayed prose argument, not an extra Lean theorem.
3. **Computed:** The finite star checks cover $2,\ldots,6$ maximal elements and ray heights $1,\ldots,8$, with 7140 incomparable pairs and 15120 forced-upper-bound triples. Evidence: the immutable experiment, command, exit 0 and SHA-256 above. A uniform star-family Lean theorem is not delivered.
4. **Computed:** The finite-poset enumeration covers sizes $1,\ldots,5$: counts $1,2,7,40,357$, greatest-element counts $1,1,2,7,40$, 868 maximal assignments, 912 lower-cone-plus-ray cases and 337295 escape witnesses. Evidence: the same experiment reading. It is finite supporting evidence only.
5. **Open:** The full formal classification for nonempty finite P, existence of a least extension iff P has a greatest element, is a separate candidate. No additional classification theorem is included.
6. **Open:** An already omega-chain-partitionable P being its own least extension, and the merged-tail construction being least for finite P with a greatest element, are surviving neighbours not separately Lean-verified here.
7. **Open:** The effect on source claims outside Question 2.32 has not been formally audited. The source inspection recorded in #23817 identified no dependence on an affirmative answer; the question is in the closing future-question list. No stronger dependency clearance is claimed.

## ASSUMED-UNVERIFIED

Literature completeness, unavailable citation enumeration, the blocked Zenodo queries and the original MacNeille-source reading remain `ASSUMED-UNVERIFIED`. The source/literature inspection is attributed to the preregistration producers; this dossier does not turn their partial screen into an exhaustive search. The separate classification and surviving-neighbour formalizations remain open. Four-slot escape registration for `result` is unfinished under #28004.
