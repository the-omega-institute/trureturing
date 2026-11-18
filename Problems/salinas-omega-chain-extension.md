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
| A poset P | `claim` quantifies `P : Type u` and `pOrder : PartialOrder P` | The base, candidate and comparison levels are independent, and the base may be empty. |
| An extension Q of P | `IsExtension P Q` | A nonempty type of order embeddings preserves and reflects the induced order; no requirement that comparison embeddings fix P. |
| Partitioned into ω-chains | `OmegaPartitionable Q` and `IsOmegaChain` | `Setoid.IsPartition` covers the entire carrier with disjoint nonempty parts, each order-isomorphic to the naturals with inherited order. |
| Every admissible extension Q′ | The last universal quantifier and two implications in `claim` | The comparison order is arbitrary in its universe, subject only to the extension and partition conditions. |
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

The Lean module and its Blueprint Scribe are at `D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.lean` and the corresponding `Blueprint/D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisOmegaChainExtensionRefutation.scribe.cs`. The proof uses the actual Rays and Tail order laws and partitions. Its private structural theorems include `rays_upper_comparable`, `tail_forced_bound` and `partition_of_two`. The public `incompatible` theorem combines the first two with an arbitrary incomparable pair and the strict-successor property. The admission basis for the original `result` is the named-problem settlement in #23817.

Escape audit unfinished: [#28004](https://github.com/the-omega-institute/trureturing/issues/28004) names the public `result`. Because the symbolic argument has `utility: none`, it has no utility-refutation audit exemption. No Reg mirror or validated four-slot registration is claimed. A lawful source reconstruction, enrolled readout and the family bridge, variation, sensitivity and observational-dependence evidence are missing.

### Finite supporting experiment

[Immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/d453d72ed364991569e954374859a20b9f829664/docs/reports/salinas-omega-chain-extension).
The program is `docs/reports/salinas-omega-chain-extension/check.py` at commit `d453d72ed364991569e954374859a20b9f829664`, SHA-256 `4f43ac92d490c5b143c4098c57e71ad77e82fa5c0b233f9f5777fb97b37d571c`.
The implementation seat executed `python3 /tmp/op-salinas2610/check.py` on those exact bytes, exit 0, `ALL_CHECKS_OK`.

Naturally labelled posets of sizes $1,\ldots,5$ have counts $1,2,7,40,357$ (407 total); greatest-element counts are $1,1,2,7,40$. The merged-tail partition checks use tail indices $0,\ldots,6n-1$, with strict successors also tested beyond that window. The program checks 868 maximal assignments, 912 lower-cone-plus-ray cases and 337295 merged-tail escape witnesses. For stars with $2,\ldots,6$ maxima at ray heights $1,\ldots,8$, it checks 7140 separated-ray incomparable pairs and 15120 merged-tail forced-upper-bound triples. These exact finite computations do not establish any infinite universal assertion or formal classification.

## Triage

### What the settlement shows

1. `result` refutes the universal assertion using the connected three-element fork. Its root gives a path between the two branches in the undirected Hasse diagram. `rays_partition`, `tail_partition`, `intoRays` and `intoTail` supply the actual competing extensions.
2. `incompatible` needs only an incomparable pair and strict successors. Taking a successor of one image in Tail puts it above both. Reflection carries that upper bound back to the candidate, and the Rays embedding then forces the pair to be comparable. The two incomparable branch images suffice for the two-point antichain.
3. The finite star computations retain the bounds and counts above. The uniform branching-fork inference follows from the bounded-height theorem.
4. **Computed:** The finite-poset enumeration covers sizes $1,\ldots,5$: counts $1,2,7,40,357$, greatest-element counts $1,1,2,7,40$, 868 maximal assignments, 912 lower-cone-plus-ray cases and 337295 escape witnesses. Evidence: the same experiment reading. It is finite supporting evidence only.
5. The bounded-height theorem and its exact applications give the finite classification, self-leastness of admissible orders, and leastness of the merged tail when the base has a greatest point.
6. The inspection recorded in #23817 located Question 2.32 in the closing future-question list and identified no dependence on an affirmative answer. Effects on other primary claims lack a formal dependency audit.

### Revision 2 and its formal counterparts

The revision-2 note, *Bounded-height classification for Salinas Schmeis’s omega-chain extension question*, is by Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National University of Singapore and ChronoAI Pte Ltd, Singapore). Release 445258020 contains the same manuscript as 445172937. The retained revision 1, release 444952904, already contains the two-point argument, duality, arbitrary-base existence and the finite classification. Revision 2 proves the countable bounded-height theorem and the lifting and skeleton corollaries. The original Fork, Rays and Tail proof and #23817 keep the settlement credit for Question 2.32.

| Revision-2 clause | Owning Lean and Blueprint | Exact scope |
| --- | --- | --- |
| S1. Incompatible targets | `SalinasSchmeisOmegaChainExtensionRefutation.incompatible` | An incomparable pair in an arbitrary poset with a strict successor above every point prevents embeddings into both actual targets. |
| S2. Antichain and connected fork | `SalinasSchmeisOmegaChainExtensionRefutation.result`, `incompatible`, `intoRays`, `intoTail` | The fork and the two incomparable branch images give the two obstructions under unrestricted comparisons. Rays has two full inherited rays and Tail has the even and odd parts. |
| S3. Existence | `SalinasSchmeisLexicographicFiberExtension.lexFiberExtension` | Over any base partial order, choose zero in the natural coordinate. The actual fibers partition the product, including the empty product and partition. |
| S4. Countable partition of the natural order | `SalinasSchmeisCountablePartitions.residuePartition`, `twoAdicPartition`, `countablePartition` | For a positive finite modulus use the ranges $i+mk$. For natural indices use $2^i(2k+1)-1$. Transport along a finite or infinite indexing equivalence for each nonempty countable index type. The parts are pairwise disjoint, cofinal, infinite and cover the natural order. |
| S5. Bounded-height classification | `SalinasSchmeisBoundedHeightLeastExtension.ordinalSum_isLeastExtension`, `hasLeastOmegaExtension_iff` | Nonempty countable bases have one uniform finite bound on chain sizes. The ordinal sum and maximal-ray extension use literal inherited parts. The negative direction allows countably infinitely many maxima and appends a maximal point to an image of an attained longest chain in the actual base. Candidate and comparison universes are independent, and maps between extensions need only preserve and reflect order. |
| S6. Instances and sharp boundary | `SalinasSchmeisBoundedHeightLeastExtension`, applications of `hasLeastOmegaExtension_iff` and `IsLeastExtension` | All nonempty finite posets, countable antichains, and bottom points with at least two finite or countably infinitely many incomparable maxima. The empty and singleton cases make the two-point antichain cardinality-minimal. The naturals give a least extension of every nonempty finite chain. |
| S7. Order duality | `SalinasSchmeisBoundedHeightLeastExtension`, dual applications of the partition and leastness predicates | Dualize the inherited order in each part and both ends of every embedding. This gives arbitrary-base existence, the dual fork and two-point obstructions, the least-element classification and its instances for omega-star partitions. |
| S8. Unbounded height | `SalinasSchmeisBoundedHeightLeastExtension.IsLeastExtension` and `PartitionableBy` | Already partitionable orders are self-least. The natural order and its dual are self-least with unbounded finite chain lengths and lack the respective greatest and least points. |
| S9. Explicit lifting | `SalinasSchmeisLexicographicFiberExtension.lexNatFiberLifting` | For Noetherian $K$ in the natural-fiber extension, P and K may be uncountable. Each natural section is finite. In a nonempty section, add one plus its maximum to the natural coordinate. The resulting injection lands strictly above the input and outside K, giving both lifting and the local-shortness inequality. |
| S10. Ordinal extensions and finite skeletons | `SalinasSchmeisLexicographicFiberExtension.lexFiberExtension` and `SalinasSchmeisBoundedHeightLeastExtension.finiteSkeletonObstruction` | For each nonzero ordinal, including one, successor, limit and uncountable ordinals, use its actual carrier with an independent universe and the distinguished point at zero. The covering family is cofinal. For every natural $n\ge2$, the one-part skeleton in `Fin (n + 1)` is the inherited interval $\{1,\ldots,n\}$. A partition would give $n+1=nm$. At $n=1$ the singleton partition exists, and a singleton poset has no 2-skeleton. |
| S11. Prior results and exclusions | This provenance map and the Salinas primary locator | The primary partition, lifting, local-shortness and duality credits, the restrictions on the MacNeille analogy, the original settlement and the audit scope are recorded below. |

Each cited Blueprint contains the arguments and source conditions for its own results. Exact specializations and boundary applications use these declarations. The manuscript’s finite `verify.py` checks bounded order and partition examples, including finite orders on at most five points. The inherited finite experiment above has its own scope and custody.

#### Primary provenance and limits

- Salinas Schmeis’s Question 2.3 (p. 3) asks the general partition question. Theorem 2.5 (p. 4) proves the partition result for countable posets with no maximal element. Theorem 2.27 (p. 12) gives the equivalence of lifting and partitionability for posets with no maximal element. Definitions 2.14 (p. 7) and 2.26 (p. 12) give the local-shortness and lifting conditions.
- Salinas Schmeis’s Corollaries 2.23 (p. 10) and 2.25 (p. 11) give locally short posets without an omega partition. The statement and discussion of the uncountable chain in Example 2.10 span pp. 5–6. Remark 2.29 (p. 13) gives the duality convention.
- The arXiv v1 PDF locates Question 2.32, Definition 2.33 and Question 2.34 on printed page 14. The bounded-poset remark following Definition 2.33 uses a two-point chain of bottom and top, which requires distinct points.
- In Abela and Chetcuti’s Theorem 3.14 (arXiv:2609.16280v2), if a sublattice Y is join-regular in a complete lattice L and both L and the Dedekind–MacNeille completion of Y satisfy the join-infinite distributive law, the canonical extension is a lattice embedding with join-regular image in L. The locator is the theorem labelled Regular MacNeille extension in the source TeX.
- Question 2.30 on reflection cardinals, Question 2.31 on weak choice in ZF and a general criterion for ordinal skeletons or partitions of the original poset stay outside the writeback. The literature screen has the scope recorded above.
- Exact equivalence to a row in the original 34/4/11 portfolio remains unresolved. Salinas revision 2 has a separately identified approved source entry. The written mathematics carries its original attribution and does not change the portfolio counts.
- The source-family escape audit remains unfinished under #28004. The finite skeleton proof gives the literal interval and a cardinality contradiction for every permitted n. The source reconstruction and lawful enrolled observations, including variation, sensitivity and actual dependence, remain unestablished.

## ASSUMED-UNVERIFIED

Literature completeness, unavailable citation enumeration, the blocked Zenodo queries and the original MacNeille-source reading remain `ASSUMED-UNVERIFIED`. The source/literature inspection is attributed to the preregistration producers; this dossier does not turn their partial screen into an exhaustive search. Four-slot escape registration for `result` is unfinished under #28004.
