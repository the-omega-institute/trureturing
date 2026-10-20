---
slug: khesin-li-2024-equivalence-class-sizes
bibkey: khesinli2024equivalence
doi: 10.48550/arXiv.2406.12083
url: https://arxiv.org/abs/2406.12083v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Codes/KhesinLiEquivalenceClasses.result
---

# Divisibility of connected encoder equivalence classes

## Problem

Khesin and Li, *Equivalence Classes of Quantum Error-Correcting Codes*, arXiv:2406.12083v1, Conjecture 7.1, state:

> For positive integers n > k, the equivalence classes of [n,k] codes with a single connected component have sizes divisible by 3^k.

The proposition concerns the labelled normalized encoders counted in Section 7. Every normalized member of the class is required to be connected, as in the figures' restriction to classes in which every graph is prime. Completeness of the operations as a characterization of physical code equivalence is a separate question, Conjecture 6.3.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive integers $n>k$ | Natural parameters in `claim`, with `0 < k` and `k < n` | Both positivity and strict inequality are retained. |
| Encoder graph with $k$ inputs and $n$ outputs | `SimpleGraph (Fin k ⊕ Fin n)` | Inputs and outputs have distinct labels. |
| Operations 1–5 of Conjecture 6.3 | `Step` | Local complementation, separate input/output permutations, modulo-two row addition and input-edge removal are explicit constructors. |
| Removed output Clifford decorations | Decoration-free carrier | Operation 6 has no graph action; this is the source's normalized convention. |
| Claim 6.4 normalized adjacency matrices | `Normalized` | No input-input or pivot-pivot edges; the first $k$ output columns form the identity block. |
| One operation followed by renormalization | `NormalizedStep`, using `Step` and `Relation.ReflTransGen RenormStep` | Normalization is required at both endpoints; an empty renormalization sequence is allowed. |
| Equivalence classes of distinct normalized encoders | `Relation.EqvGen NormalizedStep` and `classSize` | The subtype is counted by `Nat.card`; no quotient by graph isomorphism is taken. |
| A single connected component | The hypothesis that every normalized class member is `Connected` | This is the preregistered interpretation of the source's connected-class restriction. |
| Size divisible by $3^k$ | `result` proves `claim` | No additional conclusion is assumed. |

The source's XOR expression for local complementation is written literally in `Step.complement`. The consumed private correspondence `lc_source` identifies it with the existing graph operation `GraphStateMonogamyForbiddenSubgraph.lc` used in the proof.

## Motivation

The conjecture predicts a divisibility law in the authors' encoder-class tabulations. The result identifies an independent order-three motion at each input and its matched pivot. It establishes the arithmetic conclusion for all positive $k<n$, rather than extrapolating the finite tables.

Preregistration: [#19189](https://github.com/the-omega-institute/trureturing/issues/19189). The source locator and definitions are documented in [the Library note](../Library/QuantumContext/khesinli2024equivalence.md). There is no digestion atom.

## Gap

A free action must be constructed on the actual normalized class. Its coordinates must preserve normalization and class membership, commute with each other, and have no nonidentity stabilizer on a connected member. Counting arbitrary graphs or using an unrelated equivalence relation would not prove the conjecture.

## Route

Apply local complementation first at an input and then at its matched pivot. The corresponding free-output row pair rotates as $(b,c)\mapsto(c,b+c)$ over $\mathbb F_2$. The pair returns after three rotations. Distinct input-pivot pairs are nonadjacent, and the corresponding local complementations commute.

The private `connected_nonzero_row` shows that every input-pivot pair has a nonzero free-output row pair in a connected normalized graph when $k<n$. The private `action_free` uses the row readout to prove that the action of $(\mathbb Z/3\mathbb Z)^k$ is free. The proof of `result` applies the orbit decomposition through its consumed `free_action_card_dvd` helper, using Mathlib's `MulAction.selfEquivOrbitsQuotientProd`.

## Falsifier

A counterexample would be a normalized labelled graph with $0<k<n$, all normalized members of its equivalence class connected, and class cardinality not divisible by $3^k$. The kernel-checked `result` excludes such a graph under the stated definitions. A mismatch between physical code equivalence and the specified operations remains a fidelity question outside this theorem.

## Evidence

The settling declaration is `D5.S3.Quantum.Codes.KhesinLiEquivalenceClasses.result`. The public `claim` displays the complete proposition. Its Scribe theorem node also displays that proposition in full.

The numerical check is [the pinned experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/f11598580a685cb5f2b1d58e37be87f788935cb8/docs/reports/khesin-li-2024-equivalence-class-sizes-divisible). Command: `python3 check.py` in that directory; exit 0; script SHA-256 `32da32fd75c82664d399fcb308677d6470308d114059a1cbc41026ea2de87c29`. It reproduces the class-size lists for $(n,k)=(2,1),(3,1),(4,1),(5,1),(3,2),(4,2)$, with zero mixed classes. The action check has zero failures at $(2,1),(3,1),(4,1),(5,1),(3,2),(4,2),(5,2),(4,3),(5,3)$; the last three connected-encoder counts with $n=5$ are $14280$, $29970$ and $6534$ for $k=1,2,3$ respectively. These are finite computations, independent of the universal Lean conclusion.

The four-slot escape audit is unfinished: [#19215](https://github.com/the-omega-institute/trureturing/issues/19215) names both the settling result and the publicized `GeneralizedCHSHGroupDecomposition.cyclicHom_int`. No compiled registration is supplied. The missing evidence consists of faithful source-family realization, reconstruction and equivalence bridges, variation, sensitivity and observational dependence with an enrolled readout. This issue supplies no mathematical premise or registration-validation status.

## Triage

### What the settlement shows

- **Kernel-checked:** `result` proves the $3^k$ divisibility. Its consumed private statements `rotationPerm_cube`, `rotationPerm_commute`, `connected_nonzero_row`, `action_row` and `action_free` supply the order-three coordinate action, independence, nonzero rows and freeness. Connectedness and $k<n$ exclude an isolated input-pivot component. The factor three has this structural origin.
- **Proved in prose, supplemental:** the interaction with the free/free block is absorbed by $J=D+\sum_j(\Delta(b_j)+\Delta(c_j))$, where $\Delta(v)_{ab}=v_av_b$ for distinct free outputs $a,b$. One rotation changes $(b_i,c_i,D)$ to $(c_i,b_i+c_i,D+\Delta(b_i)+\Delta(b_i+c_i))$. Substitution in $J$ cancels both copies of $\Delta(b_i+c_i)$ and leaves $D+\Delta(b_i)+\Delta(c_i)$ plus the unchanged other summands. Thus $J$ is invariant. This is an algebraic explanation over $\mathbb F_2$, not a separately exported theorem of the delivered module; the delivered proof uses direct local-complementation commutation.
- **Computed, finite scope:** evaluating the pinned checker's `run` function with the `skip` rule at $(n,k)=(5,4),(6,5),(7,6)$ returns a single connected class of sizes $81$, $243$ and $729$ respectively, with zero mixed classes. Command: `python3 -i check.py`, evaluating its existing `run` function at those three pairs; exit 0. The script identity is the experiment entry above. The uniform exact-size statement for all $[n,n-1]$ encoders is not a delivered Lean theorem; it requires an additional count of connected normalized encoders with one free output.
- **Open scope:** completeness Conjecture 6.3 and the proposed class-count formulas $(n-1)!$ and $(n-2)(n-2)!$ remain unsettled by this result. The theorem settles the conjectured divisibility for the specified normalized classes; it supplies neither a class-count formula nor a completeness theorem for code equivalence.

The argument uses only local-complementation steps within the class. Its freeness mechanism applies to a connected normalized family closed under those rotations; this observation does not add a new exported theorem or remove the public claim's connected-class hypothesis. Sharpness and general exact-size classifications remain outside the delivered theorem.

## ASSUMED-UNVERIFIED

The preregistration records a literature screen of the arXiv record, Khesin's thesis, ten INSPIRE citing records, formal-conjectures and repository records. No settlement was found in that scope. Completeness of that screen is **ASSUMED-UNVERIFIED**; no exhaustive absence or originality claim is made.

The finite absence of mixed connected/disconnected classes is not a universal theorem. The identification of the specified graph classes with all physically equivalent Clifford encoders remains conditional on the source's separate completeness question.
