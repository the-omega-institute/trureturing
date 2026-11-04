---
bibkey: traversogianini2026brooks
authors: Juan Pablo Traverso Gianini
year: 2026
title: "Graph theorem Lean sources: BrooksSubcubic, chordal elimination, Menger and Hamiltonian closure"
doi: null
url: https://github.com/jtraverso
claim: "Subcubic four-clique-free graphs are three-colorable; finite chordal graphs admit perfect elimination rankings; finite Menger certificates and Hamiltonian closure and Ore degree-sum criteria hold."
strata_touched:
  - D5/S3/Combinatorics/Graph/Brooks/Coloring
  - D5/S3/Combinatorics/Graph/Brooks/Cuts
  - D5/S3/Combinatorics/Graph/Brooks/Endblock
  - D5/S3/Combinatorics/Graph/Brooks/Subcubic
  - D5/S3/Combinatorics/Graph/Chordal/Dirac
  - D5/S3/Combinatorics/Graph/Chordal/EliminationForest
  - D5/S3/Combinatorics/Graph/Chordal/Characterization
  - D5/S3/Combinatorics/Graph/Walks/MengerCertificates
  - D5/S3/Combinatorics/Graph/Walks/EdgeMengerCertificates
  - D5/S3/Combinatorics/Graph/Walks/HamiltonianClosure
license: Apache-2.0
triage: anchor
---

# Subcubic Brooks theorem: Lean source

Juan Pablo Traverso Gianini's formalization proves
`BrooksSubcubic.brooks_cubic`: for a finite vertex type, a simple graph with
`G.maxDegree ≤ 3` and `G.CliqueFree 4` has `G.Colorable 3`.
Connectedness is not a hypothesis. The theorem is the subcubic specialization
of Brooks' theorem, not a new graph-coloring theorem.

## Verified locator

Author source collection: https://github.com/jtraverso. The immutable theorem
source locators are given with each result below.

https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic

- Immutable distribution: `Vilin97/lean-pool`, commit
  `91c154506e3d08a1a25e4966c22c99212bf9df54`.
- Exact declaration: `LeanPool/BrooksSubcubic/Main.lean`, lines 28–49.
- Author source recorded in `LeanPool/projects.yml`:
  https://github.com/jtraverso/lean-pool/tree/aced439fd4161d118bf167a1e8d10553f28913fe/LeanPool/BrooksSubcubic.
- Distribution and author-source pins: Lean `v4.35.0-rc3`, Mathlib
  `c55e6e786f49471c72fbddbec5415808896aec1e`.
- Copyright headers name Juan Pablo Traverso Gianini. The full distribution
  `LICENSE` and `NOTICE` are preserved as
  `docs/reports/brooks-suppliers/lean-pool-LICENSE.txt` and
  `docs/reports/brooks-suppliers/lean-pool-NOTICE.txt`.

## Reused scope

The source closure spans `Greedy`, `NonRegular`, `ColouringGlue`,
`ComponentAttachments`, `CandidatePair`, `CutVertex`, `CutPartition`,
`Endblock`, `K4Free`, `NoCutTriple`, `GoodTriple`, `CutColouring`,
`CubicColouring`, and `Main`. Only declarations needed by the local theorem
and its consumers are retained. The local modules group these source units
while preserving their proof text and copyright headers.

Compatibility consists of removing upstream module/public-section wrappers,
redirecting imports, and using the pinned dependent-if reduction names
`dif_pos` and `dif_neg` in place of `dite_eq_left` and `dite_eq_right`.
These transplants are retired when this repository's pinned Mathlib contains
equivalent declarations, with consumers changed to direct applications.

## Mathematical source and boundary

R. L. Brooks, *On colouring the nodes of a network*, Proceedings of the
Cambridge Philosophical Society 37 (1941), 194–197,
DOI https://doi.org/10.1017/S030500410002168X, is the original theorem.
The publisher metadata supplies this bibliographic locator; the original
article text is not used as a checked proof source here.

An accessible statement and proof are in Daniel W. Cranston and Landon Rabern,
*Brooks' theorem and beyond*, https://arxiv.org/abs/1403.0479v1:
page 2 states the theorem and the minimal-counterexample reduction;
page 3 gives the greedy/good-triple proof. The published version is
Journal of Graph Theory 80 (2015), 199–225,
DOI https://doi.org/10.1002/jgt.21847.

A bound on the average degree does not by itself imply the maximum-degree
hypothesis. The hereditary sparsity application additionally needs a
low-degree deletion argument and the degree-sum identity. That interface
reduction is separate from the reused subcubic theorem. The source supplies
neither a Kostochka–Yancey critical-edge estimate nor a covering-system repair
assignment.

## Finite chordal graphs and perfect elimination orders

For V in any universe and [Finite V], the source proves
G.IsChordal iff there exists ord : V → ℕ with G.IsPEO ord.
IsPEO has exactly the fields injective and isClique_later: ord is
injective and every later-neighbor set is a clique. Empty and disconnected
graphs are included. IsChordal uses supported endpoints of an adjacency whose
unordered edge is absent from the given cycle.

### Verified source locators and selected content

The immutable distribution is
[LeanPool/lean-pool@edbe5bd56f476cc2965564676b66199f281ab714](https://github.com/LeanPool/lean-pool/tree/edbe5bd56f476cc2965564676b66199f281ab714).
All paths below are relative to that revision:

- LeanPool/Erdos81PaperIIContrib/Chordal.lean: IsChordal, IsSimplicial,
  induced-subgraph heredity, the internal Finset separator and induced-path
  arguments, minimal-separator clique, and Dirac's cardinal induction including
  its disconnected branch and internal rdirac2U argument.
- LeanPool/PaperIVCliqueTree/Basic.lean: the rooted CliqueTree structure,
  Option-valued parents, decreasing injective ranks, top bags, edge coverage
  and the ancestor/intersection calculus.
- LeanPool/PaperIVCliqueTree/PEO.lean: IsPEO, empty-base erase-and-shift
  elimination, later-neighbor bags, earliest-later-neighbor parents and ranks,
  and the clique-forest construction.
- LeanPool/PaperIVCliqueTree/Helly.lean: only top_comparable_of_mem_bag,
  isAncestor_top_of_rank_le and mem_bag_top_of_rank_le.
- LeanPool/PaperIVCliqueTree/Characterization.lean: the off-cycle-edge
  argument, deepest-top converse, IsPEO.isChordal, and
  isChordal_iff_exists_isPEO, whose exact endpoint is at lines 151–153.

The Paper IV registry records author source
[jtraverso/erdos-81-chordal-clique-partitions@ff2019f56a50cf300a6531c9f8d4a8fb1a541e3d](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/ff2019f56a50cf300a6531c9f8d4a8fb1a541e3d).
The Paper II registry records author source
[jtraverso/lean-pool@822738f3089d92c5e65a6bfb8c88c992e4699167](https://github.com/jtraverso/lean-pool/blob/822738f3089d92c5e65a6bfb8c88c992e4699167/LeanPool/Erdos81PaperIIContrib/Chordal.lean).
The Brooks distribution and author-source mappings above continue to identify
their separate older selection.

### Adaptation and dependency boundary

The donor uses Lean v4.35.0-rc3 and Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e. The host uses Lean v4.35.0 and
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. The pin mismatch excludes a
donor package dependency; the A17.2 attributed source-transplant route applies.

The host groups the selection under Chordal/Dirac, Chordal/EliminationForest
and Chordal/Characterization. Repository imports and ordinary Lean sections
replace the donor module interface. The pinned dif_pos reduces the dependent
parent choice. Walk.mk_mem_edges_iff_exists and
Walk.IsCycle.snd_ne_penultimate replace the two duplicate upstream walk proofs
by direct pinned applications. Relation.ReflTransGen.total_of_right_unique
supplies ancestor comparability for the Option-parent relation; right uniqueness
follows from Option.some_inj and equality transitivity. The consumed
IsAncestor.comparable helper retains no independent escape credit. These four
supplier adaptations preserve the original construction. Unused Set-separator
adapters, connected-only
public conclusion, leaf/branch/edge-accounting, maximum-clique, other Helly
and separate clique-tree-existence conclusions are excluded.

The host also proves correspondence with the existing Type-zero
FaalNonStable.Chordal predicate and its finite native equivalence. This
interface proof retains the same cycle, support and adjacency, Sym2 edge
orientation, strict length indices, closing endpoint normalized to zero,
consecutive-edge and wrap exclusions. The native endpoint and interface proof
are repository adaptations; they are not attributed to the donor.

### License, attribution and historical limits

Copyright and original proof authorship remain Juan Pablo Traverso Gianini's.
The selected Lean software is Apache-2.0. The complete 202-line
[LICENSE](../../docs/reports/brooks-suppliers/lean-pool-LICENSE.txt) and complete
571-line [NOTICE](../../docs/reports/brooks-suppliers/lean-pool-NOTICE.txt)
are retained. Every earlier attribution entry remains in the NOTICE; its two
generator-description lines refer to the project registry. The written Paper
IV documents use a separate CC BY-NC 4.0 license, which does not replace the
Lean software license.

This is classical known mathematics with the original proof construction;
no mathematical originality or whole-source novelty is claimed. Dirac's
1961 original full text has not been read. D. R. Fulkerson and O. A. Gross,
*Incidence matrices and interval graphs*, Pacific Journal of Mathematics
15(3) (1965), 835–855,
[DOI 10.2140/pjm.1965.15.835](https://doi.org/10.2140/pjm.1965.15.835),
section 7, pages 851–852, supplies a checked historical comparison:
Theorem 7.1 is about interval graphs and the consecutive-ones property and is
not cited as the perfect-elimination-order theorem.

Retirement requires the host actually to adopt a Mathlib pin with an equivalent
complete finite characterization, establish its native-predicate correspondence,
and migrate affected consumers and frozen records. Upstream acceptance alone
does not retire the transplant. This selection asserts no graph algorithm,
finite enumeration bound, maximal-clique classification or interval-graph
characterization.


## Finite set-form Menger certificates

Juan Pablo Traverso Gianini, *Menger's theorem*, immutable source
[jtraverso/menger-hamiltonian@35c5f684f9bfbd244bd0999ce725623ab571adb6](https://github.com/jtraverso/menger-hamiltonian/tree/35c5f684f9bfbd244bd0999ce725623ab571adb6).
The proof follows the second proof of Diestel, *Graph Theory*, Theorem 3.3.1
(Böhme, Göring, Harant), as stated by the source. This is known mathematics,
received as attributed proof source rather than an originality claim.

For every finite vertex type V, simple undirected G and arbitrary finite terminal
sets A and B, a finite vertex separator X meets the support of every A-to-B walk,
and there are exactly |X| paths from A to B with pairwise disjoint vertex supports.
Every family of m pairwise vertex-disjoint A-to-B walks satisfies m ≤ |Y| for every
separator Y. Empty V, empty terminal sets and A intersect B are included. Supports
include endpoints; separators may contain endpoints; zero-length paths are allowed.
The weak-duality clause imposes no IsPath premise. Directed, infinite-vertex,
edge-disjoint and two-terminal variants are outside this result.

The received live source slice is MengerHamilton/MengerCore.lean through
fam_of_le and the set-form Separates, card_le_of_separates and
exists_separator_and_paths proofs in MengerHamilton/Menger.lean. The internal Fam
invariant additionally requires each path to meet A only at its start and B only
at its end; splicing consumes this invariant. The public theorem projects away
these internal cleanliness clauses without restricting its inputs. One canonical
Separates predicate carries the full walk-support semantics.

The source pins Lean v4.35.0-rc3 and Mathlib
c55e6e786f49471c72fbddbec5415808896aec1e; the receiver pins Lean v4.35.0 and
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679. This mismatch excludes dependency
form. The A17.2 port preserves source proof attribution and the full license in
docs/reports/licenses/menger-hamiltonian-LICENSE.txt. Copyright (c) 2026 Juan Pablo
Traverso Gianini. The immutable recursive source tree has 31 entries and contains
no NOTICE path. The received source bytes have SHA-256:

- Menger.lean: e297798fc564b1922e22b840a925b1c58b41e31246228afd8ade5dff43c0020e.
- MengerCore.lean: 2222b03a08e2c238d415133b30ea337086d1e4c6c87b4eca29010885ded80700.
- LICENSE: c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4.

Retire the port when this repository's own pinned Mathlib contains an equivalent
entire finite set-form certificate and arbitrary-walk duality, after migrating
consumers lawfully to direct applications. An upstream acceptance event alone is
not the retirement predicate.


## Finite edge-Menger certificates

The same immutable Menger source supplies the finite edge theorem:
for every finite vertex type V, simple undirected graph G, natural k and vertices
u,v, G.IsEdgeReachable k u v if and only if there are k paths from u to v whose
unordered edge lists are pairwise disjoint. The native predicate quantifies over
every S : Set(Sym2 V) with S.encard < (k : ENat), including nonedges, and requires
reachability in G.deleteEdges S. The statement includes k=0, u=v, empty V,
edge-free graphs, adjacency and nil paths. For u=v a constant nil family works
for every k; internal vertices may be shared by different paths.

The exact received slice at commit 35c5f684f9bfbd244bd0999ce725623ab571adb6 is
MengerHamilton/MengerCore.lean lines 422–470 (lift_to_lineGraph, walk_in_edge,
lower_from_lineGraph) and MengerHamilton/Menger.lean lines 179–235
(isEdgeReachable_iff). The receiver directly consumes the first conjunct of its
public MengerCertificates.exists_separator_paths_and_weak_duality on the line
graph and local incident-edge terminal sets. It lowers walks before bypassing
them to paths, retaining edge containment. The global IsEdgeConnected wrapper
and the vertex induction are outside this selection.

The source pins, file hashes, complete Apache license, copyright, no-NOTICE
reading and source-stated Diestel Theorem 3.3.1 (Böhme, Göring, Harant)
attribution above also apply to this slice. The original Diestel text is not a
checked source here. No novelty is claimed. Retire this edge port only when the
receiver's own adopted Mathlib pin supplies the equivalent entire finite edge
theorem and affected consumers and records have migrated lawfully.


## Hamiltonian single-edge closure and Ore's theorem

The same immutable Juan Pablo Traverso Gianini source supplies the known
Bondy--Chvatal single-edge closure theorem and Ore's degree-sum theorem. For
any finite vertex type V and simple undirected graph G, distinct nonadjacent
u,v with |V| ≤ deg_G(u)+deg_G(v) satisfy
(G sup edge(u,v)).IsHamiltonian if and only if G.IsHamiltonian. The closure
statement has no external cardinality or connectedness hypothesis. For
|V| ≥ 3, the same degree-sum bound on every distinct nonadjacent pair implies
G.IsHamiltonian. The degrees are those of the original G.

The selected live source is MengerHamilton/ClosureAux.lean, the
endpoint-neighborhood counting and index-crossing argument in
exists_cycArr_of_path and the single-edge reduction in
isHamiltonian_of_sup_edge, together with Hamiltonian.lean's
isHamiltonian_sup_edge_iff and ore. The native receiver uses actual Walk
prefixes and reversed suffixes, the existing EdgeSlicing cycle-opening
theorem, and PathRingSplicing's actual cycle construction. Full support
counts establish that the two rearranged pieces span every vertex exactly
once. The donor's CycArr representation, complete-graph construction,
MengerCore, Menger, ChvatalErdosAux, Dirac and Chvatal--Erdos are not received
as part of this theorem.

The donor and receiver pins, Apache-2.0 license, authorship, copyright and
no-NOTICE source-tree reading above apply. The full software license remains
in docs/reports/licenses/menger-hamiltonian-LICENSE.txt. Historical locators
are J. A. Bondy and V. Chvatal, *A method in graph theory*, Discrete
Mathematics 15 (1976), 111--135,
[DOI 10.1016/0012-365X(76)90078-9](https://doi.org/10.1016/0012-365X(76)90078-9),
and Oystein Ore, *Note on Hamilton Circuits*, The American Mathematical
Monthly 67 (1960), 55,
[DOI 10.2307/2308928](https://doi.org/10.2307/2308928).
Crossref metadata verifies these locators; the original full papers have
not been read. This is attributed known-theorem source reception with no
originality or global theorem-absence claim.

Retire the port only when the receiver's own adopted Mathlib pin supplies
the equivalent complete finite single-edge closure and Ore statements,
after the affected consumers and frozen records migrate lawfully. Upstream
acceptance alone does not meet this retirement condition.
