---
bibkey: feldmanwilce2026compactnesscliques
authors: David V. Feldman and Alexander Wilce
year: 2026
title: A Note on Compactness and Clique Size
doi: 10.48550/arXiv.2608.13320
url: https://arxiv.org/abs/2608.13320
claim: Question 1 asks for a countably compact T1 or Hausdorff space with an all-product closed orthogonality relation having finite but unbounded cliques; Section 4 gives a conditional finite-block construction.
strata_touched:
  - D5/S3/Topology/StoneCech/SectionGoodFreshClusters
  - D5/S3/Topology/StoneCech/SectionDenseSelector
  - D5/S3/Topology/StoneCech/SectionClosedGraph
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Topology/feldmanwilce2026compactnesscliques -->

# Compactness and finite unbounded cliques

David V. Feldman and Alexander Wilce, *A Note on Compactness and Clique
Size*, arXiv:2608.13320v1 [math.GN], submitted 13 August 2026. The
manuscript is dated 8 August 2026. The author names, title, manuscript
date, category and version date are present on printed page 1 of the
inspected primary text. Stable record:
https://arxiv.org/abs/2608.13320. Explicit inspected version:
https://arxiv.org/abs/2608.13320v1. This note paraphrases the supplied
primary text and does not reproduce its source or assert a journal
publication or a reuse license for the manuscript.

## Verified locator

DOI: 10.48550/arXiv.2608.13320.
URL: https://arxiv.org/abs/2608.13320.
Explicit version: https://arxiv.org/abs/2608.13320v1.

An orthogonality relation is symmetric, irreflexive and closed in the
**entire** product $X^2$ (printed pages 1–2). Remark 1(ii), printed page 3,
expressly distinguishes this from closedness only in $X^2\setminus\Delta$.
A clique is a subset whose distinct pairs are related. A relation has
finite cliques when each clique is finite; it has bounded cliques when
one finite bound works for all of them. The corresponding properties of
a space quantify over every closed orthogonality on that space.

Question 1, printed page 5, asks whether there is a countably compact
$T_1$ (or Hausdorff) space with a closed orthogonality relation having
finite but unbounded cliques. This asks for one relation witnessing the
failure of the bounded clique property, while countable compactness
ensures finite cliques by Lemma 2. Exact finite cliques of every natural
size suffice for unboundedness. The abstract on printed page 1 calls
this the main open problem. Printed page 11 instead asks Question 2
about finite open chromatic number versus bounded cliques, and Question
3 about open orthogonality-free covers of spheres; neither is Q1.

## The paper's conditional finite-block construction

Section 4, printed page 10, partitions $\omega$ into finite cells $A_n$
of size $n$ and relates distinct points in the same cell by $R_0$. A
partial section meets each cell at most once. For a free ultrafilter $u$,
the paper identifies $(u,u)\in\overline{R_0}$ with the absence of any
partial section in $u$, where the closure is in $(\beta\omega)^2$.
Its good set consists of free ultrafilters containing a partial section.
The paper explains that this set is open and dense in the free remainder,
and that bounded transversals already give a partial section in an
ultrafilter by finite partitioning.

The stated sufficient condition is a dense countably compact $Y$ of
free ultrafilters contained in that good set. Then $X=\omega\cup Y$,
with $R=\overline{R_0}\cap X^2$, would give the requested example.
It suffices for $Y$ to meet the basic clopen $\widehat S$ for every
infinite partial section $S$: every infinite subset of the base contains
such an $S$, since all cells are finite. The paper proposes this
condition; this passage does not supply the missing $Y$. The authors'
verification discussion on printed page 12 reports formalization of
the conditional construction and leaves Q1 unresolved. That is a report
about their development, not evidence of successful compilation of the
repository's new chain.

## Relationship to the arbitrary-map construction

For $q:A\to B$, a partial section is exactly a subset on which $q$ is
injective. SectionGood consists of free ultrafilters on $A$ containing
an actual such subset. The source of SectionGoodFreshClusters uses
disjoint supports and ultrafilter-monad membership readout to separate
**projected** accumulation values for arbitrary $q$, without countability
or finite fibres. SectionDenseSelector uses countability of $A$ to bound
all infinite-section tasks by the continuum, constructs their seed, and
uses the existing injective closing-off theorem to construct a
section-dense, countably compact, projection-injective $Y$.

SectionClosedGraph takes the actual subspace
$X=\operatorname{range}(\mathrm{pure}:A\to\operatorname{Ultrafilter}A)
\cup Y$, hence inherits Hausdorffness. It relates only unequal principal
points in one $q$-fibre. Section-goodness handles equal-selector diagonal
pairs and mixed pairs; injectivity of $\operatorname{Ultrafilter.map}q$
on $Y$ separates unequal selector points. These give closedness in all
$X^2$ without finite fibres. The extra projection-injectivity requirement
ensures that the principal-only relation is already closed; it is not a
premise of the paper's conditional construction, which uses the ambient
closure relation. Finite fibres separately give countable compactness
of the principal extension and finiteness of all cliques. Unbounded
finite fibre sizes give exact finite cliques of each prescribed size.

The finite-block parameter correspondence uses
$A=\sum_{n:\mathbb N}\operatorname{Fin}(n+1)$, $B=\mathbb N$, and
$q(n,i)=n$. Its fibre over $n$ is the injective image of
$\operatorname{Fin}(n+1)$ and has ncard $n+1$. This reindexes the
nonempty cells of the paper's partition. The owning graph Scribe gives
the detailed parameter and cardinal calculation. Its complete application
uses the supplied actual space and graph, including full-product closedness,
T2/T1 separation and finiteness of every clique. A clique of size N+1 rules
out any proposed uniform bound N. A transient exact Lean application checks
the parameter discharge and this final inference through the canonical
targeted build; no separate named specialization is retained. This is an
application of the existing generic theorem, and it asserts no sequential
compactness conclusion. The exact statement/axiom report, canonical Freeze
and required repository checks remain distinct from source exposition.

## Current primary-source status

The current arXiv record lists only v1 and its abstract still calls this
existence problem the main open problem. The authors' formal repository,
`DavidVFeldman/compactness-clique-size`, main commit
`1f4da701cfb6d7588a90f005fa83698e3a1b081b`, marks `MainQuestion` open in its
README. Its `RequestProject/Witness.lean` proves
`mainQuestion_of_exists_countablyCompact_dense_subset_goodSet` only from
the supplied free, section-good, section-dense and countably compact Y.
This is a check of the two primary surfaces, not a worldwide priority or
literature-exclusion claim.

## Classical methods and attribution limits

Reference [7], printed page 13, is Ginsburg and Saks, *Some applications
of ultrafilters in topology*, Pacific Journal of Mathematics 57 (1975),
403–418; printed page 8 discusses productive ultrafilter compactness.
The existing [Ginsburg–Saks note](ginsburgsaks1975ultrafilters.md)
separately locates Theorem 2.12's fixed-free-ultrafilter $D$ closing-off
construction for completely regular spaces. The existing
[Frolík note](frolik1960countablycompact.md) records direct primary
provenance for abundance, avoidance and closing-off: Lemma 2.8 requires
separable metrizable $P$ and an infinite subset of $\beta P$ with no
accumulation point in $P$; Lemma 2.9 gives a small countably compact
extension avoiding a remainder set of cardinal below $2^{\mathfrak c}$.
Frolík's attribution is independent of the Feldman–Wilce reference list.

These classical methods do not attribute the exact arbitrary-$q$
section-good supplier, constructed projection-injective selector or
graph endpoint to those papers. The exact chain is repository-derived;
the primary finite-block proposal is the application provenance. The
open status reported in this particular version establishes neither a
literature exclusion nor global priority, novelty, uniqueness or
official acceptance. No external exclusion search is claimed.
