---
bibkey: corey2024multitwistgraph
authors: Daniel Corey; Wanlin Li
year: 2024
title: The Ceresa class and tropical curves of hyperelliptic type
doi: 10.1017/fms.2024.36
claim: The classical multitwist homology formula supplies a square-zero block. The appended research studies actual cover lattices and fixed contextual probes, without attributing its probe decoder to the cited paper.
license: citation-only
triage: anchor
---

# Cover monodromy, graph lattices and contextual geometric probes

## Primary sources and reading scope

[1] Daniel Corey and Wanlin Li, *The Ceresa class and tropical curves of
hyperelliptic type*, Forum of Mathematics, Sigma 12 (2024), e54.
Published online April 25, 2024. DOI: 10.1017/fms.2024.36.
https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/ceresa-class-and-tropical-curves-of-hyperelliptic-type/45FB665F25690EB975E500852FA4AFCA

The publisher's mathematical HTML was read in the earlier package and opened
again during synchronization. Section 3.1, Propositions 3.1 and 3.2, and
Section 3.3, equation (3.4), supply the multitwist sum formula, square-zero
property and cycle-pairing block in an adapted symplectic basis. The appended
ordinary proof treats arbitrary complement genera by constructing a primitive
isotropic sublattice and retaining the other homology directions. These
standard monodromy facts are not a first-discovery claim. The two-probe trace
reconstruction below is a separate derivation, not a quoted theorem of [1].

[2] Roland Bacher, Pierre de la Harpe and Tatiana Nagnibeda,
*The lattice of integral flows and the lattice of integral cuts on a finite
graph*, Bulletin de la Societe Mathematique de France 125(2) (1997), 167-198.
DOI: 10.24033/bsmf.2303.
https://www.numdam.org/articles/10.24033/bsmf.2303/

The primary bibliographic record was inspected in the earlier research,
not the complete PDF proof. The theory supplies its particular
critical-group/cycle-Gram argument directly. No successful visual PDF review
is claimed in this synchronization increment.

[3] Adam Klukowski, *Congruence subgroup property for nilpotent groups and
subsurface subgroups of Mapping Class Groups*, arXiv:2411.06867v2.
https://arxiv.org/html/2411.06867v2

Definition 3, Corollary 11 and Conjecture 13 were re-read in the primary HTML.
The conjecture asks for a congruence subgroup controlling a full simple-curve
orbit relative to a prescribed finite-index subgroup. Exact orders of cyclic
twist subgroups and reconstruction of a marked homology matrix do not provide
that full principal-kernel containment. The fixed source homomorphism and
paired joint-image factorization criterion remain necessary.

[4] Adam Klukowski, *Simple closed curves, non-kernel homology and Magnus
embedding*, Journal of Topology 18(2) (2025), e70023.
DOI: 10.1112/topo.70023. Online April 30, 2025.
https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/topo.70023
https://arxiv.org/abs/2304.13196

The earlier package inspected the primary abstract and introduction, which
state existence of unbranched covers whose homology is not spanned by
elevations of simple closed curves. The full Magnus-algebra construction
was not audited. In particular, arbitrary simple curves on the covering
surface must not be assumed to descend to permitted probes on the base.

[5] James A. Schafer, *Representing Homology Classes on Surfaces*, Canadian
Mathematical Bulletin 19(3) (1976), 373-374.
DOI: 10.4153/CMB-1976-058-4.
https://www.cambridge.org/core/journals/canadian-mathematical-bulletin/article/representing-homology-classes-on-surfaces/7BA9A0E56A179AE1480C19A91F275A91

The publisher's extract and metadata were inspected this turn, not the full
PDF proof. The original publication year is 1976; the page's 2018 date refers
to online publication. The extract situates the primitive-class realization
problem for oriented surfaces. The particular probe classes used here are
standard basis curves and their primitive band sums, so their realization
can also be constructed directly in a geometric symplectic basis.

## The synchronized geometric package, Sections 40-45

These sections retain ordinary proofs from the previously delivered package:

- A positive exponent-one multitwist has a genuine homology block Q=Z^t Z.
  Its integral return cokernel has graph-critical-group torsion. Finite-field
  rank and composite-modulus period are computed from its Smith invariants.
- A real regular cover and separating curve give the actual coset dual graph;
  the required base twist power lifts to the multitwist on all elevations.
- The characteristic mod-p homology cover gives K_(a,b), where a=p^(2h) and
  b=p^(2(g-h)). The rectangle basis gives exact all-prime rank
  (a-1-1_(l|a))(b-1-1_(l|b)) and first Smith invariant one.
- In pi/[N_p,N_p]N_p^m, each essential separating twist has exact outer order m.
  A deck-action rank comparison excludes compensating inner conjugation.
- Under the preceding centerless, outer-trivial base assumptions, a fixed
  simple target must satisfy ord(f(T_beta)) | ord(q0(beta))*epsilon_(beta,l).
  Passing these tests is not sufficient for global factorization.

These conclusions do not solve the unrestricted orbit conjecture. For m a
p-power the explicit quotient itself remains a p-group and is subject to the
existing fixed-pair nilpotent obstruction. The old package's Sections 33-38
are renumbered 40-45 to preserve the parallel Prym Sections 33-39.

## Actual spacetime sources informing Sections 52-58

Read at immutable dev 3e418b5db11201dad55230368b6c3f34b7f0a542:

- D5/S0/History/Spacetime/ArchiveCarrier.lean, full source, blob
  aac0c6b565c00dc5c0314642e700bd6f58ef3d7b. Archive contains a finite event
  set, integer time and position labels, signs/source trees, a strict partial
  causal relation, and time_lt on causal pairs. ArchiveEmbedding preserves
  attributes and reflects/preserves the causal relation. It does not define a
  Lorentz metric, Einstein equation, Ricci flow or physical cosmic topology.
- docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC.md, initial definitions
  and guarded arithmetic, blob e9f3153a0cedacb367e145cf58a5ac1877c67ca5.
  Occurrence identifiers and source identity differ; contextual complements
  depend on a specified background. The initial model is not asserted to
  make every physical distinction observable.
- docs/develop/theory/CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md, Sections 1-7,
  blob 63c9d88666230e3e754b01316fb19aa131f92758. Particularly relevant are
  the actual joint-world image, action/guard/cost descent, full future-response
  kernels, spurious paths under representative mixing, and the distinction
  between available experiments and one passive trajectory.
- D5/S3/Observer/WorldModel/TransversalFixedPoint.lean, definitions and first
  transport results, blob 9eec154b785525b03a0796081554dd48fb52bbd0. Its pairwise
  semiconjugacies deliberately do not include identity/composition laws.
  Coherent sections are extra data, and reflection needs injectivity.
- docs/develop/theory/OBSERVER_CLOSURE_SPECTRUM.md, opening definitions and
  selected later sections, blob cfebbce1e62890463d496a60a444e780b71463e6.
  Future-response completion is task-relative; postprocessing cannot recover
  distinctions already erased by the underlying observation.

Current PR summaries across contributors, including #7858 and #7850, were
also read. They distinguish exact storage and available instruments from
success scores. No claim that their entire proofs were re-audited is made.
The complete large spacetime manuscript was not read end to end, and no
whole-manuscript kernel certification is inferred from these source reads.

## New ordinary derivation: an exact context-depth threshold

Let A_Q=I+U_Q act on a marked symplectic R^(2G), with U_Q mapping the first r
b-directions to the a-directions by a symmetric r-by-r matrix Q and zero
elsewhere. U_Q^2=0. All passive power traces and characteristic polynomials
are independent of Q. No analogous claim for every periodic-point count or
integral cokernel is made.

For P_z(x)=x+<x,z>z, the baseline-subtracted one-probe trace is -v^t Q v,
where v is the relevant b-coordinate vector. In characteristic two its
complete information is exactly the diagonal of Q. This is a statement about
ALL one-probe vectors, not a failure of one chosen finite list.

Use z=b_i and w=b_j+a_i for i<j. The fixed two-probe trace difference is
D_ij=-Q_ii-Q_jj+Q_ij, while D_i=-Q_ii. Hence

Q_ii=-D_i, Q_ij=D_ij-D_i-D_j.

The construction needs no division and works over every commutative ring,
including even composite moduli. Over a characteristic-two finite field and
r>=2, maximal probe depth two is necessary and sufficient. Exactly
r(r+1)/2 scalar field readouts suffice and meet the fixed-length counting
lower bound. This is an elementary rank-one calculation and an explicit
protocol; no scientific-priority claim is made for trace tomography or
polarization. No independent external open conjecture is closed.

Experiments reset to the same unknown operator. All probes and the operator
share one marking. Simultaneous symplectic change of coordinates preserves
mixed traces; independent changes do not preserve the protocol. The probes
are simple-curve operations on the cover and need not descend to the base.
These restrictions are part of the actual task rather than free capabilities.

On the previously constructed genus-17 cover with K_(4,4) block, chosen
rectangle indices have diagonal entries four and off-diagonal entry one.
For A_k=I+kU, three differences are -4k,-4k,-7k, recovering the SIGNED k by
D_ij-D_i-D_j over Z and modulo any m. This is a marked, oriented observation;
it does not refine the unmarked unoriented homeomorphism classification.

Any such protocol that is a function of one fixed quotient action still
factors through that action. In particular a full-product joint-image
obstruction im(f,a)=F x im(a) persists after deterministic contextual readout.
One must separately verify descent through an outer-action quotient when
inner/deck ambiguity is present. Reconstructing Q does not establish
C_q subset Gamma Stab(alpha).

## Diagnostic and delivery boundaries

The previous geometric package recorded 192 graph-lattice checks, 960
finite-field ranks, 2304 period checks and eight actual cellular-cover cases.
Those were not rerun this turn and are not new computation evidence.

This turn executed an independent exact matrix script: a symbolic symmetric
2-by-2 proof check; all symmetric matrices in the five small cases
(modulus,r)=(2,2),(2,3),(3,2),(4,2),(5,2), totaling 288 reconstructions;
544 tests of EVERY single probe in the selected characteristic-two
zero-diagonal families; 51 signed integer K_(4,4) block cases and 867 modular
checks. The K_(4,4) tests use the explicitly identified adapted homology
block. They are not new cellular-cover computations, physical measurements,
or a successful hard-target mapping-class joint-image test.

Sections 52-58 are ordinary proofs. No Lean/Scribe wrapper, custom axiom,
freeze record or CI change is added for standard matrix normalization.
Existing candidate Lean/Scribe pairs are unchanged and were not compiled.
The active runtime has no Lean/lake executable. Current niche searches and
source matching do not establish exhaustive novelty or a resolution of
Klukowski Conjecture 13. Research synchronization is recorded in PR #7710.
