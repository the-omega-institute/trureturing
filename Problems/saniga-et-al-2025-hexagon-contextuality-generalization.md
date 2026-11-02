---
slug: saniga-et-al-2025-hexagon-contextuality-generalization
bibkey: saniga2025hexagons
doi: 10.22331/q-2025-01-20-1601
url: https://arxiv.org/abs/2312.07738v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.result
---

# The perp hyperplane refutes the three-qubit hexagon contextuality generalization

## Problem

M. Saniga, F. Holweck, C. Kelleher, A. Muller, A. Giorgetti and H. de Boutray, *Hexagons govern three-qubit contextuality*, Quantum 9 (2025) 1601, DOI 10.22331/q-2025-01-20-1601; arXiv:2312.07738v3, Section 4, `main.tex`, lines 736–740:

> The message from the above-given observations is more than obvious: the *degree of contextuality* of a contextual quantum geometry of the three-qubit $\mathcal{W}(5,2)$ whose contexts are i) all the 315 lines of the whole space $\mathcal{W}(5,2)$, ii) all the 45 lines of an elliptic quadric, iii) all the 105 lines of a hyperbolic quadric or iv) all the 15 lines of a doily is equal to the *number of lines* each of these geometries shares with a classically-embedded hexagon, with the understanding that each shared line corresponds to an unsatisfiable context. A natural generalization of these findings is that this should hold for *any* contextual sub-geometry of $\mathcal{W}(5,2)$ whose contexts are *lines*.

The next paragraph begins, “As a particular stance of this conjecture, let us consider the complement of a skew-embedded hexagon” (`main.tex`, lines 742–744), so the proposed generalization extends beyond the four named families. Definitions and source locators are also in [the literature note](../Library/FiniteGeometry/saniga2025hexagons.md).

For the formal reading, put $V=(\mathbb F_2^2)^3$. Its nonzero vectors label the canonical three-qubit Pauli observables $P_v$. Write $B$ for the binary symplectic form. Lines are the triples $\{u,v,u+v\}$ with $u,v$ nonzero, distinct and $B(u,v)=0$. Set $s(\ell)=1$ when $\prod_{q\in\ell}P_q=-I$, and $s(\ell)=0$ otherwise. For a finite family $C$ of these lines, define $d(C)=\min_{f:V\to\mathbb F_2}|\{\ell\in C:\sum_{q\in\ell}f(q)\ne s(\ell)\}|$.

Issue [#24997](https://github.com/the-omega-institute/trureturing/issues/24997) fixes `claim`: for every such $C$ with $d(C)>0$, there exists $H$ satisfying `IsClassicalHexagon` with $d(C)=|C\cap H|$. The predicate, specified below, includes all the source's classical embeddings. This claim is refuted.

## Motivation

The conjectured equality would turn a minimization over hidden-variable assignments into a geometric intersection problem. Its additional requirement on the shared lines would identify an optimal set of violated contexts. The full contained-line geometry of a point's commutation hyperplane tests whether this proposed mechanism extends to another naturally defined subgeometry.

## Gap

Issue #24997 records the preregistration author's bounded literature check:

- The v3 source retains the conjecture; the quotation above is checked directly against that source.
- The four citing-work searches recorded there, covering arXiv:2407.02928, 2610.26465, 2509.20250 and 2505.21243, reported no proof or counterexample to this generalization.
- The author distinguishes the “perpsets” of Muller et al., *New and improved bounds on the contextuality degree of multi-qubit configurations* (2024; arXiv:2305.10225), which use only lines through a pole, from all lines contained in its perp hyperplane.

`not-found-in-searched-scope`. The citing-work searches and the prior-paper comparison are reported checks, not independently reproduced literature readings.

## Route

Fix $p=IIZ$, let $S=\{q\in V\setminus\{0\}:B(p,q)=0\}$, and let $C$ be all isotropic lines contained in $S$; these are `perpPoints` and `counterexample`.

1. **Positive degree.** For every $i\in\mathrm{Fin}\,6$, `square_mem i` puts the specified Mermin–Peres square context `squareLine i` in $C$. For every assignment $f:V\to\mathbb F_2$, `square_violation f` applies the published `Square.parity_miss` of `D5/S3/QuantumContext/RankOfContextualityNonPowerTwo` through the correspondence between the square's nine observables and its labels: some context's parity differs from its sign, so a context is violated, and `counterexample_contextual` gives $d(C)>0$. The lower bound on the natural infimum uses `le_csInf` with `Set.range_nonempty`; the range contains the violation count of the zero assignment.
2. **Degree at most twelve.** For nonzero, distinct $u,v\in V$ with $B(u,v)=0$, `triple_negative` identifies the negative sign of $\{u,v,u+v\}$ with multiplication exponent two in $\mathbb Z/4\mathbb Z$. `negative_certificate_exact` identifies the negative lines of this fixed $C$ with `negativeCertificate`, and `certificate_count` gives its cardinality twelve. The zero assignment violates exactly those lines, so `counterexample_degree_le` gives $d(C)\le12$. Its use of `csInf_le` supplies the lower boundedness of the natural-number range through `OrderBot.bddBelow`.
3. **Hexagon intersections.** For any isotropic line $\ell\in\mathrm{lines}\,w$, `line_perp_profile` gives $|\ell\cap S|=3$ if $\ell\in C$ and $1$ otherwise. For any finite line family $H$ satisfying all of `IsClassicalHexagon H`, `hexagon_card H` gives $|H|=63$. The frozen incidence identity `DominatingSetAverageBound.sum_inter_card` counts the incidences of $H$ with the $31$ points of $S$. Each of those points has three incident $H$-lines. Writing $k=|C\cap H|$ gives $93=3k+(63-k)=2k+63$. Under the same hypothesis `IsClassicalHexagon H`, `hexagon_intersection_ge H` concludes $15\le k$.
4. **Contradiction.** Applying `claim` to this $C\subseteq\mathrm{lines}\,w$, using `counterexample_contextual`, would give such an $H$ with $d(C)=k$. The bounds from `counterexample_degree_le` and `hexagon_intersection_ge H` contradict that equality, yielding `result : ¬ claim`.

## Falsifier

The refutation must preserve both the source's signs and its geometric domain.

- `observable`, `B`, `points`, `lines` and `lineProduct` are reused from `LinearDoilyNegativeLineParity`, at three qubits and $w=\top$. The canonical single-qubit labels are $I,X,Z,Y$, with $Y=iXZ$. Binary assignments encode signs by $a\mapsto(-1)^a$; the zero label is excluded from every line and its assigned value has no effect.
- `IsClassicalHexagon H` requires $H\subseteq\mathrm{lines}\,w$, exactly three $H$-lines through every nonzero point, no three distinct points cyclically joined by three distinct $H$-lines, and $B(a,b)=0$ whenever $a$ and $b$ lie on $H$-lines through a common point. The source specifies “63 points and 63 lines, with three points on a line and three lines through a point, such that its smallest polygons are hexagons” (`main.tex`, line 290), and “A classically-embedded hexagon enjoys the property that *each* of its points is planar” (line 479), with planarity defined by mutual commutation in lines 477–478. Its $63$ points exhaust the $63$ nonzero ambient labels, so these properties give the source-to-predicate implication; no converse characterization is asserted. Excluding every $H$ in this broader class excludes every genuine classical embedding.
- The counterexample takes every isotropic line inside $p^\perp$, including lines not through $p$. It is not the smaller family consisting only of lines incident with the pole.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.lean`.

- **Proof.** It defines `claim : Prop` and proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/PerpHyperplaneHexagonContextualityRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:4af7cc8b63bfa269cd5b058bde8018b504639122383077dee004f3cc8f3efe90`;
- `claim`: `sha256:777a24463584308a285d2c51a22c6a0865133f87b6446f9f6a72870e09c45373`.

## Triage

Tier 1 conjecture of a 2023 preprint retained in its 2025 journal publication, preregistered in issue #24997 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that every finite isotropic line family $C$ with $d(C)>0$ admits an $H$ satisfying `IsClassicalHexagon H` and $d(C)=|C\cap H|$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and scope of the obstruction.* For $H$ satisfying all of `IsClassicalHexagon H`, the incidence equation used in `hexagon_intersection_ge H` actually gives $k=15$; the Lean lemma concludes only $k\ge15$. More generally, the same count needs only a family of isotropic lines with exactly three lines through each of the $63$ nonzero points: counting all incidences gives $3|H|=3\cdot63$, and counting incidences with $S$ gives $3k+(|H|-k)=3\cdot31$, hence $k=15$. Thus triangle-freeness and planarity are not needed for this counting obstruction. Provided the class is nonempty, minimizing the intersection over its members still gives $15$, while `counterexample_degree_le` bounds the fixed $C$'s degree by $12$. An equality theorem needs additional structure forcing every assignment to violate at least as many contexts as the intersection count; regular incidence alone supplies no such lower bound here.
- *A surviving conditional inequality.* For a genuine classically embedded $H$, assume its full line complement admits a satisfying assignment. For any line family $C$, that assignment can violate only lines of $C\cap H$, giving $d(C)\le|C\cap H|$. Saniga et al. (2025; arXiv:2312.07738v3, `main.tex`, line 471) state that “the complement of any skew-embedded copy of $\mathcal{H}$ is contextual, which is, strangely, not the case for any classically-embedded one”, citing Holweck, de Boutray and Saniga (2022), DOI 10.1038/s41598-022-13079-3. This cited premise supports the weaker upper bound, without supplying equality; it is not a theorem of this module.
- *Effect on the source.* The universal generalization cannot justify extracting an optimal violated-context set from every contextual line subgeometry. The particular families in the quoted paragraph, the skew-hexagon complements discussed in lines 742–744, and the named-family assertions in the conclusion at line 818 require their own arguments; this counterexample does not refute those restricted statements. Which further geometric hypotheses guarantee equality remains open here. The four-qubit proposals in lines 820–822 are outside the settlement's scope.

## ASSUMED-UNVERIFIED

The bounded literature check is the preregistration author's reported search, not an exhaustive worldwide novelty or priority check. The four citing works listed in #24997, the comparison with Muller et al. (2024; arXiv:2305.10225), and the original complement result of Holweck, de Boutray and Saniga (2022) were not independently reread; the conjecture and the quoted complement statement were checked in Saniga et al.'s v3 source itself.

The orchestrator's exhaustive $2^{31}$-assignment calculation of $d(C)=12$ reported in #24997 is not part of this dossier and was not reproduced here. Every statement in “Argued, not formalized” is outside the type of `result`; in particular, the exact degree twelve, the strengthened intersection equality fifteen, the extension to arbitrary three-regular isotropic line families, the complement-based upper bound and the source-to-hexagon-predicate correspondence have no separate formalized conclusion here. The formal counterexample fixes $p=IIZ$; degrees for other poles, the full space, quadrics, doilies, skew-hexagon complements and higher-qubit configurations are not established by this module.
