---
slug: monterde-2022-strong-cospectral-multiplicity-bound-refutation
bibkey: monterde2022strongcospectralitytwins
doi: 10.13001/ela.2022.6721
url: https://arxiv.org/abs/2111.01265v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.result
---

# Two strongly cospectral vertices of $K_{2,3}$ exceed the multiplicity bound

## Problem

H. Monterde, *Strong cospectrality and twin vertices in weighted graphs*, Electronic Journal of Linear Algebra 38 (2022), 494–518, DOI 10.13001/ela.2022.6721; arXiv:2111.01265v2, Section 3, immediately following Theorem 3.11:

> We mention an interesting result of {\'{A}}rnad{\'{o}}ttir and Godsil which states that if $X$ is a normal Cayley graph and $n$ is the largest multiplicity of an eigenvalue of $A$, then the number of pairwise adjacency strongly cospectral vertices is bounded above by $|V (X)|/n$ \cite[Theorem 6.1]{Arn2021}. It would be interesting to check whether this bound holds for other classes of graphs, and in general whenever $M=\textbf{A}$.

This quotation is from line 727 of the downloaded v2 TeX, `ELA-sample1_copy.tex` (1444 lines, MD5 `21a1ee53b9e64ae0b3a6773aa4fdbb45`). The definitions and source locators are collected in [the literature note](../Library/GraphInvariants/monterde2022strongcospectralitytwins.md).

Issue [#21638](https://github.com/the-omega-institute/trureturing/issues/21638) fixes the general-extension reading for ordinary adjacency: for every $n\in\mathbb N$, every connected simple graph $G$ on $\operatorname{Fin}n$ with decidable adjacency, and every finite set $S$ of pairwise adjacency strongly cospectral vertices,
$|S|\le n/m(G)$.
Here $V_\theta=\{x\in\mathbb R^n:A(G)x=\theta x\}$ and
$m(G)=\operatorname{sSup}\{\dim_{\mathbb R}V_\theta:\theta\in\mathbb R\}\in\mathbb N$, the module's `maxMultiplicity`. Cardinalities and $m(G)$ are cast to the reals before division. The universal extension is refuted.

## Motivation

The proposed bound would control the size of a pairwise strongly cospectral set using only the vertex count and the largest adjacency-eigenspace dimension. Its extension beyond the stated normal Cayley setting therefore asks whether that global spectral statistic constrains the local projection relations without additional symmetry. Ordinary adjacency tests this question already within connected simple unweighted graphs.

## Gap

The bounded literature-check record in #21638 reports:

- the orchestrator's arXiv listing contains v1 and v2; its search for the bound and non-Cayley counterexamples found the source, Arnbjörg Soffía Árnadóttir and Chris Godsil's *Strongly cospectral vertices in normal Cayley graphs* (2021 preprint, arXiv:2109.07568), and an unspecified thesis by Árnadóttir, without a general counterexample;
- the search contributor reports screening the 16 citing arXiv full texts listed by Semantic Scholar without finding a settlement, and reports that Árnadóttir–Godsil (2021 preprint, arXiv:2109.07568v2) and Peter Sin's *Large sets of strongly cospectral vertices in Cayley graphs* (2022 preprint, arXiv:2207.05211) retain the Cayley hypothesis;
- the orchestrator reports no prior repository issue, module, Library note or dossier on this question within its search.

`not-found-in-searched-scope`. These attributed search outcomes do not establish exhaustive novelty.

## Route

Fix $G=K_{2,3}$ with parts $\{0,1\}$ and $\{2,3,4\}$, its real adjacency matrix $A$, and $E_\theta=\operatorname{idempotent}(G,\theta)$.

1. **Connected witness and a bounded supremum.** The imported `K23_connected` states that this fixed graph is connected. For this graph, `multiplicity_lower` states $3\le\operatorname{maxMultiplicity}(G)$. Its linear map
   $f(x_0,x_1,x_2)=(x_0,-x_0,x_1+x_2,-x_1,-x_2)$
   has image in the zero eigenspace and is injective, so that eigenspace has dimension at least three. The proof bounds every eigenspace dimension by five before applying `le_csSup`; the defining range is nonempty because it contains the dimension at $\theta=0$. Thus the supremum comparison has its required boundedness, and the argument uses only $m(G)\ge3$, not an exact multiplicity calculation.
2. **Polynomial identities for the fixed matrix.** With $Q=A^2/3-I$, `polynomial_swap` states $Qe_0=e_1$, and `adjacency_cubic` states $A^3=6A$. For every $\theta\in\mathbb R$ and every nonzero $v\in\mathbb R^5$ satisfying $Av=\theta v$, `eigenvalue_support` gives $\theta=0$ or $\theta^2=6$. For every $\theta\in\mathbb R$ and every $v\in\mathbb R^5$ satisfying $Av=\theta v$, including $v=0$, `polynomial_eigenvector` gives $Qv=(\theta^2/3-1)v$.
3. **Projection relations.** For every real $\theta$, `projector_columns` states $E_\theta e_1=(\theta^2/3-1)E_\theta e_0$. Its proof uses symmetry of this fixed $Q$, the identity $Qe_0=e_1$, and the eigenbasis formula for `idempotent`. When $\theta$ occurs in that orthonormal eigenbasis, its basis vector is nonzero, so `eigenvalue_support` makes $c=\theta^2/3-1$ equal to $-1$ or $1$. Consequently $c^2=1$ also gives the required orientation $E_\theta e_0=cE_\theta e_1$. When $\theta$ does not occur, the projector is zero and the scalar $1$ suffices. This is `strong_pair`, whose conclusion is `StronglyCospectral K23 0 1`.
4. **Every ordered pair in the set.** `pairwise_witness` states that for every $u\in\{0,1\}$ and every $v\in\{0,1\}$, `StronglyCospectral K23 u v`. Equal pairs use the scalar $1$; the reversed pair uses the fact that a real scalar of absolute value one has square one.
5. **Contradiction.** Applying `claim` to this connected graph and this set of cardinality two gives $2\le5/m(G)$. For every natural number $m$ with $3\le m$, `bound_contradiction` excludes $2\le5/(m:\mathbb R)$: the denominator is positive, so the asserted inequality gives $2m\le5$, whereas $m\ge3$ gives $2m\ge6$. These are the hypotheses used by `result : ¬ claim`.

## Falsifier

The refutation would not settle this reading if the graph, projection relation or multiplicity statistic differed from the source's. The correspondence is:

- The graph is connected, simple and unweighted. Monterde's generalized adjacency matrix is $\mathbf A=\alpha I+\beta D+\gamma A$ with $\gamma\ne0$ (v2 TeX, lines 143–150), and the source explicitly identifies ordinary adjacency as the case $\alpha=\beta=0$, $\gamma=1$ (line 161). A counterexample in this subcase excludes an unrestricted extension to all such matrices.
- `StronglyCospectral` requires, for every real $\theta$, a real $c$ with $|c|=1$ and $E_\theta e_u=cE_\theta e_v$. This is the real symmetric specialization of the source's definition (lines 170–192). The reused `idempotent` is the sum of $ww^{\mathsf T}$ over an orthonormal adjacency eigenbasis of eigenvalue $\theta$. Outside the spectrum this sum is zero. Equal vertices satisfy the relation with $c=1$, so including them in the pairwise condition imposes no extra restriction.
- `maxMultiplicity` is a natural-valued supremum of real eigenspace dimensions. For the witness the proof supplies the bound of five on the entire defining range and the lower bound of three from the zero eigenspace. In particular the denominator in the contradiction is positive; neither an empty supremum nor division by zero supplies the refutation.

The question also asks about other graph classes. Refuting its universal extension does not exclude the bound on every more restricted class.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.lean` (210 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Definitions and reuse.** It defines `StronglyCospectral`, `maxMultiplicity` and `claim`, reuses `AverageMixingTraceMaximum.idempotent`, and imports `K23` and `K23_connected` from `FiedlerResistanceInvariantWeightsRefutation`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Dynamics/StrongCospectralMultiplicityBoundRefutation.lean.json`, statement `sha256:28f575f8ba2e1970cbe3e401f9e6bbdb5991b13221f37df973accffc6e7ceaa0`.

Declaration statements:

- `result`: `sha256:3d6954579560652f24cba16ab92101788607a5a5c7d30911ef9868410becee1b`;
- `claim`: `sha256:d4da5de29aec8a40801b70eac2e4c2bcefe1d0cce9cd335e619477112d800fe4`.

## Triage

Tier 1 question of a 2022 journal paper, preregistered in issue #21638 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every $n\in\mathbb N$, every connected simple graph $G$ on $\operatorname{Fin}n$ with decidable adjacency, and every finite $S$ whose every ordered pair, including equal vertices, satisfies `StronglyCospectral G u v`, one has $|S|\le n/\operatorname{maxMultiplicity}(G)$, with real casts and division.

**Computed, not formalized** (exact rational arithmetic for the single matrix $A(K_{2,3})$):

- The characteristic polynomial is $x^3(x^2-6)$ and the matrix rank is two. Thus the zero eigenspace has dimension three, the other two eigenvalues are simple, and the maximum multiplicity is exactly three. This exact value is a computation, not the statement of `result`.
- For $Q=A^2/3-I$, multiplication gives $Q^2=I$ and $Qe_0=e_1$.
- The matrix $E_0=I-A^2/6$ is symmetric and idempotent, has rank three and satisfies $AE_0=0$. Its diagonal is $(1/2,1/2,2/3,2/3,2/3)$, and $E_0e_0=-E_0e_1$.
- For the tested graph and set, $|S|=2>5/3=n/m(G)$. No other graph is included in these computations.

**Argued, not formalized**.

- *Mechanism.* For this fixed graph, the three independent kernel directions used in `multiplicity_lower` are $e_0-e_1$, $e_2-e_3$ and $e_2-e_4$. The latter two vanish on both selected vertices, so their contribution to the global multiplicity is compatible with the opposite projection columns at those vertices. The computed zero projector has weight $1/2$ at each selected vertex, below its average diagonal value $3/5$. A largest-eigenspace dimension alone therefore supplies no uniform lower bound of $m(G)/n$ on the diagonal at the selected vertices. Connectedness does not supply that missing uniformity.
- *A sufficient condition that survives.* Consider any nonempty simple graph on $n$ vertices, its real adjacency matrix, and a largest-rank eigenspace with rank $m\ge1$ and orthogonal projector $E$. Suppose $E_{vv}=m/n$ for every $v$ in a pairwise strongly cospectral set $S$. If $S$ is empty the bound is immediate. Otherwise choose $u\in S$ and signs $s_v\in\{-1,1\}$ such that $Ee_v=s_vEe_u$. For $z=\sum_{v\in S}s_ve_v$, one has $Ez=|S|Ee_u$ and $\|z\|^2=|S|$. Since an orthogonal projection contracts the Euclidean norm, $|S|^2m/n=\|Ez\|^2\le|S|$, giving $|S|\le n/m$. Vertex transitivity supplies this sufficient condition for ordinary adjacency: every graph automorphism preserves the eigenspace and commutes with its orthogonal projector, so transitivity makes its diagonal constant, and its trace $m$ makes that constant $m/n$. This argument is not a Lean declaration in the settlement module; it does not classify all graph classes satisfying the bound.
- *Effect on the source.* The unrestricted extension asked at v2 TeX line 727 is excluded already for ordinary adjacency. The quoted normal-Cayley statement is not contradicted: $K_{2,3}$ has vertices of degrees three and two, so it is not vertex-transitive and cannot be a Cayley graph. The later twin characterization explicitly cites the preceding twin results (lines 753–758), and the product, partition and join arguments use spectral decompositions and those results rather than the proposed multiplicity bound. No later theorem in the inspected v2 text invokes the question as a hypothesis, so no dependent source theorem is identified as requiring retraction. This is a reading of those dependencies, not their formal verification.

## ASSUMED-UNVERIFIED

The literature check is bounded by the search scope recorded in #21638; it establishes neither exhaustive worldwide novelty nor priority. The arXiv version listing, Árnadóttir's thesis, the 16 citing full texts, and the reported Cayley restrictions in arXiv:2109.07568v2 and arXiv:2207.05211 were not independently reproduced here and remain attributed reports. The thesis title and version, and the individual identities of the 16 citing texts, are unspecified in the issue. Only the arXiv title, author and submission-year metadata of the two identified citing preprints was independently checked. The v2 source quotation and definition locators were checked against the downloaded TeX; the published journal text was not independently compared with it.

The exact characteristic polynomial, exact maximum multiplicity, projector calculations, uniform-diagonal argument, vertex-transitivity argument and source-dependency assessment in the two nonformal groups are not additional formal conclusions of `result`. The correspondence between the source's terminology and the Lean definitions is a mathematical reading, not a formalization of the external text. A complete classification of graph classes or generalized-adjacency parameters for which the bound survives remains open in this dossier.
