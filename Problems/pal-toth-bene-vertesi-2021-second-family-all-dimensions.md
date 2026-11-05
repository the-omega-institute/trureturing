---
slug: pal-toth-bene-vertesi-2021-second-family-all-dimensions
bibkey: paltothbenevertesi2021singlet
doi: 10.1103/PhysRevResearch.3.023101
url: https://arxiv.org/abs/2002.12409v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.result
---

# Second-family singlet-like data exist in every dimension

## Problem

K. F. Pál, G. Tóth, E. Bene and T. Vértesi, *Bound entangled singlet-like states for quantum metrology*, Phys. Rev. Research 3, 023101 (2021), arXiv:2002.12409v4, section “Second family of states and its quantum Fisher information,” state:

> For this family of states we have constructed analytical examples only for $d=3$ and $2^n.$ However, we believe that such states exist for all $d$.

This quotation is from line 674 of the v4 TeX source `metroboundent53.tex`. Definition 2 and its accompanying requirements are at lines 556–640; the source's analytic constructions are in the appendix “Special properties of orthogonal matrices,” lines 1196–1308. See [the literature note](../Library/Estimation/paltothbenevertesi2021singlet.md).

Issue [#25511](https://github.com/the-omega-institute/trureturing/issues/25511) fixes the question as existence of the data required by Definition 2 for every natural $d\ge2$. In the module, `claim` asserts that there exist real $d\times d$ matrices $Q^k$, real vectors $\bar q_m\in\mathbb R^d$, labels $\mu_{ij}\in\mathrm{Fin}\,d$, real coefficients $a_{ij}$ and complex vectors $s_m\in\mathbb C^{d\times d}$ satisfying all six conditions below. All indices range over $\mathrm{Fin}\,d$; the coefficient $a_{ij}$ is the source's $S_{ij}$.

Write $N_m=\#\{(i,j):a_{ij}\ne0,\ \mu_{ij}=m\}$, the module's `multiplicity`, and define the module's `tVec` by $t_m(i,j)=a_{ij}/\sqrt d$ when $a_{ij}\ne0$ and $\mu_{ij}=m$, and $t_m(i,j)=0$ otherwise. The conditions in `IsSecondFamilyData` are:

1. $(Q^k)^{\mathsf T}Q^k=I_d$ for every $k$.
2. $\sum_k\bar q_m(k)\bar q_n(k)=\delta_{mn}$ for every $m,n$.
3. $Q^k_{ij}=a_{ij}\bar q_{\mu_{ij}}(k)$ for every $i,j,k$.
4. $a_{ij}\ne0$ implies $a_{ij}^2=d/N_{\mu_{ij}}$ for every $i,j$.
5. $\sum_{i,j}\overline{s_m(i,j)}s_n(i,j)=\delta_{mn}$ for every $m,n$.
6. $(\sum_m s_ms_m^\dagger)^\Gamma=\sum_m t_mt_m^\dagger$, where $M^\Gamma_{(i,j),(i',j')}=M_{(i,j'),(i',j)}$.

The last operation is `AbsolutePPT.Bipartite.partialTranspose`. The fixed $|01\rangle_{AB}$ factor of the source's shield vectors is suppressed in these coordinates. The theorem is `result : claim`.

## Motivation

The source's Definition 2 constructs states on $\mathbb C^2_A\otimes\mathbb C^2_B\otimes\mathbb C^d_{A'}\otimes\mathbb C^d_{B'}$. From the required data, it derives positivity of their partial transpose on $BB'$ (TeX lines 650–672) and the quantum Fisher information $16\sqrt d/(1+\sqrt d)$ for $H=Z_A+Z_B$ (Observation 1, lines 171–183 and 700–714). This exceeds the separable bound $8$ for $d\ge2$. Supplying the data in every dimension closes the second family's construction gap. The Lean statement concerns the data, rather than the density operator or its quantum Fisher information.

## Gap

The bounded literature check is recorded in #25511:

- The v4 source contains the quoted belief and supplies analytic examples for $d=3$ and $d=2^n$, with $n\ge1$; these passages were checked directly in the source.
- The issue reports 22 citing records from Semantic Scholar and a search contributor's full-text checks of nine citing works, without an all-dimension construction of the second-family data.
- The preregistering orchestrator reports no matching Zenodo phrase-search record, repository record or issue-title record in the searches specified there.

`not-found-in-searched-scope`. The citation searches and the reported persistence of the belief in v1 have not been independently reproduced.

## Route

Fix a natural $d\ge2$ and identify $\mathrm{Fin}\,d$ with the cyclic group of order $d$. Every sum and difference in the following construction is modulo $d$.

1. **Orthogonal matrices and factorization.** Set $Q^k_{ij}=\delta_{j,i+k}$, $\mu_{ij}=j-i$, $a_{ij}=1$ and $\bar q_m=e_m$. For every natural $d$ and $k\in\mathrm{Fin}\,d$, `cyclic_q_orthogonal` proves $(Q^k)^{\mathsf T}Q^k=I_d$. For every natural $d$, `cyclic_q_factorization` proves the factorization for all $i,j,k\in\mathrm{Fin}\,d$, and `cyclic_qbar_orthonormal` proves orthonormality for all $m,n\in\mathrm{Fin}\,d$.
2. **Multiplicity.** For every natural $d$ and label $m\in\mathrm{Fin}\,d$, `cyclicFiberEquiv` identifies its nonzero label fiber with $\mathrm{Fin}\,d$ by $i\mapsto(i,i+m)$. Thus each fiber has $d$ elements. For $d\ge2$ and $i,j\in\mathrm{Fin}\,d$, `cyclic_multiplicity` proves $a_{ij}^2=d/N_{\mu_{ij}}$, with the nonzero denominator supplied by $d\ge2$.
3. **Shield vectors.** Set $s_m(i,j)=d^{-1/2}$ when $i+j=m$, and zero otherwise. For $d\ge2$, `cyclic_shield_orthonormal` proves their orthonormality for all labels. Its reuse of `AbsolutePPT.Bipartite.sector_basis` takes the nonzero coordinate count $2$, dimension $d\ge2$, both frequencies zero and sector labels $(0,-m)$ and $(0,-n)$, each with zeroth coordinate zero, through the coordinate equivalence $(i,j)\mapsto(i,-j)$.
4. **Partial transpose.** For every natural $d$, `cyclic_partial_transpose` proves the projector identity for these specific cyclic witnesses. At pair indices $(i,j),(i',j')$, the sum-sector condition under transposition is $i'+j=i+j'$, equivalent to $j'-i'=j-i$. These are exactly the difference labels defining $t_m$.
5. **Existence.** For $d\ge2$, `cyclic_data` collects the six requirements. `result` supplies these five witnesses for every natural $d\ge2$.

## Falsifier

The settlement would miss the source question if an orthonormal direction were unused, if the transpose acted on the wrong shield factor, or if an extra symmetry requirement were silently imposed. For $d\ge2$, `cyclicFiberEquiv` gives exactly $d$ supported pairs for every label, so all $d$ coordinate directions occur. The matrix orthogonality is the column identity stated at TeX lines 567–570. On the fixed $|01\rangle\langle01|_{AB}$ block, transposition on $BB'$ is transposition on $B'$, with the entry formula stated above. The source's shield identity at TeX lines 634–640 requires a projector identity between the $s$ and $t$ families; it does not require $s_m=t_m$.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions.lean.json`.

Declaration statements:

- `result`: `sha256:9a281fc2488266f9ae1dcf833d3c5dd5a5cd07c89516c9b0de12beb3a64e5c1a`;
- `claim`: `sha256:727fc29d8b090a08b9ace667eb9b236037a255aa70940a34d9c6cccda1769b4e`.

## Triage

Tier 1 existence belief of Pál, Tóth, Bene and Vértesi (2021), preregistered in issue #25511 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $d\ge2$, there exist $d$ real orthogonal matrices, $d$ orthonormal real vectors, a label function, real coefficients and $d$ orthonormal complex shield vectors satisfying the factorization, conditional multiplicity square law and partial-transpose projector identity specified by the six conditions in “Problem.”

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism and the role of the shield.* For every natural $d\ge2$, the specific cyclic witnesses certified by `cyclic_data` pair difference labels with sum-indexed shields; `cyclic_partial_transpose`, valid for every natural $d$, converts one equality into the other. This requires no restriction on the prime factors of $d$. Writing $P_t=\sum_m t_mt_m^\dagger$ and $P_s=\sum_m s_ms_m^\dagger$ for these witnesses, their entries at row $(0,0)$ and column $(1,1)$ are respectively $1/d$ and $d^{-1}\delta_{2,0}$, with the delta interpreted modulo $d$. Thus $P_s\ne P_t$ for every $d\ge3$, although $P_s^\Gamma=P_t$. At $d=2$, addition and subtraction coincide, so $s_m=t_m$. The source's choice $s_m=t_m$ for its tensor products of identity and Pauli $X$ matrices, justified by Observation 8 at lines 1288–1308, remains a property of that particular construction.
- *Algebraic scope.* The same formulas admit an extension to any finite abelian group $G$ of order $D\ge2$: take translations for the matrices, coordinate vectors for $\bar q$, coefficients $1$, difference labels and normalized sum-sector shields. Translations are permutations; each difference fiber and each sum sector has $D$ elements; distinct sectors are disjoint. These facts give the two orthonormal families, the factorization and the square law. The entries of $P_s^\Gamma$ and $P_t$ are respectively $D^{-1}[i+j'=i'+j]$ and $D^{-1}[j-i=j'-i']$, which agree by abelian cancellation. This verifies the six analogous equations as an ordinary argument; the compiled theorem is indexed by $\mathrm{Fin}\,d$.
- *Boundary and neighbouring questions.* At $d=1$, the singleton matrices and vectors with entry $1$, label $0$ and coefficient $1$ satisfy all six equations directly; this case lies outside `claim`. The source's Fisher-information expression becomes $8$ there, so it supplies no strict advantage over the stated separable bound. Classification of all admissible data, extremality of the resulting states and global optimality among PPT states are not settled by `result`.
- *Effect on the paper.* The witnesses supply the existence premise for the source's second-family PPT derivation and Observation 1 in every dimension $d\ge2$. The paper's density-operator and Fisher-information calculations therefore apply to these data, as source deductions rather than conclusions formalized in this module. Conjecture 1, the optimality assertion at TeX line 221, still requires an upper bound over all PPT states and remains open here. The first family's construction is unaffected.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The reported v1 reading, Semantic Scholar citation list, citing full texts, Zenodo search and preregistration repository searches have not been independently reproduced. The preregistration's full-state numerical checks concern its reflection-block construction, and its search contributor also reports exact cyclotomic checks; neither set of computations was reproduced here.

The statements in “Argued, not formalized” are not formalized. In particular, the finite-abelian-group extension and the $d=1$ boundary are ordinary arguments, and the module does not formalize the density operator, its PPT entanglement, its quantum Fisher information, ranks, noise robustness, extremality or optimality. The transfer from coordinate data to the source's quantum states uses the source's derivations and the fixed-sector identification described above.
