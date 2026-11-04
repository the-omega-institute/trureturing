---
slug: mallick-ganguly-majumdar-2026-pea-tensor-nonclosure
bibkey: mallickgangulymajumdar2026partialannihilating
doi: 10.1063/5.0274921
url: https://arxiv.org/abs/2411.19315v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.result
---

# Non-local partial entanglement annihilation is not closed under aligned tensor products

## Problem

B. Mallick, N. Ganguly and A. S. Majumdar, *On the characterization of partially entanglement breaking and annihilating channels*, arXiv:2411.19315v2; J. Math. Phys. 67, 082201 (2026), ask in Section VI, Conclusions, PDF page 16:

> We have also shown that $r$-partially entanglement breaking channels are not closed under tensor products, motivating the investigation of whether a similar property holds for $r$-partially entanglement annihilating channels.

This is the verbatim sentence in `main.tex`, line 1167, from the v2 source archive (member MD5 `02f5d47ee4475c5ba30a52b1e5931b9b`). The definitions are in Section IV.A, PDF pages 9–10, `main.tex` lines 630–632; see also [the literature note](../Library/QuantumContext/mallickgangulymajumdar2026partialannihilating.md).

Write $\operatorname{PEA}_{d,r}(E)$ for the module's `IsPEA d r E`: $E$ is a completely positive, trace-preserving complex-linear map on the matrices of $\mathbb C^d\otimes\mathbb C^d$, cannot be written as a tensor product of two individual CPTP maps, satisfies $r<d$, and sends every positive semidefinite trace-one input to a state of Schmidt number at most $r$.

Issue [#21802](https://github.com/the-omega-institute/trureturing/issues/21802) fixes the closure assertion: for every $d,r\in\mathbb N$ and every pair of complex-linear bipartite matrix maps $E,F$, $\operatorname{PEA}_{d,r}(E)$ and $\operatorname{PEA}_{d,r}(F)$ imply $\operatorname{PEA}_{d^2,r}(E\otimes_{\mathrm{aligned}}F)$. The aligned split groups $B_1B'_1\,|\,B_2B'_2$ when the two copies are $B_1B_2$ and $B'_1B'_2$. The threshold remains $r$.

This closure assertion is refuted. The source asks whether non-closure occurs; it does not assert closure. Thus refuting the registered assertion answers the source's non-closure question affirmatively.

## Motivation

The question tests whether a bound on the internal entanglement dimension of every single-use output remains valid for parallel uses across the aligned split. This matters when interpreting partial entanglement annihilation as a restriction on available high-dimensional entanglement. The definition bounds the output Schmidt number; it permits a channel to prepare an entangled state even from a separable input.

## Gap

Issue #21802 records the bounded literature check before any Lean:

- The arXiv listing and v2 TeX retain the question.
- The reported web search combining “partially entanglement annihilating”, tensor products and Schmidt number returned the source and background on partially entanglement breaking channels, without a settlement.
- Citation and publisher screening are reported in the issue, without an enumerated corpus of citing works. The issue also records no existing repository settlement.

`not-found-in-searched-scope`.

The v2 TeX comments at lines 679–706 contain a non-closure proposal and an informal proof sketch at lines 691–699. They are absent from the rendered article. The sketch considers pure outputs of Schmidt number $r$ and their tensor product, but supplies no channels realizing those outputs and does not justify a product-output identity for an arbitrary joint input. Replacement channels supply a concrete realization for which the identity is valid on every input matrix.

## Route

Set $d=3$, $r=2$, $\phi=(\lvert00\rangle+\lvert11\rangle)/\sqrt2$, $\sigma=\lvert\phi\rangle\langle\phi\rvert$, and $R(X)=\operatorname{Tr}(X)\sigma$. These are the module's fixed `phi` and `replacement`.

1. **A channel with a rank-two output.** `phi_rank` gives coefficient-matrix rank two for this normalized $\phi$. `replacement_cptp` proves CPTP for this fixed $R$, using the nine Kraus operators $\lvert\phi\rangle\langle j\rvert$ indexed by the input basis.
2. **Non-locality.** `replacement_nonlocal` proves `NonLocal replacement`. A proposed product factorization evaluated on $\lvert00\rangle\langle00\rvert$ would give $\sigma=A\otimes B$. Its diagonal entries require $A_{00}B_{00}=A_{11}B_{11}=(1/\sqrt2)^2\ne0$ and $A_{00}B_{11}=0$, which are incompatible.
3. **Membership.** For every bipartite qutrit matrix $\rho$ with $\operatorname{Tr}\rho=1$, `replacement_schmidt` gives `SchmidtNumberLE (replacement ρ) 2` by the one-term decomposition with weight one and vector $\phi$. `replacement_pea` combines this with CPTP, non-locality and $2<3$ to establish `IsPEA 3 2 replacement`, including the required bound for every positive semidefinite trace-one input.
4. **The aligned output.** For every matrix $X$ on the two-copy input, `replacement_kron` gives $(R\otimes R)(X)=\operatorname{Tr}(X)(\sigma\otimes\sigma)$. Let $\psi$ be the normalized aligned tensor of the fixed $\phi$ with itself, the module's `psi`. `tensor_output` gives $(R\otimes_{\mathrm{aligned}}R)(\lvert\psi\rangle\langle\psi\rvert)=\lvert\psi\rangle\langle\psi\rvert$. `psi_rank` gives coefficient-matrix rank four: in the $\mathrm{Fin}\,9$ coordinates the matrix is diagonal with entry $1/2$ at indices $0,1,3,4$ and zero elsewhere.
5. **Excluding a different decomposition.** For all $d,r\in\mathbb N$ and every normalized vector $u\in\mathbb C^d\otimes\mathbb C^d$, `pure_rank_le` assumes `SchmidtNumberLE (proj u) r` and concludes that the coefficient matrix of $u$ has rank at most $r$. Applying it to the positive semidefinite trace-one input and output $\lvert\psi\rangle\langle\psi\rvert$, with `tensor_output` and `psi_rank`, makes an assumed `IsPEA 9 2` imply $4\le2$. This is `tensor_not_pea`.
6. **Refutation.** `result` applies the universal `claim` at $d=3$, $r=2$, $E=F=R$, using `replacement_pea` for both hypotheses, and contradicts `tensor_not_pea`.

## Falsifier

The correspondence requires the source's output Schmidt-number condition, its non-locality condition and the registered bipartition. The module uses:

- `SchmidtNumberLE`, the existence of a finite convex decomposition into normalized pure states with nonnegative weights summing to one and coefficient-matrix ranks at most $r$; a large rank in one decomposition alone would not exclude another decomposition;
- `NonLocal`, excluding a tensor product of individual CPTP maps, with CPTP of the bipartite map separately required by `IsPEA`;
- `alignedTensor`, exchanging the middle factors and reindexing each party by $\mathrm{Fin}(d^2)$;
- the unchanged threshold $r$, and the bound on all positive semidefinite trace-one inputs.

The failure is witnessed by the output Schmidt-number condition itself, independently of whether the tensor channel satisfies the other clauses of `IsPEA`.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.lean` (253 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It uses `MatrixMap` and the finite Kraus API of `FiniteKrausChannel`, `IsCPTP` of `ChannelAssemblageLOSRRefutation`, and `coeff`, `proj` and `SchmidtNumberLE` of `TavakoliMorelliIncompleteEAM`. The pure-state decomposition step uses `positive_phase` of `UniqueBasisFormationRefutation`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/SchmidtNumber/PartiallyEntanglementAnnihilatingTensorRefutation.lean.json`, statement `sha256:629c340faa7d88f500f198ec22a86cdcdc93034999c3052a16f5a37a112e3123`.

Declaration statements:

- `result`: `sha256:fde14a3bf65ec27d118ecda36c6cc23f12590b3a61291dc7bd91a6c51f2518aa`;
- `claim`: `sha256:6d93a41a70d4ae87aaee89f186840a903fba0c44409c38e1bc977aa662e9b237`.

## Triage

Tier 1 question of a 2026 journal article, preregistered in issue #21802 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: fixed replacement-channel and coefficient-rank certificates, the existing pure-state decomposition lemma and arithmetic refute universal closure | open-problem-resolution |
| `NonLocal`, `IsPEA`, `alignedTensor`, `claim` | bind-only | none | definitions used by `claim` |
| the private vectors, replacement map and proof helpers | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal closure assertion is false: it is not the case that, for every natural $d,r$ and every pair $E,F$ satisfying `IsPEA d r`, their aligned tensor product satisfies `IsPEA (d * d) r`.

**Computed, not formalized.** Exact rational Gaussian elimination for $r=1,\dots,6$, $d=r+1$, used $D_{d,r}=\operatorname{diag}(1,\dots,1,0,\dots,0)$ with $r$ ones. For these six tested pairs, the ranks of $D_{d,r}$ were $1,2,3,4,5,6$, and those of $(D_{d,r}\otimes D_{d,r})/r$ were $1,4,9,16,25,36$. Each latter coefficient matrix had squared entry norm one. These computations concern this finite family only.

**Argued, not formalized.**

- *Mechanism and missing structure.* For the fixed $R$ and every two-copy matrix $X$, `replacement_kron` gives $(R\otimes R)(X)=\operatorname{Tr}(X)(\sigma\otimes\sigma)$. Thus even product density inputs produce the problematic output. A bound on each output's Schmidt rank supplies no bound by the same number on the product of the ranks. The definition permits preparing a pure entangled output, so restricting input correlations cannot remove this obstruction. A surviving same-threshold statement needs an additional tensor budget or a restriction on the allowed prepared states.
- *A family beyond the formal instance.* For any integers $d>r\ge2$, take $\phi_{d,r}=r^{-1/2}\sum_{j=0}^{r-1}\lvert jj\rangle$ and the replacement onto its pure density. Kraus operators $\lvert\phi_{d,r}\rangle\langle j\rvert$ have adjoint products summing to the identity, so the map is CPTP. Its constant output has a one-term decomposition of rank $r$. Non-locality follows from the same diagonal obstruction: a product output would require $A_{00}B_{00}=A_{11}B_{11}=1/r$ but $A_{00}B_{11}=0$. The aligned two-copy vector is $r^{-1}\sum_{i,j<r}\lvert(i,j)\rangle\otimes\lvert(i,j)\rangle$, with $r^2$ nonzero orthogonal Schmidt terms. A decomposition of a pure density cannot lower that rank: for any vector perpendicular to its support, the expectation is a sum of nonnegative weighted squared overlaps and equals zero, forcing every positive-weight component into the same ray. Its Schmidt number is therefore $r^2>r$. This gives a mathematical family of counterexamples, while the compiled settlement uses only $d=3,r=2$.
- *A surviving restricted statement.* For the canonical pure replacement channels of ranks $s,t$ with $2\le s,t\le r<d$, the aligned output has $st$ orthogonal Schmidt terms, each of amplitude $1/\sqrt{st}$. It is the constant output on every density input, and its pure-state decompositions have that same Schmidt rank by the preceding support argument. On input matrix units, each replacement vanishes off the diagonal and prepares its density on the diagonal; linearity makes the joint output the input trace times the tensor of the prepared densities. Tensoring the Kraus operators gives CPTP, and the entangled pure output excludes a product of individual channels. Consequently these replacements satisfy same-threshold closure precisely when $st\le r$; allowing threshold $st$ always gives the output bound for this family. This is not a bound on arbitrary joint outputs of general PEA channels.
- *Effect on the paper.* The rendered article leaves tensor closure as a question and uses no affirmative closure hypothesis in its other statements. The settlement answers the tensor-product part of the Conclusions for the registered non-local class and aligned split. It does not establish the separate topological, detection, series-concatenation or class-inclusion assertions. The other questions in `main.tex` line 1167, concerning representations, capacities and multipartite extensions, remain unsettled by this result.

## ASSUMED-UNVERIFIED

The bounded literature search and citation screening in #21802 do not establish exhaustive worldwide novelty or priority. The individual citing works and a separately hosted publisher full text have not been independently checked here; the source reading is the arXiv v2 TeX and PDF. Crossref metadata confirms the title, authors, DOI and journal reference.

The coefficient-matrix computations are finite checks. The family extension, restricted tensor-budget criterion and interpretations in “Argued, not formalized” are not additional compiled theorems. General non-local PEA tensor closure at $r=1$, and an $r^2$ output bound for general PEA channels on arbitrary correlated joint inputs, are not decided by this settlement.
