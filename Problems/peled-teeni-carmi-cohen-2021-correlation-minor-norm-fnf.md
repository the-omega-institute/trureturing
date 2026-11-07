---
slug: peled-teeni-carmi-cohen-2021-correlation-minor-norm-fnf
bibkey: peledteenicarmicohen2021minor
doi: 10.1038/s41598-021-82303-3
url: https://arxiv.org/abs/2005.12079v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.result
---

# The correlation-minor bound fails without filter normal form

## Problem

B. Y. Peled, A. Te'eni, A. Carmi and E. Cohen, *Correlation minor norms, entanglement detection and discord*, arXiv:2005.12079v2, Scientific Reports 11 (2021) 2849, states in Theorem 3 that a separable state in filter normal form satisfies the $p=\infty$ correlation-minor bound $\mathcal{M}_{h,p=\infty} \leq \frac{1}{\sqrt{Dd}}\left[\frac{D-1}{D(h-1)}\frac{d-1}{d(h-1)}\right]^{(h-1)/2}$. The source then asks whether the filter-normal-form hypothesis can be removed. In the source TeX file `CMN_16_12_20_arXiv.tex`, line 281, it says:

> As in Theorem \ref{thm_bound_p_1}, we conjecture this theorem still holds without the assumption that $\rho$ is in FNF.

The compiled Lean `claim` is the universal assertion over natural numbers $da$, $db$, and $h$ that, when $2 \leq da$, $2 \leq db$, $\max(da,db)\min(da,db) \leq h^2$, and $h \leq \min(da,db)^2$, every separable matrix $\rho$ on the product index space and every pair of `IsHermBasis` families satisfies $\operatorname{cmnInf}(h,\operatorname{corr}(\rho,a,b))\leq\operatorname{bound}(da,db,h)$. Here `IsHermBasis`, `corr`, `compound`, `cmnInf`, and `bound` are the definitions in the module, so the formal assertion has no filter-normal-form assumption.

## Motivation

The paper presents correlation-minor norms as basis-invariant quantities for entanglement detection: exceeding a separable-state upper bound is intended to certify entanglement. Theorem 3 supplies such a bound for filter-normal-form states, and the conjecture would extend that certification threshold to all separable states in unequal local dimensions. Determining whether that extension is valid matters because a bound that fails for separable states cannot be used as a universal separability threshold.

## Gap

The bounded search recorded in issue [#25435](https://github.com/the-omega-institute/trureturing/issues/25435) found no earlier repository record and no settlement in the searched literature. The latest arXiv source version retains the conjecture. The recorded citation search found five citing works by OpenAlex retrieval through Semantic Scholar and OpenCitations, including Lenny et al., arXiv:2302.00650, whose Theorem 1 retains the filter-normal-form condition; none of the searched works settles the conjecture. The recorded Zenodo search returned no correlation-minor-norm record.

`not-found-in-searched-scope`.

## Route

1. The private lemma `projectors_density (j : Fin 3)` proves `IsDensity (projectors j)` for each `j : Fin 3`. The private lemma `rho_separable` then proves `IsSeparable rho` by exhibiting four mixture weights $333/1000$, $333/1000$, $333/1000$, and $1/1000$, with the three projectors paired with the first three diagonal four-dimensional matrix units and the maximally mixed local matrices paired in the fourth term.
2. The private lemma `alice_basis` proves `IsHermBasis alice` for the four matrices $(I,Z,X,Y)/\sqrt{2}$. The private lemmas `bob_pairing_0` through `bob_pairing_15`, each for every `j : Fin 16`, establish the trace-product pairing for the sixteen Bob matrices, and `bob_basis` combines those cases with Hermiticity to prove `IsHermBasis bob`.
3. For every `j : Fin 16`, the private lemmas `correlation_row_0`, `correlation_row_1`, `correlation_row_2`, and `correlation_row_3` identify the corresponding entry of `corr rho alice bob` with `coefficients`. The private lemma `correlation_eq` combines these four row statements to prove equality of the full correlation matrix and `coefficients`.
4. The private lemma `selectedCols_injective` proves that the map `selectedCols : Fin 4 \to \{s : Finset (Fin 16) // s.card = 3\}` is injective. For every `k : Fin 4`, `minor_value` computes the determinant of the selected row `selectedRow` and selected column `selectedCols k` as the corresponding one of four rational values divided by $(\sqrt{2})^3$. The private lemma `minor_energy` sums the four squared minors and obtains $\frac{559341805929555807}{500000000000000000000}$.
5. The private lemma `row_lower` applies to any types `m`, `n`, and `t` with instances `[Fintype m]`, `[Fintype n]`, `[Fintype t]`, and `[DecidableEq n]`, any real matrix `c : Matrix m n \mathbb{R}`, any row `r : m`, any map `s : t \to n`, and any proof `hs : Function.Injective s`; it proves $\sum_k c\,r\,(s\,k)^2 \leq \lVert c\rVert^2$. Using this lemma with `c = compound 3 coefficients`, `r = selectedRow`, and `s = selectedCols`, `witness_lower` proves the squared lower bound for `cmnInf 3 (corr rho alice bob)`.
6. The private lemma `bound_value` proves `bound 2 4 3 = 3/(64\sqrt{2})`, and `numerical_gap` proves $\left(\frac{3}{64\sqrt{2}}\right)^2 < \frac{559341805929555807}{500000000000000000000}$. Finally, `result` assumes `claim`, instantiates it at $da=2$, $db=4$, and $h=3$ with the four dimension hypotheses, `rho_separable`, `alice_basis`, and `bob_basis`. Nonnegativity permits squaring the resulting norm inequality, and `witness_lower` together with `numerical_gap` gives the contradiction.

## Falsifier

The formal definitions track the source construction at the relevant level. `IsHermBasis` requires Hermitian matrices, exactly the squared local dimension many basis elements, and trace-product pairing equal to one on equal indices and zero otherwise. `corr` takes the real part of the trace against the Kronecker product, `compound` uses determinants of submatrices with increasing finite-set enumerations, and `cmnInf` is the norm of that compound matrix. The definition `bound` uses the real casts of the maximum and minimum local dimensions and the real exponent $((h:\mathbb{R})-1)/2$. The imported `IsSeparable` is a finite convex combination of product matrices whose local factors are positive semidefinite and have trace one.

The counterexample in the module has $da=2$, $db=4$, and $h=3$, satisfying the formal conditions $8 \leq 9$ and $3 \leq 4$. Its state, Alice basis, Bob basis, correlation coefficients, four selected minors, and numerical comparison are all the objects used by the compiled proof. The result is therefore a refutation of the universal no-FNF `claim`, rather than a statement about the FNF-restricted Theorem 3.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/CorrelationMinorNormFNFRefutation.lean.json`.

Declaration statements:
- `result`: `sha256:3fe7072d6440018c4e41f6f28de743362cb1f572f503cb2022ce55396ddf40f7`;
- `claim`: `sha256:a2e41b7a623e022e5349330e9f6164c3bae78a071e9b7954cd43841d9057d546`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2020 arXiv paper published in Scientific Reports (2021), preregistered in issue #25435 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the formal universal `claim` asserting the correlation-minor operator-norm bound for all natural `da`, `db`, and `h` satisfying its four dimension and order hypotheses, every separable state at those dimensions, and every pair of `IsHermBasis` families is false.

**Computed, not formalized:** None.

**Argued, not formalized.**

- **Mechanism.** Removing FNF allows local expectation components that FNF sets to zero to remain in the correlation matrix. In the displayed construction, the diagonal Bob flags and the three Alice projectors produce nonzero selected minors whose combined norm exceeds the proposed right-hand side; the missing FNF restriction is the structural condition that the counterexample exploits. Whether this is the only failure mechanism for no-FNF bounds is open.
- **Nearby statements.** The refutation does not refute the source's Theorem 3 with its FNF hypothesis. It gives no settlement of the source's separate $p=1$ conjecture, its quantum-design saturation statements, or its discord measure.
- **Effect on dependent claims.** Any use of the conjectured $p=\infty$ expression as a separability bound for arbitrary separable states must retain FNF or supply a different bound. The source's no-FNF conjectural extension is unavailable as a universal entanglement-detection threshold; the other source statements named above require their own hypotheses and are not settled by this result.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not establish exhaustive worldwide novelty or priority. The report that the journal version retains the conjecture was recorded in issue #25435 and was not independently reproduced here. The mechanism explanation, the precise FNF status of the displayed state as a separate calculation, and all consequences beyond the compiled proposition remain unverified. The source's statements outside the formal `claim` and `result` declarations are not formalized.
