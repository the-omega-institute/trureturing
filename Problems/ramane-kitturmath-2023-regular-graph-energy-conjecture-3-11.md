---
slug: ramane-kitturmath-2023-regular-graph-energy-conjecture-3-11
bibkey: ramanekitturmath2023regularenergy
doi: 10.1016/j.exco.2023.100115
url: https://doi.org/10.1016/j.exco.2023.100115
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.result
---

# Ramane–Kitturmath's regular graph energy conjecture

## Problem

H. S. Ramane and D. V. Kitturmath, *On the conjecture of Sombor energy of a graph*, Examples and Counterexamples 3 (2023), 100115, Conjecture 3.11, page 8:

> There is no regular graph with adjacency energy 2k√2, where k∈Z⁺.

The quotation is the search seat's source reading recorded in preregistration #18578; independent verification of the publisher text and the scope of the corrigendum, DOI 10.1016/j.exco.2024.100135, is `ASSUMED-UNVERIFIED`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Regular graph | A finite type `V`, `G : SimpleGraph V`, and `G.IsRegularOfDegree r` for `r : ℕ` | Includes disconnected graphs, empty vertex types and degree zero. |
| Adjacency energy | Imported `graphEnergy G MatrixKind.adjacency` | Sum of absolute adjacency eigenvalues, with multiplicities and center zero. |
| $k\in\mathbb Z^+$ | `k : ℕ` with `0 < k` | Exactly the positive integers. |
| There is no such graph | Universal inequality in `claim`; `result : claim` | Positive settlement. |
| Finite enumeration and decidability instances | Anonymous `Fintype`, `DecidableEq` and `DecidableRel` instances | Represent finite simple graphs without adding a mathematical restriction. |

The only public definition is `claim`. It states the source proposition through the definitions explicitly fixed in #18578; it introduces no replacement notion of energy or regularity.

## Motivation

The frozen motivation is `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.result`. It proves that a regular graph's adjacency energy never equals $2k\sqrt2$ for a positive integer $k$. The source note is `Library/GraphInvariants/ramanekitturmath2023regularenergy.md`.

## Gap

The source leaves the even multiples $2k\sqrt2$ as a named conjecture. Preregistration #18578 records the external statement, exact Lean conventions, proposed Galois-conjugation argument and literature screen. Within that recorded search scope, no settlement was found. This bounded search does not establish exhaustive priority or originality.

## Route

The rational adjacency characteristic polynomial splits in a real normal extension. The imported definitions `graphSpectrum` and `graphEnergy` in `D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation` retain the entire eigenvalue multiset. `spectrum_roots` uses `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues` to identify it with the characteristic roots. `degree_root` uses `SimpleGraph.adjMatrix_mulVec_const_apply_of_regular` and the characteristic-root/eigenvalue correspondence to put the positive regular degree $r$ into this multiset.

Write $S$ for the sum of its positive roots and $E$ for its absolute-value sum. Zero trace gives $E=2S$. An assumed $E=2k\sqrt2$ puts $\sqrt2$ in the splitting field. `quadratic_flip` applies `minpoly.exists_algEquiv_of_root'` to obtain an automorphism sending it to its negative; `roots_invariant` applies the roots-map identity to preserve multiplicities. The conjugated positive submultiset $T$ has sum $-S$ and still contains the fixed rational root $r$. Apply `submultiset_lower` to $T-\{r\}$: $-E\le 2(-S-r)=-E-2r$, contradicting $r>0$. Degree zero and the empty graph are covered inside `result`.

## Falsifier

A finite regular graph satisfying the forbidden equality would contradict `result` under the specified energy convention. A source correction changing the conjecture, or a prior published settlement, would change the external novelty assessment without invalidating the checked Lean proposition. No claim about general Sombor energy follows from this theorem alone.

## Evidence

The canonical module is `D5/S3/Combinatorics/SpectralGraph/RegularGraphEnergyQuadraticExclusion.lean`; its only named public declarations are `claim` and `result`. Its Scribe presents both complete formulas and attaches one `OpenProblemResolutionClaim(Proved)` to `result`. The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`.

The proof classification after expanding the delivery's helpers is `bind-only`, with `escape_witness: none`. The module's `admission_basis` is `open-problem-resolution (#18578; Proved)`; `generality: I`; `utility: none`.

| Declaration | proof_shape | escape_witness | Direct consumers |
| --- | --- | --- | --- |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.degree_root` | bind-only | none | `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.positive_energy` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.quadratic_flip` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.quadratic_irreducible` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.quadratic_flip` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` | bind-only | none | `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_invariant` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.spectrum_roots` | bind-only | none | `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` |
| `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.submultiset_lower` | bind-only | none | `_private.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.0.D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.roots_energy_exclusion` |
| `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` | bind-only | none | external named settlement |

The four-slot escape audit of `D5.S3.Combinatorics.SpectralGraph.RegularGraphEnergyQuadraticExclusion.result` is unfinished: [#20305](https://github.com/the-omega-institute/trureturing/issues/20305). Its complete dependent source reconstruction, realization bridge, variation, sensitivity and observational-dependence evidence are missing; no `declared_validated` registration is claimed.

### Experiment

[Experiment directory at commit `8b3553867db125bfd115be8090c9175223ee7247`](https://github.com/the-omega-institute/trureturing-experiments/tree/8b3553867db125bfd115be8090c9175223ee7247/docs/reports/ramane-kitturmath-2023-regular-energy-2k-sqrt2).
Command from the main repository root: `python3 ../trureturing-experiments/docs/reports/ramane-kitturmath-2023-regular-energy-2k-sqrt2/check.py`; exit 0; `check.py` SHA-256 `9b50e6641203754df2c924e100a543b1ab36b7d143adaf2bdfb2d4dc3c1d214a`. The script was checked against the pinned Git object.

Computed with floating-point eigensolvers and tolerance $10^{-8}$: 48 distinct regular spectra from all regular labelled graphs on at most eight vertices, and 4,742 distinct circulant spectra on at most 26 vertices, satisfy the excluded-energy check and the submultiset bound. Among the tested spectra, 384 have numerically integral $E_A^2$; each has numerically even integral $E_A$. The controls give $E_A(P_3)=2.828427124746$, $E_A(K_{1,2k^2})=2k\sqrt2$ for $k=1,\ldots,5$, and $E_A(C_8)=9.6568542495$. These are numerical checks with the stated scope, not uniform proofs.

## Triage

| Target item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| RK-1 | Proved; kernel-checked `result` | The exact finite-simple-graph statement, including disconnected and degree-zero cases. |
| Stronger root-polynomial exclusion | Proved; kernel-checked private `roots_energy_exclusion` | A split rational polynomial with zero root sum and a positive natural-number root has the stated $2k\sqrt2$ exclusion in a real normal field. |
| General rational symmetric matrix form with $E^2\in\mathbb Q$ | Open | No such general theorem is delivered. |
| Regular graph energy with rational square is an even integer | Open | No uniform theorem is delivered. |
| Integral-square finite sample | Computed; pinned experiment | The 384 numerically integral-square spectra have numerically even integral energy; this does not establish the rational-square statement. |
| Mathematical route | Proved; kernel-checked private helpers and `result` | The trace, conjugation, multiplicity and submultiset steps used by the settlement close in Lean. |
| Counterexample search | Computed; pinned experiment | No forbidden regular spectrum in the tested ranges. |
| Regularity boundary | Computed for $P_3$ and stars with $k=1,\ldots,5$; uniform family proved in prose below | Nonregular graphs can attain the excluded energy. |
| Delivery scope | Computed; changed-path inventory | One settlement module and its Scribe; no judge source changes. |

### What the settlement shows

The decisive mechanism is a positive rational spectral root fixed by every conjugation. Erasing that root from the conjugated positive part strengthens the lower bound enough to rule out conjugation of the energy to its negative. The private polynomial lemma makes this mechanism independent of graph connectivity; the public result needs only regularity of a finite simple graph.

Regularity cannot simply be removed. For the star $K_{1,m}$, the adjacency map preserves the span of the center vector and the normalized sum of its $m$ leaf vectors. In that orthonormal basis its matrix is $\left(\begin{smallmatrix}0&\sqrt m\\\sqrt m&0\end{smallmatrix}\right)$, so this subspace has eigenvalues $\pm\sqrt m$; the orthogonal leaf-difference subspace has eigenvalue zero. Its energy is therefore $2\sqrt m$. Taking $m=2k^2$ gives $2k\sqrt2$ for every positive integer $k$. This is a prose derivation of the uniform nonregular family, not a theorem in the delivered Lean module. It includes $P_3=K_{1,2}$.

The general rational-square matrix statement and the regular-graph even-integrality statement remain follow-up candidates. The source's other Sombor-energy results receive no additional checked conclusion here; applying the settled conjecture to them requires their precise hypotheses and the Sombor/adjacency scaling correspondence.

### Literature status

The #18578 literature screen covers searches for the title and authors, Conjecture 3.11, regular adjacency energy, $2k\sqrt2$, and graph-energy Galois/conjugation arguments. It records the classical restrictions attributed to Bapat–Pati, Pirzada–Gutman and Li–Shi–Gutman, plus the cited Sivakumar–Rajkumar–Siddiqui, Shinde–Macha–Ramane and Ramane–Chowri–Shivaprasad–Gutman papers. Their assessment is search-seat-reported. The Monastir talk and inaccessible citing papers are outside the verified reading set. Literature completeness is `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

- The verbatim publisher quotation and the corrigendum's scope are source-seat-reported; independent publisher retrieval returns HTTP 403.
- Literature completeness and priority are `ASSUMED-UNVERIFIED`.
- Numerical conclusions apply only to the pinned script's tested ranges and tolerance.
- The four-slot escape audit is unfinished under #20305.
