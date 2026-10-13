---
slug: tamer-et-al-2026-eight-vertex-qutrit-dimension
bibkey: tamer2026quadc5
doi: null
url: https://arxiv.org/abs/2605.12828v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/EightVertexQutritBound.result
---

# The Wagner graph and the rank-5 eight-vertex graph have no qutrit violation, so d* = 4

## Problem

U. Tamer, B. Ünal, A. Dizdar, Z. Gedik and Ö. E. Müstecaplıoğlu, *The Quad-C₅ Graph: Maximum Contextuality Gap on Eight Vertices*, arXiv:2605.12828v3, rank eight-vertex exclusivity graphs by their contextuality gap.
- For a graph G they define the dimension-restricted value η_d(G), the largest λ_max(Σ_i |v_i⟩⟨v_i|) over unit vectors v_i ∈ ℝ^d orthogonal on every edge (Eq. (13)).
- They define the minimum dimension d*(G) = min{d : η_d(G) > α(G)} (Eq. (25)).
- For the Wagner graph W and the graph ranked fifth in Table V(a), their non-convex search finds no three-dimensional value above α = 3. They mark d* = 4 for both with "†Numerically indicated; a rigorous three-dimensional upper bound is not established here."
- §IV: "A formal demonstration that d*(W) = 4 would require an independent upper bound on η₃(W)."

The verbatim statements are in [the literature note](../Library/QuantumBounds/tamer2026quadc5.md).

Issue [#16223](https://github.com/the-omega-institute/trureturing/issues/16223) fixes the reading. For G ∈ {W, G₅}, with the edge lists of Table VI:
- every realization in ℝ^d with d ≤ 3 satisfies Σ_i ⟨ψ, v_i⟩² ≤ 3‖ψ‖², that is λ_max ≤ 3;
- the value 3 is attained in ℝ³;
- some realization in ℝ⁴ exceeds 3;
- α(G) = 3.

Hence d*(G) = 4.

## Motivation

The minimum dimension separates contextuality witnesses that a single qutrit can show from those that need a four-level system or two qubits. The Wagner graph is the exclusivity graph of the CHSH expression, the standard eight-vertex benchmark, and the paper uses it as the contrast to Quad-C₅, whose qutrit value it proves exactly. Without an upper bound on η₃, the dimensional classification of the two dagger entries rests only on failed numerical searches.

## Gap

Issue #16223 records the literature check before any Lean:
- arXiv v3 is the latest version and keeps the dagger;
- an arXiv full-text search for the Wagner graph with contextuality returns only this paper, and Semantic Scholar lists no citing works;
- related works do not bound η₃ for these graphs: dimension witnessing (arXiv:2007.10746), self-testing of the CHSH graph (arXiv:2104.13035), and arXiv:1512.05048 and 2409.10179;
- the authors' code archive classifies dimensions heuristically. A later Zenodo archive (10.5281/zenodo.22324644) treats d* as a heuristic lower bound and quotes the authors that "a formal d* = 4 proof remains an open question";
- Crossref and web searches return no settlement.

`not-found-in-searched-scope`.

## Route

1. **Square lemma.** In ℝ³, unit vectors with a ⊥ b, b ⊥ c, c ⊥ d and d ⊥ a satisfy a = ±c or b = ±d. If a and c are independent, b and d both lie in the one-dimensional complement of span{a, c}.
2. **W.** The squares (0,1,5,4) and (2,3,7,6) give v₀ = ±v₅ or v₁ = ±v₄, and v₂ = ±v₇ or v₃ = ±v₆. Each of the four combinations yields an orthonormal triple and forces one more vertex onto its third ray. The witness sum becomes 2‖ψ‖² + ⟨ψ, v_i⟩² + ⟨ψ, v_j⟩² for an edge (i, j). For example, in the case v₀ = ±v₅, v₂ = ±v₇:
   - the triple is (0, 2, 6), and v₁ = ±v₆;
   - the sum is 2(Q₀ + Q₂ + Q₆) + Q₃ + Q₄, with residual edge (3, 4).
3. **G₅.** The triangle (2,5,7) gives an orthonormal basis a, b, c. The square (1,5,2,6) and the edges force one of three patterns, each again of the form 2‖ψ‖² + ⟨ψ, v_i⟩² + ⟨ψ, v_j⟩² for an edge (i, j).
4. **Closing.** Parseval for the triple and Bessel for the orthogonal pair give the sum ≤ 3‖ψ‖². Dimensions below three embed isometrically into ℝ³.
5. **Attainment and violation.**
   - The colourings (e₁,e₂,e₃,e₁,e₂,e₁,e₂,e₃) for W and (e₃,e₁,e₁,e₁,e₂,e₂,e₂,e₃) for G₅ attain 3 at ψ = e₁.
   - Integer vectors in ℝ⁴, orthogonal on every edge, give the exact values 49449/15625 for W and 846537181/276109725 for G₅, both above 3.
   - α = 3 for both graphs by finite checks.

## Falsifier

The settlement would fail if η_d were taken over complex vectors and a complex qutrit realization exceeded 3, if the edge lists differed from Table VI, or if Eq. (13) imposed conditions beyond unit norm and edge orthogonality. The module follows Eq. (13): real unit vectors, orthogonal on edges, nothing else. Coincident rays and non-orthogonal non-edges are allowed. The ℝ³ argument uses only orthogonal complements, Parseval and Bessel. Over ℂ³ it applies with rays identified up to a unit-modulus phase and overlaps |⟨ψ, v⟩|², so the bound holds for complex qutrit realizations too (not formalized).

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/EightVertexQutritBound.lean` (591 lines).
- Public declarations: `Vertex`, `E`, `W`, `G5`, `Realizes`, `overlapSq`, `score`, `UpperBound`, `UnitScores`, `eta`, `HasViolation`, `Settled`, `claim` and `result`.
- It uses Mathlib only: `EuclideanSpace`, `SimpleGraph.fromRel`, `NormedSpace.normalize`, `Submodule.finrank_add_finrank_orthogonal`, `exists_smul_eq_of_finrank_eq_one`, `OrthonormalBasis.sum_sq_inner_left`, `Orthonormal.sum_inner_products_le`, `LinearMap.isometryOfOrthonormal`, `SimpleGraph.indepNum` with `maximumIndepSet_card_eq_indepNum`, and `IsGreatest.csSup_eq`.
- It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- The escape registration `Reg/D5/S3/Quantum/Contextuality/EightVertexQutritBound.lean` was attempted and is not validated: the readout decide(Settled G) at the graph operand W stays `declared_unresolved` (source operand `Classical.choice`), and a proposition-valued readout is rejected. The audit is unfinished and tracked in issue #16263 (CLAUDE.md §3.9).

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/EightVertexQutritBound.lean.json`, statement `sha256:9d61f62b772704132d4157b8ca553681a1f87016adc0ddd378d108a37cf7a555`.

Declaration statements:
- `result`: `sha256:1e4f3c4a267b8f1bf12483a4ac9235cacf4ff4f6bff4c5e1bb5a1fc958412c95`;
- `claim`: `sha256:6b6c9d50f6caca0eb8912a58e0964a72ab00d2a8262608d10d2b0d3f2c5382ac`.

## Triage

Tier 1 question of a 2026 paper, preregistered in issue #16223 before any Lean.
`theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

Every other declaration is a definition used by `claim` or a private helper on the proof path of `result` (CLAUDE.md §3.2 「有消费的辅助声明」). Utility is `none`. The explicit witnesses are local facts inside general proofs. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for both W and G₅:
- α = 3;
- every real realization in dimension at most 3 has λ_max ≤ 3, and 3 is attained in dimension 3, so η₃ = 3;
- η₄ > 3;
- the least dimension with a violation is 4.

**Established inside the proof.**
- The square lemma in ℝ³.
- For every real qutrit realization of W or G₅ there is an edge (i, j) with Σ_k ⟨ψ, v_k⟩² = 2‖ψ‖² + ⟨ψ, v_i⟩² + ⟨ψ, v_j⟩² for every ψ, and v_i ⊥ v_j.
- The exact four-dimensional values 49449/15625 (W) and 846537181/276109725 (G₅).

**Argued, not formalized.**
- *The mechanism.* In three dimensions every four-cycle of an exclusivity graph collapses: either its two diagonals coincide as rays, or the other two do. W and G₅ are covered so densely by four-cycles (and, for G₅, a triangle) that every realization is rigidly a doubled orthonormal basis plus one orthogonal pair. The witness operator is then 3I − R with R of rank one, so its top eigenvalue is exactly the classical bound. In four dimensions a four-cycle no longer collapses, which is where the CHSH violation of W, 2 + √2, lives.
- *The witness operator.* The decomposition says that the witness operator Σ_k |v_k⟩⟨v_k| equals 2I + P_x + P_y with x ⊥ y unit vectors, so its spectrum is {3, 3, 2}. The module states the quadratic-form identity, not a spectrum.
- *Complex qutrits.* Over ℂ³ the same argument applies once rays are identified up to a unit-modulus phase and overlaps are taken as |⟨ψ, v⟩|². The square lemma, the forced third ray, Parseval and Bessel then hold with these changes, so η₃ = 3 also for complex realizations. The ℂ³ case is not formalized.
- *Rigidity.* Since the witness operator of every real qutrit realization has spectrum {3, 3, 2}, every one of them attains η₃ = 3, on a two-dimensional eigenspace. No realization falls below the classical bound, so the qutrit value of these witnesses is the same for all realizations.

**Open.**
- The exact η₃ values 1 + √5 that the paper reports numerically for the graphs ranked 2 and 4.
- Whether every eight-vertex graph whose qutrit search finds no violation has the same four-cycle rigidity.

**Effect on the paper.** Both dagger entries of Table V(a) are now theorems: the Wagner graph and the rank-5 graph need a four-dimensional system to show contextuality, and the paper's dimensional classification of its six leading graphs is complete, except for the exact qutrit values of ranks 2 and 4.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The statements in "Argued, not formalized" are not formalized.
