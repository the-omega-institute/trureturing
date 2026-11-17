---
slug: mathoverflow-479815-signed-spectral-deletion
bibkey: hameed2025signedspectraldeletion
doi: null
url: https://ajc.maths.uq.edu.au/v93.p198
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SignedGraphSpectral/MO479815.result
---

# Edge deletion can increase signed-graph spectral deviation

## Problem

[MathOverflow 479815, “Change in two spectral deviations due to edge deletion in a signed graph”](https://mathoverflow.net/questions/479815), asks whether the spectral deviation

$$
\beta_A(\Sigma)=\sum_i(\lambda_i-\mu_i)^2
$$

always satisfies $\beta_A(\Sigma-e)\leq\beta_A(\Sigma)$ after deleting any edge of any finite signed graph. The two spectra are the full nonincreasing real adjacency spectra, with multiplicity, of the signed graph and its underlying graph. The deleted graph keeps the same vertex carrier. The source statement has no connectedness, non-bridge, non-isolation, dimension, or sign restriction.

## Motivation

The proposed monotonicity would control how the signed-versus-underlying spectral deviation changes under a basic graph operation. A counterexample identifies the missing hypotheses needed by any surviving monotonicity variant.

## Gap

The source question and the cited Hameed–Biju–Stanić paper, [*Spectral measures of balance for signed graphs*, Australasian Journal of Combinatorics 93(1) (2025), 198–210, equation (1)](https://ajc.maths.uq.edu.au/v93.p198), define the beta quantity, but do not settle the full universal deletion claim. The dossier's bibliographic metadata identifies this paper through `Library/Eigenstructure/hameed2025signedspectraldeletion.md`; the question being settled is the linked MathOverflow beta assertion. The preregistration is [issue #31231](https://github.com/the-omega-institute/trureturing/issues/31231). The bounded literature screen covered the source, its cited paper, and the directly relevant follow-up records arXiv:2606.11108 and arXiv:2609.11736; no complete supplier of this exact claim was found in that scope.

## Route

The Lean module uses the literal universal claim over `SimpleGraph (Fin n)`, Boolean signs on `Sym2 (Fin n)`, and actual `deleteEdges`. It proves a concrete counterexample on the paw graph with edges $01,02,12,03$, all edges negative, deleting $03$. The before matrix is the paw adjacency matrix $A$ and the after matrix is $K_3\sqcup K_1$ with adjacency matrix $B$. The proof establishes Hermitian symmetry, exact characteristic polynomials, all cubic root intervals and multiplicities, sorted full spectra, and the exact beta values

$$
\beta_{\rm before}=4(1-b)^2,\qquad \beta_{\rm after}=4,
$$

where $b\in(0,1)$ is the middle root of $x^3-x^2-3x+1$. Hence $\beta_{\rm after}-\beta_{\rm before}=4b(2-b)>0$.

## Falsifier

This route would answer a different question if it changed the vertex carrier, used a matrix-only assertion without graph and signing correspondence, discarded spectral multiplicities or ordering, assumed the cubic roots without proving existence and completeness, or replaced the source beta quantity by a trace or radius surrogate. All those obligations are part of the closed Lean proof of `result`.

## Evidence

The canonical source is `D5/S3/Combinatorics/SignedGraphSpectral/MO479815.lean`. The settling declaration is `result : ¬ claim`; the source-facing declaration is `claim : Prop`. The proof uses the pinned Mathlib Hermitian spectrum and characteristic-polynomial APIs and introduces no project axiom.

## Triage

### What the settlement shows

The unrestricted claim is refuted by a negative pendant edge: deletion can create an isolated vertex while changing both spectra, and the exact ordered spectral comparison gives a strict increase. The nearest variants that survive this witness, such as connected deletion or restrictions excluding signed bridges, remain open here. The result addresses the beta assertion only and does not settle other spectral deviations in the cited paper.

- **[refuted: Lean `result`]** The unrestricted edge-deletion monotonicity claim in MathOverflow 479815 is false.
- **[proved: Lean witness]** A negative pendant-edge deletion on the four-vertex paw graph strictly increases the source beta quantity.
- **[open]** Determine hypotheses, if any, under which a deletion monotonicity theorem survives, including connectedness or restrictions on signed bridges.
- **[open]** Classify the extremal change in beta under other graph operations and sign patterns.

## ASSUMED-UNVERIFIED

The literature screen is bounded to the sources and follow-ups listed above and does not establish exhaustive worldwide novelty or priority. The surviving restricted variants are open here.
