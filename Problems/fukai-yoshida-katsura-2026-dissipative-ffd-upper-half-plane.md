---
slug: fukai-yoshida-katsura-2026-dissipative-ffd-upper-half-plane
bibkey: fukaiyoshidakatsura2026dissipative
doi: 10.48550/arXiv.2603.22163
url: https://arxiv.org/abs/2603.22163v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.result
---

# Fukai–Yoshida–Katsura dissipative free-fermion root expectation

## Problem

K. Fukai, H. Yoshida and H. Katsura, *Dissipative free fermions in disguise*, arXiv:2603.22163v1, printed p. 4, after Eq. (17):

> We expect Im ũ_k > 0 to hold for general ECF graphs, as observed numerically in the boundary-driven Fendley model, so that ε̃_k ≡ 1/ũ_k satisfies Im ε̃_k < 0.

The roots ũ_k are those of the plus polynomial in Eq. (16):

$$
\widetilde P_G^+(u)=P_G(u^2)+i\gamma u P_{G\setminus K_s}(u^2).
$$

Equation (7), printed p. 3, defines the actual independent-set sum:

$$
P_G(x)=\sum_{S\in\mathcal S_G}(-x)^{|S|}\prod_{j\in S} b_j^2.
$$

The couplings are real, γ > 0 is the dissipation rate, and ECF means even-hole-free and claw-free. The simplicial clique K_s satisfies the source's closed-neighborhood condition, printed p. 3:

> Equivalently, denoting the closed neighborhood of j by Γ[j] ≡ {j} ∪ {ℓ ∈ V(G) | A_jℓ = 1}, K_s is simplicial if and only if Γ[j] \ K_s is a clique for all j ∈ K_s.

The standing exclusion after Eq. (26), printed p. 7, is retained:

> Equation (26) shows that N_k = 0 if P_G and P_{G\K_s} share the root u_k². Throughout this work, we exclude this nongeneric case [80].

The quantified statement ranges over every finite graph on Fin n, every real coupling vector, every simplicial clique, every positive γ, and every complex root. The shared-root exclusion ranges over all complex x. Neither nonzero individual couplings nor simple roots are assumed.

## Motivation

The frozen declaration `D5/S3/Quantum/SpinChains/DissipativeFreeFermionRootLocation.result` proves this expectation under the paper's standing shared-root exclusion. It supplies the root sign used in the paper's dissipative-mode interpretation.

## Gap

Issue [#12755](https://github.com/the-omega-institute/trureturing/issues/12755) preregisters this Tier 1 external expectation, its quantified statement, the multiplier route and literature check. The bounded literature check records `not-found-in-searched-scope`: arXiv v1 explicitly states the expectation; the identified citing paper arXiv:2605.31453 concerns path-product mode expansions and conserved charges. The preregistration also records checks of arXiv:2605.30007, arXiv:2606.08079 and MathDB. Semantic Scholar was rate-limited. These are bounded literature readings, not a claim of exhaustive novelty.

## Route

For a finite induced vertex domain U and a clique K contained in U, independent configurations meet K in at most one vertex. Frozen `IndependentPartitionDeletion.partition_delete` yields the clique-deletion identity by induction on K. The polynomial is the frozen partition with activities −C(b_j²)X, so the identity applies to the literal sum in Eq. (7).

Claw exclusion makes each neighboring clique `(U \ K).filter (G.Adj j)` simplicial in the remaining domain. For Im z < 0, strong induction on U constructs r with Im r > 0 and

$$
P_U(z^2)=zP_{U\setminus K}(z^2)r,
\qquad r=\frac1z-\sum_{j\in K}\frac{b_j^2}{r_j}.
$$

Each recursive multiplier has positive imaginary part, hence is nonzero. Only these multipliers and z are inverted; no partition value is divided by. Nonnegative squared couplings preserve the required imaginary-part inequality.

A root in the lower half-plane would satisfy

$$
0=zP_{G\setminus K_s}(z^2)(r+i\gamma).
$$

Both z and r+iγ are nonzero, forcing a shared root of the two independence polynomials. For a real root, real and imaginary parts force the same contradiction; the zero root is excluded by P_U(0)=1.

## Falsifier

A counterexample would be a finite graph, real couplings, simplicial clique and positive γ satisfying both ECF conditions and the no-common-root condition, with a dissipative root u satisfying Im u ≤ 0. The construction rules out both lower-half-plane and real roots without assuming that a partition evaluation is nonzero during induction.

## Evidence

`result : claim` is the single public theorem. Public definitions are `ClawFree`, `EvenHoleFree`, `Simplicial`, `P`, `Pt` and `claim`. The private content lemmas are `clique_partition`, `multiplier` and `roots_upper`; `SimplicialOn` is a private predicate. The source note is `Library/StatisticalMechanics/fukaiyoshidakatsura2026dissipative.md`. The sole direct D5 import is the frozen hard-core partition owner, whose actual independent configurations, deletion identity and evaluation transport are used on the proof's live path.

## Triage

Tier 1 external named open problem. Resolution: Proved. Admission basis: `open-problem-resolution (#12755; Proved)`. Utility: `none`.

| theorem | proof_shape | escape witness |
| --- | --- | --- |
| `clique_partition` (private) | content | Finite-clique deletion by induction, including the graph-dependent domain identity. |
| `multiplier` (private) | content | Construction of a strictly positive-imaginary multiplier by strong domain induction and claw-based inheritance of simpliciality. |
| `roots_upper` (private) | content | The multiplier on the live lower-root exclusion path, with real roots excluded separately. |
| `result` | content | The same construction after inlining the private content lemmas. |

Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

**Proved in this module.** The decisive mechanism is the identity `P_U(z²) = z P_(U\K)(z²) r` with Im r > 0 for Im z < 0. Since γ > 0, the dissipative term iγ cannot cancel this multiplier. This sign mechanism and the real-root argument settle the full quantified expectation.

**Proved in this module's private root lemma.** Even-hole-freeness is unused: `roots_upper` proves the root statement for every finite claw-free graph with a simplicial clique, positive dissipation and the same shared-root exclusion. `claim` and the public `result` retain EvenHoleFree to match the source. No companion theorem is added.

**Paper derivation; not separately formalized here.** The paper derives Im ε̃_k < 0 for ε̃_k = 1/ũ_k, Re λ ≤ 0 for the Liouvillian spectrum built from these modes, and a strictly positive gap when at least one mode is present. This settlement supplies the root sign for that derivation; the spectral representation, inverse-mode statement and gap formula are outside the Lean conclusion.

**Open in this delivery.** Without coprimality, the paper's footnote [80] gives the tuned four-vertex path with K_s = {2,3}, uniform couplings, P_G(x)=1−4x+3x² and P_(G\K_s)(x)=(1−x)². The shared root x=1 produces real dissipative roots. That example and a general classification of shared-root cases are not separately kernel-checked here; the delivered statement retains the exclusion.

**Open.** A quantitative lower bound on min Im ũ_k in terms of γ and the couplings remains outside this settlement. The sign argument alone gives no uniform quantitative gap estimate.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish worldwide priority or exclude unpublished proofs. The Liouvillian representation and spectral consequences are the paper's derivation, not additional formal conclusions of this module. Shared-root classification and quantitative root-height bounds remain open in this delivery.
