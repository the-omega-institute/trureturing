---
slug: andrade-severini-2018-star-graph-unitary-similarity
bibkey: andradeseverini2018qgraphs
doi: 10.1103/PhysRevA.98.062107
url: https://arxiv.org/abs/1808.01154v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.result
---

# Andrade–Severini star-graph evolution maps are unitarily similar

## Problem

F. M. Andrade and S. Severini, *Unitary equivalence between the Green's function and Schrödinger approaches for quantum graphs*, arXiv:1808.01154v2, state Claim 1 after defining the star-graph maps. In the source TeX `qgl.tex`, lines 522–530 read:

> The quantum evolution maps $U^{S}_{S_n}(k)$ and $U^{G}_{S_n}(k)$ are unitarily similar.
>
> Given the properties of these maps, there are strong reasons to believe that this claim works for every $n$. Although a proof for a general $n$ is not known, we checked this for $n=2,3,4,5$ by using Specht's theorem \cite{Book.2012.Horn}.

The formal problem defines `scatteringMatrix` and the diagonal `propagationMatrix` on the index type `Fin (n - 1) × Fin 2`. It asks whether, for every $n : \mathbb N$ with $2 \le n$, every $r : \mathrm{Fin}(n-1) \to \mathbb C$, every $r1,t1 : \mathbb C$, every $k : \mathbb R$, and every $\ell : \mathrm{Fin}(n-1) \to \mathbb R$, there is a $w$ in `Matrix.unitaryGroup (Fin (n - 1) × Fin 2) ℂ` such that

$w\, (\operatorname{scatteringMatrix}(r,r1,t1)\,\operatorname{propagationMatrix}(k,\ell))\,\operatorname{star}(w) = \operatorname{propagationMatrix}(k,\ell)\,\operatorname{scatteringMatrix}(r,r1,t1)$.

The source identifies these products as $U^S_{S_n}(k)=S_{S_n}(k)D_{S_n}(k)$ and $U^G_{S_n}(k)=D_{S_n}(k)S_{S_n}(k)$ at lines 383–405 and 472–474.

## Motivation

The Schrödinger and Green's-function constructions put the same scattering and propagation matrices in opposite orders. Unitary similarity gives a direct change of coordinates between those two evolution descriptions. In the source model, the diagonal propagation entries are $z_{ij}=e^{ik\ell_{ij}}$, while the scattering matrix contains the vertex amplitudes. Establishing the stated similarity for every star size removes the general-$n$ proof gap identified by the authors.

## Gap

The source explicitly says that a proof for general $n$ was not known and records checks only for $n=2,3,4,5$. The preregistration issue #23821 records the same statement, the universal quantifiers used here, and a bounded literature check: the cited arXiv records examined there do not state or prove Claim 1, while arXiv:2404.06628 repeats that the approaches are “unitarily equivalent” without a proof. The searched scope was recorded as `not-found-in-searched-scope`.

## Route

1. `phase_norm (k l)` proves $\lVert\exp(\mathrm I k l)\rVert=1$ for every real `k` and real `l`.
2. `propagation_unitary (k) (\ell)` applies `Matrix.diagonal_mem_unitary`, `Pi.mem_unitary_iff`, and `Unitary.mem_iff` to prove `propagationMatrix k ℓ ∈ Matrix.unitaryGroup (Fin (n - 1) × Fin 2) ℂ` for every natural `n`, real `k`, and real function `ℓ : Fin (n - 1) → ℝ`; `phase_norm k (ℓ p.1)` supplies the norm-one condition for each index `p`, and this lemma has no assumption $2 \le n$.
3. `evolution_conjugation (r r1 t1 k) (\ell)` proves the displayed conjugation identity for every natural `n`, every `r : Fin (n - 1) → ℂ`, every `r1,t1 : ℂ`, every real `k`, and every real `ℓ`; it applies `Units.mul_inv_cancel_right` to `propagationMatrix k ℓ * scatteringMatrix r r1 t1` and the unit `Unitary.toUnits ⟨propagationMatrix k ℓ, propagation_unitary k ℓ⟩`.
4. `result` introduces the hypotheses $2 \le n$, `r`, `r1`, `t1`, `k`, and `ℓ`, and chooses `w = propagationMatrix k ℓ` together with `propagation_unitary k ℓ` and `evolution_conjugation r r1 t1 k ℓ`.

## Falsifier

The settlement would not answer the source claim if the formal matrices had a different index order, if the two products were reversed, or if the phase entries were not the diagonal factors $\exp(\mathrm I k\ell(p.1))$. It also would not certify the physical scattering model if the source's amplitude relations were required: the Lean `claim` quantifies over arbitrary complex `r`, `r1`, and `t1` and does not assume those relations. The formal theorem covers only $n\ge2$; its helper lemmas also cover degenerate natural numbers, but `claim` does not assert the $n=0$ or $n=1$ cases.

## Evidence

The canonical source is `D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.lean`.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Transport/StarGraphEvolutionMapsUnitarilySimilar.lean.json`.

Declaration statements:
- `result`: `sha256:e49b6f1361d775b75126faa0e437dd14d48452240a62c1761c709d4a2ec88b70`;
- `claim`: `sha256:5a5e698624fb9147b1227b7e0275a4ad0e58aa5831568214858028337f6906d8`.

- **Proof.** `result : claim` chooses `propagationMatrix k ℓ` as the unitary witness and applies `propagation_unitary` and `evolution_conjugation`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2018 paper; preregistered in issue [#23821](https://github.com/the-omega-institute/trureturing/issues/23821) before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $n : \mathbb N$ with $2 \le n$, every `r : Fin (n - 1) → ℂ`, every `r1,t1 : ℂ`, every $k : \mathbb R$, and every `ℓ : Fin (n - 1) → ℝ$, there exists `w ∈ Matrix.unitaryGroup (Fin (n - 1) × Fin 2) ℂ` such that

$w\,(\operatorname{scatteringMatrix}(r,r1,t1)\,\operatorname{propagationMatrix}(k,\ell))\,\operatorname{star}(w) = \operatorname{propagationMatrix}(k,\ell)\,\operatorname{scatteringMatrix}(r,r1,t1)$.

**Computed, not formalized:** Andrade and Severini checked unitary similarity by Specht's theorem for $n=2,3,4,5$.

**Argued, not formalized.** The same conjugation calculation applies to any square complex matrix paired with a diagonal unitary phase matrix, but that broader schema is not a declaration of this module. The formal result does not prove that `scatteringMatrix` is unitary, nor that either product is unitary under the source's vertex-scattering constraints; those physical amplitude relations are absent from `claim`. Unitary similarity supplies a route to equality of characteristic data and transported eigenspaces, but the source's eigenvalue theorem appears before Claim 1 and is not re-proved here; its eigenvector corollary, Green-function formulas, pole interpretation, and trace formula are also not formalized here. The source's statement that the two approaches are unitarily equivalent is settled for the Lean-defined matrices; the additional physical and Green-function conclusions remain outside this result. No uniqueness or necessity of the witness `propagationMatrix k ℓ` is asserted.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and citation records recorded in issue #23821 and does not establish exhaustive worldwide novelty or priority. The source's physical boundary-condition relations, the eigenvalue and Green-function statements, and the broader matrix schema described under argued consequences are not formalized by this settlement. Any claim about quantum graphs beyond the exact Lean definitions and quantifiers remains unverified here.
