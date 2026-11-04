---
slug: ding-hu-2020-hyperdisk-regular-subset-finite-cover
bibkey: dinghu2020masking
doi: 10.1103/PhysRevA.102.042404
url: https://arxiv.org/abs/1909.11256v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.result
---

# A regular subset of a four-dimensional hyperdisk has no finite hyperdisk cover

## Problem

F. Ding and X. Hu, *Masking quantum information on hyperdisks*, Phys. Rev. A 102, 042404 (2020), arXiv:1909.11256v3, state in the conclusion at line 651 of `masking.tex`:

> Nevertheless, it is an open question for a nondegenerate masking machine  whether the number of hyperdisks in the set of maskable states is always finite. A related open question is whether a regular subset of a hyperdisk can be covered with finite number of hyperdisks.

The settled question is the second sentence. In the module, a hyperdisk is a set of unit vectors in `EuclideanSpace ℂ (Fin n)` represented by an orthonormal family `φ`, positive real coefficient moduli `r`, equality of the span of `φ` with the span of the set, and equality with the full unit-vector level set having those coefficient moduli. A regular subset `c` of `s` satisfies `IsHyperdisk s` and `(Submodule.span ℂ c : Set _) ∩ s = c`. The claim asks, for every natural `n` and every such `c` and `s`, for a natural `k` and a map `h : Fin k → Set (EuclideanSpace ℂ (Fin n))` such that every `h i` is a hyperdisk contained in `c` and `c = ⋃ i, h i`.

## Motivation

Hyperdisks retain the coefficient moduli of pure states while allowing all independent phases, and regular subsets are the linear-span intersections used in the paper's description of target states of masking machines. A finite-cover theorem would constrain the possible geometry of maskable-state sets. The counterexample tests that question at the level of the paper's definitions, with covers required to use hyperdisks contained in the regular subset.

## Gap

Issue [#25544](https://github.com/the-omega-institute/trureturing/issues/25544) records the preregistered question, the contained-cover convention from the paper, and a bounded literature check. The issue reports that the source question remains in arXiv v3 and that the cited structural follow-ups it checked do not answer the finite-cover question. The searched scope did not settle the universal claim.

## Route

The module fixes the four-coordinate set $𝒮 = \{x : ‖x‖ = 1 and ∀ j, ‖x j‖ = (1, 2, 3, 4)_j / √30\}$, the kernel $V = ker (x ↦ 6 x₀ + 3 x₁ + 2 x₂ + 3 x₃)$, and `counterexample = V ∩ ambient`. The lemma `ambient_hyperdisk` proves that `ambient` is a hyperdisk using the standard coordinate family and the positive radii. The lemma `regular` proves `IsRegularSubset counterexample ambient` by the two inclusions between the span intersection and the kernel intersection.

For each $a ∈ ℕ$, `parameter_bounds a` proves $−3/4 ≤ −1/2 − 1/(4(a+1)) ≤ −1/2$. Under the exact hypothesis `ht : -(3 : ℝ) / 4 ≤ t ∧ t ≤ -(1 : ℝ) / 2`, `phases_unit t ht` proves both $‖phases(t) j‖ = 1$ for every $j$ and $phases(t) 0 + phases(t) 1 + phases(t) 2 + 2 phases(t) 3 = 0$. Consequently, `family_mem a` proves that every `family a` lies in `counterexample`. If `family a = u • family b` for a complex $u$, the lemma `family_ray_injective a b u h`, with exactly that equality as hypothesis, proves $a = b$; hence the family supplies pairwise distinct complex rays.

The obstruction to larger contained hyperdisks is proved with the following hypotheses. The lemma `constant_modulus` assumes $a : Fin m → ℂ$, $r : ℝ$, and $h : ∀ u : Fin m → ℂ, (∀ p, ‖u p‖ = 1) → ‖∑ p, a p * u p‖ = r$, and concludes that for distinct $p,q$, $a p = 0$ or $a q = 0$. The lemma `span_reconstruction` assumes an orthonormal family `φ`, a vector $x$, and $x ∈ Submodule.span ℂ (Set.range φ)`, and reconstructs $x$ from its inner-product coefficients. The lemma `phase_state` assumes `ho : Orthonormal ℂ φ`, `hr : ∀ p, 0 < r p`, `hx : ‖x‖ = 1`, `hcoeff : ∀ p, ‖⟪φ p, x⟫_ℂ‖ = r p`, `hspan : x ∈ Submodule.span ℂ (Set.range φ)`, and a phase map `u` with `hu : ∀ p, ‖u p‖ = 1`; it proves that the corresponding phase combination has norm one and the same coefficient moduli.

With `_ho : Orthonormal ℂ φ`, `hr : ∀ p, 0 < r p`, and $hs : ∀ u, (∀ p, ‖u p‖ = 1) → (∑ p, ((r p : ℂ) * u p) • φ p) ∈ counterexample$, the lemma `disjoint_generators` proves that for every coordinate $j$ and distinct $p,q$, `φ p j = 0` or `φ q j = 0`. With `ho : Orthonormal ℂ φ`, `hr : ∀ p, 0 < r p`, `hd : ∀ j p q, p ≠ q → φ p j = 0 ∨ φ q j = 0`, and the same `hs`, `block_obstruction` proves $m ≤ 1$. Its proof uses the kernel equation, the scaled coordinate weights $(1,1,1,2)$, and the fact that a zero-sum block containing the fourth coordinate cannot be paired with another nonzero disjoint zero-sum block.

Finally, `hyperdisk_single_ray` assumes `hh : IsHyperdisk h`, `hc : h ⊆ counterexample`, $x ∈ h$, and $y ∈ h$, and proves $∃ u : ℂ, x = u • y$. It applies the preceding phase and block lemmas and handles the nonempty-index case needed for reconstruction. If a finite cover supplied by `claim` existed, `result` applies it to `ambient` and `counterexample`, chooses an index containing each `family a`, and uses `hyperdisk_single_ray` and `family_ray_injective` to obtain an injection $ℕ → Fin k$, contradicting the infinitude of $ℕ$.

## Falsifier

The refutation would not address the source question if the formal predicates changed its objects or cover convention. Here pure states are unit vectors, global phases remain in each set, and `IsHyperdisk` uses the full coefficient-modulus level set in the span of the supplied orthonormal family. The claim quantifies over all natural $n$, all sets $s,c$ in `EuclideanSpace ℂ (Fin n)`, and all `IsRegularSubset c s`; it requires the covering hyperdisks to be subsets of $c$. A convention allowing hyperdisks merely to contain $c$ would make the ambient hyperdisk itself a cover and would be a different proposition.

## Evidence

The canonical source is `D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.lean`.
Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Masking/HyperdiskRegularSubsetCover.lean.json`.

Declaration statements:
- `result`: `sha256:3f8ea22792de2e239b0d46588655e11f986d64473a8ac304334548ffb3db23bf`;
- `claim`: `sha256:ace3a7837a360b1ea6e19f0441b7009b04248f573126c7510f58e4572f8401c2`.

- **Proof.** The module proves `result : ¬ claim`.
- **Axioms.** `result` depends only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 open question from Ding and Hu (2020), preregistered in issue #25544 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The designated `result` is the certified refutation of the named `claim`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** The universal statement `claim` is false: it is not the case that every natural $n$, every hyperdisk $s$, and every regular subset $c$ of $s$ admit a finite family of hyperdisks contained in $c$ whose union is $c$.

**Computed, not formalized:** None.

**Argued, not formalized.**
- **Mechanism.** The kernel constraint becomes a weighted phase equation with scaled weights $(1,1,1,2)$. Independent phase variation forces distinct generators of a contained hyperdisk to have disjoint coordinate supports, while the weighted zero-sum obstruction leaves at most one generator. Thus every contained hyperdisk is confined to one complex ray, whereas the parameterized family has infinitely many pairwise distinct rays.
- **Missing structure.** A finite cover would need a contained hyperdisk with at least two independent phase generators, which would require a compatible disjoint block cancellation; the weights in this counterexample provide no such second block.
- **Nearby statements.** The paper's finite examples and its separate low-dimensional structural classifications are not consequences of this declaration and are not formalized here. The related first question about whether a nondegenerate masking machine always has finitely many hyperdisks, including the proposed masking-machine realization of this counterexample, is also not formalized here and remains outside this settlement.
- **Effect on dependent statements.** Any source argument that uses the universal finite-cover assertion as a premise must be revisited. Statements about particular finite examples or classifications that do not use that premise are unaffected by this refutation; no such statement is proved by this module.

## ASSUMED-UNVERIFIED

The literature check is bounded to the sources and citing works recorded in issue #25544; it does not establish exhaustive worldwide novelty or priority. The source's related nondegenerate-masking-machine question, the proposed isometric masking realization, optimal cover numbers for finite cases, and degenerate or completely degenerate masking machines are not formalized here. The paper's other structural claims and the cited follow-up literature were not independently reproduced beyond the readings recorded in the issue and library note. The interpretation of the symbolic mechanism beyond the exact Lean declaration is not a separate formal theorem.
