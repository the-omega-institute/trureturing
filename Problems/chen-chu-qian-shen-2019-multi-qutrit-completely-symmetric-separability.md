---
slug: chen-chu-qian-shen-2019-multi-qutrit-completely-symmetric-separability
bibkey: chenchuqianshen2019cs
doi: 10.1103/PhysRevA.99.032312
url: https://arxiv.org/abs/1812.04182v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.result
---

# Completely symmetric three-qutrit states need not be fully separable

## Problem

L. Chen, D. Chu, L. Qian and Y. Shen, *Separability of completely symmetric states in a multipartite system*, Phys. Rev. A 99, 032312 (2019), arXiv:1812.04182v4, Conclusion, item 2 (v4 TeX, line 1857):

> Are multi-qutrit CS states separable?

The source's Definition 1 (TeX lines 360–391) requires invariance of matrix entries under every permutation of all $2d$ ket and bra index positions, including permutations mixing ket and bra. Its multipartite convention is explicit (lines 449–452):

> For simplicity, a separable state will indicate the fully separable one in the multipartite case.

Issue [#23788](https://github.com/the-omega-institute/trureturing/issues/23788) fixes the assertion as follows. For every natural $d\ge3$, every positive semidefinite complex matrix $\rho$ of trace one on $(\mathbb C^3)^{\otimes d}$ that is completely symmetric is fully separable. Here full separability means a finite convex combination, with strictly positive real weights summing to one, of projectors onto products of unit local complex vectors. This assertion is `claim`; it is refuted.

The source definitions and locator are also recorded in [the literature note](../Library/Entropy/chenchuqianshen2019cs.md).

## Motivation

The question asks whether the linear constraints of complete index symmetry force a density matrix to admit a convex decomposition into product projectors at local dimension three. A three-party counterexample is enough to distinguish these properties and answer the universal multi-qutrit question negatively.

## Gap

The bounded literature check in #23788 records:

- a search reporting 18 citations from OpenAlex and Semantic Scholar and full-text checks of arXiv:2005.11607, 2006.15003, 2208.03236, 2209.08051, 2403.05244 and 2408.08574, and Qian–Chen–Chu, New J. Phys. 22, 033019 (2020), without a settlement of the multi-qutrit question;
- an abstract reading of K.-C. Ha's 2021 Comment, Phys. Rev. A 104, 016401, concerning the two-qutrit result, and identification of the authors' Reply, Phys. Rev. A 104, 016402;
- an arXiv title search for completely symmetric states and a repository issue search for the source identifier, without a prior settlement found in those searches.

These are attributed readings reported in the preregistration, not an exhaustive literature survey. The v4 source independently retains the quoted question. `not-found-in-searched-scope`.

## Route

Write $q(w)$ for the three letter counts of a word $w\in\{0,1,2\}^3$. The fixed matrix `state` has entries $\rho_{a,b}=y(q(a)+q(b))/471$, with the real function $y$ given by `moment`. Let $W$ denote the diagonal matrix with entries `witness`.

1. **Density and complete symmetry of the fixed instance.** `state_cs` proves complete symmetry of `state`, since a permutation of its six index positions preserves their combined counts. `gram_factor` expresses this same matrix as seven rank-one positive semidefinite terms with the nonnegative weights `gramWeight`; `state_psd` proves positivity and `state_trace` proves trace one.
2. **Support of positive-weight decompositions.** For any natural $n$, real weights $\lambda_i>0$, and complex vectors $\psi_i$ indexed by three-letter words, if $\rho=\sum_{i\in\mathrm{Fin}\,n}\lambda_i|\psi_i\rangle\langle\psi_i|$ for this fixed `state`, `decomposition_support` proves $\psi_i(a)=\psi_i(b)$ whenever $q(a)=q(b)$. Its argument is $\sum_i\lambda_i|\psi_i(a)-\psi_i(b)|^2=0$; no normalization of these vectors or weights is required by the lemma.
3. **Product vectors with that support.** For any three local complex vectors $v_0,v_1,v_2$, if their product amplitudes agree on every pair of words with equal counts, `symmetric_product_power` gives a complex scalar $c$ and a vector $x\in\mathbb C^3$ with product amplitude $c\prod_{k=0}^2x_{w_k}$ at every word $w$. The conclusion includes the zero product vector, using $c=0$; unit normalization is not a hypothesis.
4. **The separating inequality.** For nonnegative real $a,b,c$, `motzkin_nonneg` proves $a^2b+ab^2+c^3-3abc\ge0$ by three-term AM–GM. For every complex scalar $s$ and every $x\in\mathbb C^3$, `power_witness_nonneg` proves that the $W$-weighted squared amplitudes of $s x^{\otimes3}$ sum to a nonnegative number. For three local complex vectors whose product amplitudes are constant on each count class, `symmetric_product_witness_nonneg` gives the same conclusion for their product vector.
5. **Contradiction.** `state_witness_value` gives $\sum_w W_{w,w}\operatorname{Re}\rho_{w,w}=-1/471$ for the fixed `state`. A fully separable decomposition has the strictly positive weights and product vectors required above, so its weighted diagonal sum would be nonnegative. `state_entangled` excludes such a decomposition. Applying `claim` at $d=3$ to `state_psd`, `state_trace` and `state_cs` yields the contradiction in `result`.

## Falsifier

The refutation would miss the question if complete symmetry meant only permutation of whole subsystems, if separability excluded complex local factors, or if the instance lacked positivity or trace one. The definitions instead use all permutations of `Fin d ⊕ Fin d`, arbitrary complex unit local vectors, and `IsDensity`, which is precisely positive semidefiniteness together with trace one.

The separator's nonnegativity is restricted to product vectors constant on occupation classes. The proof establishes this restriction for every summand of a positive-weight decomposition of the fixed state; it does not assume that $W$ is nonnegative on arbitrary product vectors. The universal quantifier starts at $d=3$, so this settlement does not assert a two-qutrit result or a counterexample for every $d\ge4$.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/ThreeQutritCompletelySymmetricEntangled.lean.json`.

Declaration statements:

- `result`: `sha256:22d57472eda012e3e23a9b06262cf83ed2595463bc126381c9fe78cd9294d359`;
- `claim`: `sha256:6c450d42f29724a1bac6cb85bea9251fff4b86bf840ea0e9603b3941ffbe44ac`.

## Triage

Tier 1 explicitly listed open question of a 2019 paper, preregistered in issue #23788 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the universal assertion `claim` is false: it is not the case that, for every natural $d\ge3$, every completely symmetric positive semidefinite trace-one matrix on $(\mathbb C^3)^{\otimes d}$ is fully separable in the finite positive-weight sense defined above.

**Computed, not formalized** (exact rational arithmetic): the instance has rank seven and equals each of its eight partial transposes.

**Argued, not formalized.**

- *Mechanism and missing structure.* Positive semidefiniteness of the count-based matrix is insufficient for a positive mixture of product powers. For the fixed `state`, `decomposition_support` requires strictly positive real weights and equality to a sum of complex rank-one projectors; these hypotheses force every summand to be constant on count classes. For three local complex vectors with precisely that constancy, `symmetric_product_power` forces a scalar tensor cube, including the zero case. For every complex scalar and local complex vector, `power_witness_nonneg` makes the separator nonnegative on that cube. Thus a positive decomposition needs an additional positivity constraint detected by $W$, whereas `state_witness_value` is negative. Requiring this one constraint is necessary for separability with this support; its sufficiency is open.
- *Why the support restriction matters.* The product basis vector $|012\rangle$ has count tuple $(1,1,1)$, where the diagonal entry of $W$ is $-1/2$, so $W$ is not nonnegative on all product states. Its use as a separator depends on the support argument, rather than on a global product-state positivity claim.
- *A weaker conclusion that survives.* Partial transposition on a subset of parties exchanges the corresponding ket and bra positions. Such exchanges are among the permutations in complete symmetry, so a completely symmetric matrix equals each of its partial transposes. For a density matrix these transposes are therefore positive semidefinite. This argument explains why imposing positive partial transpose does not exclude the counterexample; it is not a Lean partial-transpose theorem in this module.
- *A surviving separable subclass.* The projector onto $|000\rangle$ is completely symmetric because its entry is one exactly when all six indices are zero. Its quadratic form is the squared modulus of the $000$ coordinate, so it is positive semidefinite; its sole nonzero diagonal entry is one, so its trace is one. It is a single unit product projector with weight one. Thus complete symmetry permits separable states as well as the entangled instance; a classification of the separable part remains open here.
- *Effect on the source.* The settlement answers Conclusion question 2 negatively. The distinct conditional statement at TeX lines 570–573 is “All the separable CS states in the multipartite system is S-separable.” An entangled state does not satisfy its premise and therefore does not refute it. The source states at line 1097, “All the multi-qubit CS states are separable.” This concerns local dimension two. Its statement at line 1354 is “Any CS states of rank at most $5$ are separable in the multipartite system.” The computed rank-seven instance does not contradict that restriction. The multi-qutrit question is presented as a future problem, not as an assumption of those statements. Any use of universal multi-qutrit separability as a premise is invalidated; the separate two-qutrit issue, Toeplitz conjecture, and remaining future questions are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The citation count, cited-work full-text checks, Ha Comment abstract reading, arXiv title search and repository issue search are reported in #23788 and were not independently reproduced for this dossier; the full Comment and Reply were not read. The source v4 TeX and its quoted passages were read directly.

The statements under “Computed, not formalized” and “Argued, not formalized” are not additional Lean conclusions. In particular, rank seven, invariance under partial transposition, the separable-subclass example, and the interpretation of the source's other statements are outside the type of `result`. Sufficiency of the separator inequality, counterexamples for each $d\ge4$, minimal entangled rank, and the separability of every proper reduced state remain open here. The source's other proofs and the two-qutrit correction are not certified by this settlement.
