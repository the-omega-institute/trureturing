---
slug: gutkin-2013-orthostochastic-dimension-refutation
bibkey: gutkin2013orthostochastic
doi: 10.1016/j.geomphys.2013.06.009
url: https://arxiv.org/abs/1301.2537v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.result
---

# The d-orthostochastic dimension is not eventually bounded by 3

## Problem

E. Gutkin, *On a multi-dimensional generalization of the notions of orthostochastic and unistochastic matrices*, arXiv:1301.2537v1, Conjecture 1:

> Denote by $d_{\min}(n)$ the smallest value of $d$ such that the set of $d$-orthostochastic matrices coincides with $\B_n$. Then there exists $n_0$ such that for $n\ge n_0$ we have $2 \le d_{\min}(n) \le 3.$

A bistochastic real n × n matrix P is d-orthostochastic when P_rc = ‖V_rc‖² for vectors V_rc ∈ ℝ^d satisfying the source's equations (1) and (2): column orthogonality, Σ_r ⟨V_rj, V_rk⟩ = δ_jk, and row orthogonality, Σ_c ⟨V_jc, V_kc⟩ = δ_jk. The definitions are quoted in [the literature note](../Library/QuantumContext/gutkin2013orthostochastic.md).

Issue [#19782](https://github.com/the-omega-institute/trureturing/issues/19782) fixes the reading:
- d_min(n) is the natural-number infimum of the set of d for which every bistochastic n × n matrix is d-orthostochastic;
- the claim is that some n₀ has 2 ≤ d_min(n) ≤ 3 for every n ≥ n₀.

The conjecture is refuted.

## Motivation

The source reads P ∈ OS(F, n, d) as a quantization of the classical system P with d internal degrees of freedom. d_min(F, n) is then the number of internal degrees of freedom that suffice for every bistochastic n × n matrix. Before stating the conjecture, the source says that its results and dimensional considerations suggest d_min(F, n) does not increase indefinitely with n.

## Gap

The literature check before any Lean is recorded in #19782:
- arXiv:1301.2537 has only v1;
- OpenAlex lists two citing works:
  - Nechita–Ouyang–Szczepanek (arXiv:2310.03436) report the error in the source's Lemma 1 and study a different block-unitary object;
  - Smith (2015): only the abstract was read; it concerns ray patterns and eigenvalues of unistochastic matrices;
- arXiv:2604.02309 cites the source only for the definition;
- the repository had no record.

`not-found-in-searched-scope`.

## Route

Let S_n have:
- (S_n)_00 = 0;
- (S_n)_0j = (S_n)_j0 = 1/(n − 1) for j ≥ 1;
- (S_n)_jj = 1 − 1/(n − 1) for j ≥ 1;
- all other entries 0.

1. **The star matrix.** S_n is symmetric and bistochastic for n ≥ 2.
2. **Cross terms vanish.** If V lifts S_n in ℝ^d with the norm equations and column orthogonality, then for distinct j, k ≥ 1 every row r ≠ 0 has V_rj = 0 or V_rk = 0. So column orthogonality gives ⟨V_0j, V_0k⟩ = 0.
3. **Dimension bound.** The n − 1 vectors V_0j (j ≥ 1) are nonzero and pairwise orthogonal, so n − 1 ≤ d.
4. **Membership.** If 2 ≤ d_min(n), the defining set is nonempty, so S_n is d_min(n)-orthostochastic and d_min(n) ≥ n − 1.
5. **Conclusion.** For n = max(n₀, 5) this gives d_min(n) ≥ 4, contradicting the claim.

## Falsifier

The refutation would not answer the conjecture if the module's notion of d-orthostochastic matrix were stricter than the source's, so that a lift admitted by the source were excluded.
- **Literal reading.** The module requires the norm equations and both of the source's equations (1) and (2), which is the source's set Iso read literally.
- **Weaker readings.** The proof uses only column orthogonality. Since S_n is symmetric, the same argument applies with row orthogonality alone. Weakening Iso to either equation therefore does not rescue the conjecture.

## Evidence

The canonical source is `D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.lean` (174 lines).
- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Matrix/GutkinOrthostochasticDimensionRefutation.lean.json`, statement `sha256:68f5308c3e50bf613e5fc7c990463ef5fa6ac818b7e335ef90d57039782e4c5f`.

Declaration statements:
- `result`: `sha256:587ecd9d9b417ce02bc6db2eccec8ff1dcb45f8dd1f43450e3640d3490e678d6`;
- `claim`: `sha256:e1155bcab21eedabdcd54b3abdd41694a29ec8cfe24d181e5263adde1747e350`.

## Triage

Tier 1 conjecture of a 2013 paper, preregistered in issue #19782 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. `utility: kind=certified-instance; basis=refutes`. There is no digestion atom.

### What the settlement shows

**Proved in the module:**
- *The obstruction.* The private `star_lift_dimension_bound` proves that, for n ≥ 2, every lift of the star matrix S_n in ℝ^d satisfying the norm equations and column orthogonality has n − 1 ≤ d.
- *The refutation.* `result` proves that the conjecture fails. Assuming 2 ≤ d_min(n) for n = max(n₀, 5), the set defining d_min(n) is nonempty, so S_n has a lift in dimension d_min(n), and d_min(n) ≥ n − 1 ≥ 4.

**Argued, not formalized.**
- *Unconditional lower bound.* The set defining d_min(n) is nonempty, since the lift V_rc = √P_rc (e_r ⊗ e_c) in ℝ^{n²} satisfies both equations. With the obstruction this gives d_min(n) ≥ n − 1 for every n ≥ 2. The module does not formalize the nonemptiness, so the unconditional bound is not a Lean theorem.
- *Mechanism.* A bistochastic matrix whose row r spreads its mass over columns j whose other rows have pairwise disjoint supports forces the vectors V_rj to be pairwise orthogonal. So it forces at least as many internal dimensions as the number of such columns. The dimension count behind the conjecture compares numbers of parameters and does not see this orthogonality constraint.
- *Other fields.* Steps 2–3 use only the inner-product structure, so the same bound d_min(F, n) ≥ n − 1 holds for F = ℂ and F = ℍ.
- *Effect on the paper.*
  - The heuristic preceding the conjecture fails: d_min(F, n) grows at least linearly in n.
  - With column orthogonality alone, the lift V_rc = √P_rc e_c shows that every bistochastic matrix is F^n-bistochastic (the construction in the source's Proposition 1.3). For that reading, n − 1 ≤ d_min(F, n) ≤ n.
  - With both equations read literally, V_rc = √P_rc (e_r ⊗ e_c) ∈ F^{n²} satisfies both, so d_min(F, n) ≤ n². The exact value is open.
- *Interior matrices.* For n ≥ 5 the strictly positive matrices (199/200)(A₅ ⊕ I_{n−5}) + J_n/(200n), with A₅ a 5 × 5 star, also have no lift in ℝ³. In a lift, the Gram matrix of the row-0 vectors in columns 1–4 has diagonal entries a = 199/800 + c and off-diagonal entries of modulus at most 2√(bc) + (n − 3)c, where c = 1/(200n) and b = 597/800 + c, by column orthogonality and Cauchy–Schwarz. It is therefore diagonally dominant and has rank 4 (the search seat's argument; the orchestrator checked a − 3(2√(bc) + (n − 3)c) > 0 for 5 ≤ n ≤ 2000 and the bistochasticity numerically; not formalized). So the failure is not confined to the boundary of the Birkhoff polytope.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority; the full text of Smith (2015) was not read. The statements in "Argued, not formalized" are not formalized.
