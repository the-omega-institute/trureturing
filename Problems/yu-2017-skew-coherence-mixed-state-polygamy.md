---
slug: yu-2017-skew-coherence-mixed-state-polygamy
bibkey: yu2017skewcoherence
doi: 10.1103/PhysRevA.95.042337
url: https://arxiv.org/abs/1704.04871v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.result
---

# Yu's mixed-state skew-coherence polygamy conjecture is false

## Problem

Chang-shui Yu, *Quantum coherence via skew information and its polygamy*, Phys. Rev. A 95, 042337 (2017), arXiv:1704.04871v1, Discussion and Conclusions, `coherenceLy.tex`, lines 997–999:

> However, we would like to conjecture that it could hold for the bipartite mixed states with the dimension $N \geq 6$.

Appendix D, “The conjecture,” lines 1396–1397, repeats:

> In this sense, we would like to conjecture that this relation should be satisfied in $(N\geq 6)$-dimensional systems.

The quotations are checked against the v1 TeX member `coherenceLy.tex`, md5 `026b6fb07e6d276a7bd743cc480af58c`. Lemma 1, lines 170–178, defines the reference-basis coherence by $C(\rho)=1-\sum_k\langle k|\sqrt\rho|k\rangle^2$, with the positive square root. Write $Q(\rho)=1-C(\rho)$. Theorem 2, lines 543–550, states $Q(|\Psi\rangle_{AB})\le Q(\rho_A)Q(\rho_B)$ for every bipartite pure state and its two reduced density matrices. The conjecture asks for the same inequality for arbitrary bipartite mixed states of total dimension $N\ge6$; the $2\otimes3$, $3\otimes3$, $3\otimes4$ and $4\otimes4$ figure captions identify $N$ as the total dimension.

Issue [#23835](https://github.com/the-omega-institute/trureturing/issues/23835) fixes the reading: for all natural $m,n$ with $mn\ge6$ and every positive semidefinite complex matrix $\rho$ of trace one on $\mathbb C^m\otimes\mathbb C^n$, in the product reference basis,

$Q(\rho)\le Q(\operatorname{Tr}_B\rho)Q(\operatorname{Tr}_A\rho)$.

This is `claim`; `result : ¬ claim` refutes it.

## Motivation

The question concerns the distribution of a single coherence measure between a composite state and its marginals, with all coherences evaluated in compatible reference bases. The conjecture would extend the pure-state relation without the state-dependent factors in the source's separate mixed-state bounds. Appendix D motivates the proposed dimension threshold by numerical tests; the settlement determines whether that threshold suffices for a universal statement.

## Gap

The bounded literature check recorded in #23835 reports:

- arXiv lists only v1;
- an arXiv abstract search for “polygamy” with “coherence” finds the source and arXiv:1806.10814, concerning a different, Hellinger-distance coherence measure;
- the orchestrator (Claude Code, Opus) reports 199 INSPIRE citing records and a search of all 107 arXiv sources among them for “polygam,” finding restatements of the pure-state result, different polygamy relations and citations, without a settlement of this conjecture;
- an external search report covers Zenodo, ResearchGate, SSRN and GitHub without finding a settlement;
- the repository searches recorded in the issue find no prior treatment of this conjecture.

`not-found-in-searched-scope`. These search reports are attributed evidence, not an exhaustive novelty claim.

## Route

All matrix certificates below concern only the module's fixed `rho`, `tau`, `beta` and their explicitly defined candidate roots. Put

$\sigma=\frac1{68}\begin{pmatrix}17&12&12&9\\12&17&9&12\\12&9&17&12\\9&12&12&17\end{pmatrix}$, $\tau=\begin{pmatrix}1/2&6/17\\6/17&1/2\end{pmatrix}$.

The witness `rho` is $\rho=\tfrac12\sigma\oplus\tfrac12\tau$, where the first block occupies $\mathbb C^2\otimes\operatorname{span}\{|0\rangle,|1\rangle\}$ and the second occupies $\mathbb C^2\otimes\operatorname{span}\{|2\rangle\}$. This specifies a matrix on $\mathrm{Fin}\,2\times\mathrm{Fin}\,3$, independently of how the two orthogonal blocks are listed.

1. **Density and marginals.** `root_rho_positive` proves the fixed `rootRho` positive semidefinite, using a positive scaling of a sum of six vector outer products with nonnegative weights. `root_rho_square` proves `rootRho * rootRho = rho`, and `rho_density` proves `IsDensity rho`, meaning positive semidefiniteness and trace one. For this same witness, `marginal_right` gives $\operatorname{Tr}_B\rho=\tau$ and `marginal_left` gives $\operatorname{Tr}_A\rho=\beta=\tfrac12\tau\oplus\tfrac12$.
2. **Positive square roots.** For the fixed marginal matrices, `root_tau_positive`, `root_tau_square`, `root_beta_positive` and `root_beta_square` certify the displayed candidates as positive semidefinite square roots. `sqrt_rho`, `sqrt_tau` and `sqrt_beta` identify them with `CFC.sqrt`. Each use of `CFC.sqrt_eq_iff` has both matrices nonnegative and the candidate's square equal to its target; marginal nonnegativity follows from the positive semidefinite witness by `partialTraceRight_posSemidef` and `partialTraceLeft_posSemidef`.
3. **Exact violation.** With $s=25/34$ and $q=1/2+\sqrt{145}/34$, `value_rho`, `value_tau` and `value_beta` give, for these fixed matrices, $Q(\rho)=(s+q)/2$, $Q(\tau)=q$ and $Q(\beta)=(q+1)/2$. `violation_gap` gives

   $Q(\rho)-Q(\tau)Q(\beta)=\frac{208-17\sqrt{145}}{1156}$.

   `strict_violation` proves this gap positive. The theorem `result` instantiates the assumed `claim` at $m=2$, $n=3$, using $6\le2\cdot3$ and `rho_density`; the two marginal identities turn that instance into the opposite of `strict_violation`.

## Falsifier

The refutation would miss the source's conjecture if the coherence, square root, marginal maps or dimension condition differed. The module uses:

- `skewCoherence` equal to one minus the sum of squared real diagonal entries of `CFC.sqrt`; for positive semidefinite complex matrices the positive square root is Hermitian, so its diagonal is real and agrees with the source's expression;
- `IsDensity` equal to positive semidefiniteness together with complex trace one;
- `partialTraceRight` summing over the right index and retaining the left subsystem, and `partialTraceLeft` summing over the left index and retaining the right subsystem;
- the total-dimension condition $6\le mn$, met by the two-by-three witness.

The contradiction uses an exact positive radical gap, not the source's random tests or a numerical tolerance.

## Evidence

The canonical source is `D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** The compiled `#print axioms` reading uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/SkewCoherencePolygamyMixedRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:6d4b179497f4c3019e9002fd750ddd05f636f22908335137e0af5ae27d86b8ce`;
- `claim`: `sha256:4f92b7db4a65925ee2823d78e5555090590f9d29849c36ae81fea436b1d16c10`.

## Triage

Tier 1 conjecture of a 2017 paper, preregistered in issue #23835 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the assertion that, for every pair of natural dimensions $m,n$ with $mn\ge6$ and every positive semidefinite complex matrix $\rho$ of trace one on their product, $Q(\rho)\le Q(\operatorname{Tr}_B\rho)Q(\operatorname{Tr}_A\rho)$ is false.

**Computed, not formalized** (direct arithmetic): decimal values of $Q(\rho)$ and of $Q(\operatorname{Tr}_B\rho)\,Q(\operatorname{Tr}_A\rho)$ for the witness, consistent with the exact gap proved by `result`.

**Argued, not formalized.**

- *Mechanism and scope.* For the two-qubit seed $\sigma$ displayed above, the positive square root is $M/(2\sqrt{34})$, where $M$ has diagonal $5$, off-diagonal $2$ when exactly one local index agrees, and off-diagonal $1$ otherwise. In the product Hadamard basis $M$ has eigenvalues $10,4,4,2$ and its square is $136\sigma$, so $Q(\sigma)=s$ and both marginals equal $\tau$. Consequently $s-q^2=(208-17\sqrt{145})/578>0$. More generally, for $0<t\le1$, put $\rho_t=t\sigma\oplus(1-t)\tau$ on the same two orthogonal reference-basis blocks. Its marginals are $\tau$ and $t\tau\oplus(1-t)$. The positive square root respects these blocks and scales each by the square root of its weight, giving $Q(\rho_t)=ts+(1-t)q$ and $Q(\operatorname{Tr}_A\rho_t)=tq+1-t$. Its violation is therefore $t(s-q^2)>0$. The formalized witness is the fixed choice $t=1/2$; this parameterized extension is not a statement of `result`.
- *Purity, rank and separability.* Let $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$. The seed is the mixture of the four product projectors $|++\rangle$, $|+-\rangle$, $|-+\rangle$, $|--\rangle$ with respective weights $25/34,2/17,2/17,1/34$. Also $\tau=(29/34)|+\rangle\langle+|+(5/34)|-\rangle\langle-|$. These decompositions express $\rho_t$ as a convex mixture of product states. For $0<t<1$ all six block eigenvalues are positive, so $\rho_t$ has full rank. Thus neither separability nor full rank supplies the missing restriction; purity is a sufficient restriction, as in the source's Theorem 2.
- *Surviving cases.* For any finite-dimensional density matrices $a,b$, the positive square root of $a\otimes b$ is $\sqrt a\otimes\sqrt b$, since this matrix is positive semidefinite and its square is $a\otimes b$; summing its squared diagonal entries gives $Q(a\otimes b)=Q(a)Q(b)$. For a unit pure state with Schmidt amplitudes $\lambda_i\ge0$ and local Schmidt vectors $u_i,v_i$, write $a_k=\sum_i\lambda_i|u_i(k)|^2$ and $b_l=\sum_i\lambda_i|v_i(l)|^2$, the diagonal entries of the two marginal square roots. Cauchy–Schwarz gives $|\sum_i\lambda_i u_i(k)v_i(l)|^2\le a_kb_l$; squaring and summing gives the pure-state inequality because the joint square root is the pure-state projector. These arguments preserve the product-state equality and the pure-state restriction without extending them to arbitrary mixtures.
- *Effect on the source.* The universal extension proposed in Discussion and Conclusions and Appendix D is refuted at its smallest total dimension. Corollary 1 instead states, for bipartite mixed states, $Q(\rho_A)Q(\rho_B)\ge\lambda_{\min}Q(\rho_{AB})$, with $\lambda_{\min}$ the smallest nonzero eigenvalue, and also gives bounds using the rank and eigenstate marginals. Its Appendix B derivation, and the derivation there of Corollary 2 from Corollary 1, do not assume the conjecture. The refutation therefore supplies no counterexample to these separate statements or to Theorem 2. The numerical observations in Appendix D cannot justify a universal dimension threshold; a characterization of the mixed states satisfying the unmodified inequality remains open here.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The issue's arXiv version listing, abstract search, INSPIRE count and search of 107 citing sources, external-platform searches and repository searches are reported evidence and have not been independently reproduced. The other papers named in those search reports have not been independently read. The source's random-state experiments have not been reproduced.

The decimal evaluation, the parameterized flagged extension, the separability and full-rank deductions, the general product and pure-state arguments, and the source-dependency analysis are not formalized by this module. The source text and the indicated derivations were read, but Corollaries 1 and 2 have not received an independent complete proof audit here. A characterization of all mixed states satisfying the inequality, or another sufficient structural restriction beyond the cases discussed, is not settled.
