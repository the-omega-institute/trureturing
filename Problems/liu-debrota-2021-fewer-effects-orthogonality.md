---
slug: liu-debrota-2021-fewer-effects-orthogonality
bibkey: liudebrota2021orthogonality
doi: 10.1103/PhysRevA.104.052216
url: https://arxiv.org/abs/2105.02074v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.result
---

# The Liu–DeBrota fewer-effects construction does not minimize orthogonality

## Problem

Y. Liu and J. B. DeBrota, *Relating measurement disturbance, information and orthogonality*, arXiv:2105.02074v2 (Phys. Rev. A 104, 052216, 2021), Appendix C, subsection “Fewer effects”, Conjecture 2 (`apssamp.tex`, lines 795–797):

> The above constructed POVM has
> minimal orthogonality $O$ among POVMs having $n(n<d)$ nonvanishing effects.

For a POVM $F=(F_i)_{i=1}^n$ on $\mathbb C^d$, Section IV (`apssamp.tex`, lines 403–420) defines $S(F)_{ij}=\operatorname{tr}(\sqrt{F_i}\sqrt{F_j})$ and $O(F)=\|S(F)-I_n\|_F^2$. The square roots are the positive semidefinite square roots. Equivalently, $O(F)=\sum_{i,j}|S(F)_{ij}-\delta_{ij}|^2$.

For natural numbers $0<n<d$, write $d=an+b$, where $a=\lfloor d/n\rfloor$ and $0\le b<n$. The proposed construction $E^{(n,d)}$ consists of diagonal coordinate projectors on consecutive disjoint blocks: the first $n-1$ blocks have size $a$, and the last has size $a+b$. Its Gram matrix is $\operatorname{diag}(a,\ldots,a,a+b)$, as displayed in Appendix C (`apssamp.tex`, lines 765–778).

Issue [#25254](https://github.com/the-omega-institute/trureturing/issues/25254) fixes the formal reading: for every $n,d\in\mathbb N$ with $0<n<d$ and every family of nonzero positive semidefinite complex $d\times d$ matrices $F_i$ satisfying $\sum_iF_i=I_d$, one has $O(E^{(n,d)})\le O(F)$. This universal assertion is refuted.

## Motivation

The source studies the relation between measurement disturbance, measurement strength and orthogonality. Its main orthogonality comparison concerns $d\le n\le d^2$; Appendix C asks for minimizers outside that range. The fewer-effects question distinguishes pairwise orthogonality from proximity to an orthonormal set: the objective also penalizes diagonal Gram entries different from one. Identifying the minimizer therefore requires controlling the sizes of the effects as well as their overlaps.

## Gap

Issue #25254 records the bounded literature check before any Lean:

- arXiv:2105.02074v2 retains Conjecture 2, which is directly verified in the source quoted above;
- OpenAlex and Crossref reportedly list two citing works, Sun–Li–Luo, Phys. Rev. A 105 (2022) 062458, and Sun–Li, Phys. Rev. A 109 (2024) 012407; the preregistration reports abstract readings concerning channel trade-off identities, without full-text readings;
- the reported web searches for the conjecture and fewer-effects orthogonality, Zenodo searches for the title and topic, and repository searches found no settlement.

`not-found-in-searched-scope`.

## Route

The canonical module's private counterexample lemmas use the fixed dimensions $n=4$, $d=10$.

1. **Square roots.** For a finite index type with decidable equality and a real diagonal $p$ satisfying $p_k\ge0$ for every coordinate, `NMLWMeasuredFidelitySeparation.sqrt_diagonal` identifies the positive square root of $\operatorname{diag}(p)$ with $\operatorname{diag}(\sqrt p)$. The private `construction_sqrt` and `competitor_sqrt` apply this to the zero-or-one diagonals and prove, for each $i\in\mathrm{Fin}\,4$, that the corresponding matrix equals its own `CFC.sqrt`.
2. **Gram matrices.** The definition `construction 4 10` assigns the consecutive blocks $[0,2)$, $[2,4)$, $[4,6)$, $[6,10)$; the private `competitor` assigns $[0,2)$, $[2,4)$, $[4,7)$, $[7,10)$. The private `construction_gram` and `competitor_gram` give $S(E)=\operatorname{diag}(2,2,2,4)$ and $S(F)=\operatorname{diag}(2,2,3,3)$ for these particular families.
3. **Admissibility.** The private `competitor_povm` proves `IsPOVMWith 4 10 competitor`: every competitor effect is positive semidefinite and nonzero, and their sum is $I_{10}$.
4. **Strict improvement.** The private `construction_orthogonality` and `competitor_orthogonality` prove $O(E)=12$ and $O(F)=10$, respectively, for those fixed families. Applying `claim` at $n=4$, $d=10$ and this admissible competitor would give $12\le10$; `result` derives the contradiction.

## Falsifier

The refutation would miss the source conjecture if it changed the Gram matrix, objective, admissible effects or proposed construction. The module uses:

- `gram`, defined by `GeneralizedFidelity.fidelity 1`, which reduces to $\operatorname{tr}(\sqrt{F_i}\sqrt{F_j})$;
- `orthogonality`, defined by `CHaarConcatenationNonmonotone.hsNormSq (gram f - 1)`, the sum of squared complex moduli relative to the $n\times n$ identity, with no dimension normalization;
- `IsPOVMWith`, requiring positive semidefinite, nonzero effects and sum $I_d$; it imposes no additional distinctness condition on the indexed effects;
- `construction`, with the rank pattern fixed by the source's displayed $S=\operatorname{diag}(a,\ldots,a,a+b)$.

The adjoining source sentence (`apssamp.tex`, line 775) uses the index condition “$i<n-1$”, which would leave $E_{n-1}$ unspecified under one-based indexing. The displayed Gram matrix and the preregistered reading fix the first $n-1$ ranks to be $a$. The counterexample addresses that explicit construction. Its competitor has four nonzero effects and satisfies $0<4<10$.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:d45f65815ac99db776e3bd881877cb875ea92ce7986cd39f7b2456c7d891d709`;
- `claim`: `sha256:9b247b38d975277bc596a58f244482a984d4c14aec78933a97106e0d4f2f8543`.

## Triage

Tier 1 conjecture of a 2021 preprint published in Physical Review A, preregistered in issue #25254 before any Lean.
`theorem`; resolution `refuted`.

The designated `result` has `proof_shape: bind-only` and `admission_basis: open-problem-resolution`. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every $n,d\in\mathbb N$ with $0<n<d$, the family `construction n d` has orthogonality no greater than that of every family of $n$ nonzero positive semidefinite complex $d\times d$ matrices summing to $I_d$.

**Computed, not formalized:** None.

**Argued, not formalized**:

- *Mechanism and projective repair.* For $n$ mutually orthogonal nonzero projectors summing to $I_d$, let their positive integer ranks be $r_1,\ldots,r_n$. Their square roots are themselves, their Gram matrix is $\operatorname{diag}(r_1,\ldots,r_n)$, and $O=\sum_i(r_i-1)^2$. If two ranks satisfy $r\ge s+2$, replacing them by $r-1,s+1$ preserves positivity and their sum and decreases this objective by $2(r-s-1)>0$. Every positive integer rank partition of $d$ is realized by coordinate blocks. Repeating this finite reduction leaves ranks differing by at most one. Thus, among projective POVMs with $0<n<d$ and $d=an+b$, the minimizing rank pattern has $b$ ranks $a+1$ and $n-b$ ranks $a$. Compared with it, concentrating the remainder in one block increases $O$ by $b(b-1)$, so every $2\le b<n$ gives the same failure mechanism. For $b=0$ or $b=1$, the source construction already has balanced ranks and minimizes within the projective class.
- *A surviving unrestricted case.* For any POVM with $0<n<d$, put $q_i=\operatorname{tr}F_i\in\mathbb R$, so $\sum_iq_i=d$. Keeping only the diagonal terms in $O$ and applying Cauchy–Schwarz gives $O\ge\sum_i(q_i-1)^2\ge(d-n)^2/n$. When $n$ divides $d$, the source's equal-rank projectors attain this bound, giving an argument for that restricted case even among all POVMs. For nonzero remainder, optimality of the balanced replacement among all POVMs remains open in this dossier.
- *Effect on the source.* Conjecture 2's proposed global minimizer is refuted. The formulas for the specified construction in Appendix C.1 are separate assertions; refuting its optimality does not refute those evaluations. The source's disturbance decomposition, its Section IV comparison for $d\le n\le d^2$, and Conjectures 1 and 3 are not settled by this result. The inspected proof in Appendix B and argument in Appendix C.2 do not invoke Conjecture 2, so they lose no premise from this refutation. Appendix C's general question of finding optimal POVMs outside $[d,d^2]$ is not answered in full by the formal settlement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The OpenAlex and Crossref citation count, the citing-work abstract readings, and the web, Zenodo and repository search outcomes are reports in #25254 and were not independently reproduced. The journal text and the full texts of the two citing works were not read; whether they retain or settle the same conjecture is unverified. The source reading establishes the quoted statement in arXiv:2105.02074v2, without independently checking the preregistration's assertion that v2 is the latest version.

The statements in “Argued, not formalized” are not Lean results. The general rank-balancing argument, the unrestricted divisible case, and the dependency assessment of the source's other statements are not formalized. No general minimum over all POVMs with nonzero remainder is claimed.
