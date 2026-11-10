---
slug: yao-li-sun-2019-coherence-fraction-incoherent-nonmonotone
bibkey: yaolisun2019coherencefraction
doi: 10.1103/PhysRevA.100.032324
url: https://arxiv.org/abs/1906.09789v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.result
---

# The quantum coherence fraction can increase under incoherent operations

## Problem

Y. Yao, D. Li and C. P. Sun, *Quantum coherence fraction*, Phys. Rev. A 100, 032324 (2019), arXiv:1906.09789v1, Section V, `CF.tex`, lines 422–423:

> First, similar to the behavior of fully entangled fraction \cite{Badziag2000}, we conjecture that $C_{\mathcal{F}}(\rho)$ may not satisfy the monotonicity under general incoherent operations.

The source fixes the computational basis as the incoherent basis. An incoherent operation has a Kraus representation whose individual branches map diagonal density matrices to diagonal matrices; the normalized nonzero branches are again incoherent states (Section II, lines 122–131). Its quantum coherence fraction is $C_{\mathcal F}(\rho)=\max_{|\phi\rangle\in\mathcal{MCS}}\langle\phi|\rho|\phi\rangle$, where the maximally coherent unit vectors have coordinates of modulus $1/\sqrt d$ (lines 141–150). The definitions and source locator are in [the literature note](../Library/QuadraticForms/yaolisun2019coherencefraction.md).

Issue [#22563](https://github.com/the-omega-institute/trureturing/issues/22563) fixes `claim` as the universal monotonicity assertion: for every $d,m\in\mathbb N$, every complex $d\times d$ matrix $\rho$ that is positive semidefinite with trace one, and every family $K:\mathrm{Fin}\,m\to M_d(\mathbb C)$ satisfying $\sum_\alpha K_\alpha^\dagger K_\alpha=I$ and preserving diagonality under each sandwich $X\mapsto K_\alpha X K_\alpha^\dagger$ for every complex diagonal matrix $X$, one has $C_{\mathcal F}(\sum_\alpha K_\alpha\rho K_\alpha^\dagger)\le C_{\mathcal F}(\rho)$. Here the module defines $C_{\mathcal F}(A)=\sup\{\operatorname{Re}(z^\dagger Az)/d: z\in\mathbb C^d,\ |z_j|=1\text{ for every }j\}$ using the real `sSup`.

The formal resolution is `refuted`, because `result : ¬ claim` negates universal monotonicity. This confirms the source's conjecture of non-monotonicity.

## Motivation

The fraction optimizes the overlap with a single maximally coherent state, making it a natural measure of proximity to that target set. Whether a free incoherent operation can increase it tests deterministic resource monotonicity of this overlap. The source also compares it with normalized robustness of coherence, $\overline C_{\mathcal R}=(1+C_{\mathcal R})/d$, whose optimization allows more general correlation matrices. A strict increase distinguishes these two optimizations without relying on numerical maximization of the input fraction.

## Gap

Issue #22563 records the bounded literature check before any Lean:

- The source's v1 TeX states the conjecture; its Section IV cautions that local maxima can affect the observed numerical gap from normalized robustness.
- The orchestrator's web searches for coherence fraction, monotonicity, counterexamples and robustness gaps found the source, the separate *Coherence Fraction* preprint arXiv:1906.08326, and one-shot coherence-distillation work, with no settlement found in that scope.
- The orchestrator reported an unrelated Zenodo title match and no existing repository record of arXiv:1906.09789.
- The search seat reported no settlement in site-restricted searches of Zenodo, ResearchGate, SSRN and GitHub for the title and conjecture fragment.

`not-found-in-searched-scope`.

## Route

Use coordinates $0,1,2,3$ and write $i$ for the imaginary unit. The module's fixed matrix `p` is

$P=\frac1{2163}\begin{pmatrix}1425&-300-300i&615-240i&615+240i\\-300+300i&1075&680+180i&-180-680i\\615+240i&680-180i&913&225-400i\\615-240i&-180+680i&225+400i&913\end{pmatrix}$.

1. **A density matrix and an incoherent operation.** For this fixed $P$, `p_star`, `p_square`, `p_trace` and `p_pos` establish $P^\dagger=P$, $P^2=P$, $\operatorname{tr}P=2$ and positive semidefiniteness. `rho_half` identifies the fixed `rho` with $\rho=P/2$, and `rho_density` establishes its density conditions. The fixed Kraus matrices are $K_0=\operatorname{diag}(1,0,3/5,3/5)$ and $K_1=\operatorname{diag}(0,1,4/5,-4i/5)$; `k_incoherent` proves completeness and preservation of every complex diagonal matrix by each branch. Put $Q=\Phi(\rho)=\sum_{\alpha=0}^1K_\alpha\rho K_\alpha^\dagger$.
2. **The output lower bound and supremum obligations.** `phi_rho` identifies this fixed output with the explicit matrix `q`; `output_at_ones` gives $\operatorname{Re}(\mathbf1^\dagger Q\mathbf1)/4=1/2$. For every complex $4\times4$ matrix $A$, `coherence_bddAbove` proves that the set in its coherence-fraction supremum is bounded above. `output_lower` uses this boundedness and the admissible all-ones vector to obtain $C_{\mathcal F}(Q)\ge1/2$.
3. **A uniform defect on unit-modulus coordinates.** For complex $x,y,w,t$ with $|x|=|y|=|w|=|t|=1$, `torus_defect` gives $4/25\le|w-(3x+4y)/5|^2+|t-(3x+4iy)/5|^2$. For arbitrary complex $a,b,c,d$, `residual_functional_bound` bounds the analogous sum by $4(|a|^2+|b|^2+|c|^2+|d|^2)$. For every $z\in\mathbb C^4$, `p_functionals` says that $F_1(v)=v_2-(3v_0+4v_1)/5$ and $F_2(v)=v_3-(3v_0+4iv_1)/5$ vanish at $v=Pz$, and `defect_identities` gives $F_j(z)=F_j(z-Pz)$. Thus for every $z$ whose four coordinates have modulus one, these bounds give $\|z-Pz\|_2^2\ge1/25$.
4. **The input bound and contradiction.** For every $z\in\mathbb C^4$, `projection_energy` gives $\operatorname{Re}(z^\dagger Pz)+\|z-Pz\|_2^2=\sum_j|z_j|^2$. With the hypothesis $|z_j|=1$ for every coordinate, `input_bound` therefore gives $\operatorname{Re}(z^\dagger\rho z)/4\le1/2-1/200$. `input_upper` supplies nonemptiness using the all-ones vector and takes the supremum, obtaining $C_{\mathcal F}(\rho)\le99/200$. Finally `result` applies `claim` at $d=4$, $m=2$, this density matrix and this incoherent Kraus family, contradicting $C_{\mathcal F}(\rho)\le99/200<1/2\le C_{\mathcal F}(Q)$.

## Falsifier

The refutation would not answer the source's question if the overlap normalization, state conditions or branch condition differed in a way that invalidated the witness.

- For $d>0$, $z\mapsto z/\sqrt d$ identifies the unit-modulus coordinate vectors with the source's maximally coherent states. The domain is nonempty and compact, and the quadratic form is continuous, so its real supremum agrees with the source's maximum. This correspondence is a mathematical interpretation of the definitions, not a separate theorem of the module.
- `IsDensity` means positive semidefinite with trace one. The fixed four-dimensional witness satisfies both conditions by `rho_density`.
- `IsIncoherentOperation` tests all complex diagonal matrices without dividing by branch traces. For the fixed diagonal Kraus matrices, `k_incoherent` proves this condition directly. Their sandwiches of diagonal density matrices are positive diagonal matrices, and every nonzero-trace branch can be normalized as in the source; zero branches need no normalization.
- Although `claim` quantifies over all natural dimensions and Kraus counts, the contradiction uses $d=4$, $m=2$, so it does not exploit a zero-dimensional convention or an empty Kraus family.
- The strict increase uses the certified bounds $99/200<1/2$, not a numerical estimate of the input optimum or an unproved exact output optimum.

## Evidence

The canonical source is `D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone.lean.json`.

Declaration statements:

- `result`: `sha256:767b42fbaddc79c89df214af0e14579a52dbc1c3804d977eaa02e9470b88f7f0`;
- `claim`: `sha256:c3204f58356b933831e8c80f50e910553c83a85a7f908160bcf4a491f6eaec7c`.

## Triage

Tier 1 conjecture of a 2019 Phys. Rev. A paper, preregistered in issue #22563 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural dimension $d$, every natural Kraus count $m$, every positive semidefinite complex $d\times d$ matrix of trace one, and every complete Kraus family whose individual sandwiches preserve all complex diagonal matrices, the output `coherenceFraction` is at most the input `coherenceFraction`.

**Computed, not formalized** (orchestrator, reported in issue #22563): phase-alignment ascent from 4000 random starts on the fixed four-dimensional witness reported an input overlap approximately $0.49198$ and an output overlap $0.5$, without certifying the input global maximum.

**Argued, not formalized.**

- *Mechanism.* The range constraints for the fixed projection require $v_2=(3v_0+4v_1)/5$ and $v_3=(3v_0+4iv_1)/5$. If all four coordinates had modulus one, the two equations would force both the real and imaginary parts of $v_0\overline{v_1}$ to vanish, contradicting $|v_0\overline{v_1}|=1$. This explains why an optimized flat vector misses part of the projection's energy. The diagonal Kraus channel changes the off-diagonal compatibility while fixing every diagonal matrix: completeness makes each diagonal multiplier equal to one. Preserving populations and branchwise incoherence therefore does not ensure monotonicity of this optimized overlap.
- *A sufficient restriction that survives.* In a fixed positive dimension, a finite mixture $\Psi(A)=\sum_jp_jU_jAU_j^\dagger$ of diagonal unitaries, with $p_j\ge0$ and $\sum_jp_j=1$, cannot increase the fraction. Substitution of $U_j^\dagger z$ preserves the admissible phase vectors, giving unitary invariance; taking the supremum of linear overlap functionals gives convexity. Consequently $C_{\mathcal F}(\Psi(\rho))\le\sum_jp_jC_{\mathcal F}(U_j\rho U_j^\dagger)=C_{\mathcal F}(\rho)$. The witness channel therefore cannot be such a mixture. Diagonal Kraus operators alone are a weaker restriction.
- *Exact output and robustness gap.* For this fixed projection, $0\le P\le I$. The diagonal complete Kraus family is also unital, so positivity gives $Q=\Phi(P/2)\le I/2$. Every normalized coherent vector then has overlap at most $1/2$; together with the fixed-witness lemma `output_lower`, this gives $C_{\mathcal F}(Q)=1/2$. The output upper bound is an argument here, not a compiled conclusion of that lemma. The source's Theorem 2 (Section III, lines 259–266) identifies normalized robustness, for every density matrix, with the largest overlap with $|\phi^+\rangle$ obtainable by a genuinely incoherent operation. Since the witness channel fixes every diagonal state, it is genuinely incoherent in the source's sense; inserting it into that optimization gives $\overline C_{\mathcal R}(\rho)\ge1/2> C_{\mathcal F}(\rho)$. The robustness quantity and this strict-gap inference are not formalized in the module.
- *Nearby source statements and remaining scope.* The source's Theorems 1–3 do not assume the conjecture, so this settlement invalidates none of their arguments. Its qubit identity in Section II and qutrit identity in Theorem 3, together with its stated monotonicity of normalized robustness under MIO, imply nonincrease under incoherent operations that keep dimension $2$ or $3$ fixed; these source-dependent implications are not formalized here. The source's second question (Section V, lines 426–428) concerns the distance between genuinely incoherent channels and mixtures of diagonal unitaries. The witness separates the two classes by the preceding convexity argument, but supplies no channel-distance value or general quantitative characterization. Uniform higher-dimensional families and full-rank perturbations are outside the formal settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches recorded in issue #22563 and does not establish exhaustive worldwide novelty or priority. Its external search results, repository-search reading and site-restricted search-seat reports were not independently reproduced. The v1 TeX definitions, conjecture and related theorem statements were read directly; later source versions and the journal text were not compared. The separately cited coherence-distillation papers were not independently read for this dossier.

The numerical reading attributed to the orchestrator was not rerun and does not certify the global input optimum. The maximum–supremum and normalized-branch interpretations in "Falsifier", and all statements grouped as "Argued, not formalized", are outside the module's formal conclusions; the latter include the genuinely incoherent classification, the exact output upper bound, diagonal-unitary mixture monotonicity, the robustness gap, the low-dimensional implications and the channel-class separation. The source's robustness characterization and its low-dimensional identities are used as literature results and have no Lean verification here. No higher-dimensional family, full-rank extension, optimal increase or channel-distance bound is claimed as formalized.
