---
slug: xu-et-al-2023-noisy-ghz-witness-bound-gap
bibkey: xuzhouzhaohu2023gme
doi: 10.1103/PhysRevA.107.052405
url: https://arxiv.org/abs/2211.05563v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.result
---

# The optimized GHZ witness bound need not equal the geometric GME measure

## Problem

X.-Y. Xu, Q. Zhou, S. Zhao, S.-M. Hu, L. Li, N.-L. Liu and K. Chen, *A generic framework for genuine multipartite entanglement detection*, arXiv:2211.05563v1; published as *General framework for genuine multipartite entanglement detection*, Phys. Rev. A 107 (2023) 052405, DOI 10.1103/PhysRevA.107.052405. In the arXiv TeX member `GMEwitness.tex`, subsection “Estimating entanglement measures”, line 325, they ask:

> It remains open whether $\epsilon_o^{n,d}(p)$ equals $E_G(\rho_{n,d}(p))$.

The definitions are at lines 284–311:

- $|GHZ_n^d\rangle=d^{-1/2}\sum_{i=0}^{d-1}|i\rangle^{\otimes n}$ and $\rho_{n,d}(p)=pI/d^n+(1-p)|GHZ_n^d\rangle\langle GHZ_n^d|$.
- $E_G(\psi)=1-\sup_{\phi\text{ biseparable}}|\langle\phi,\psi\rangle|^2$, where both vectors are unit vectors and biseparability means a product across some nonempty proper bipartition; the mixed-state measure is its convex roof.
- $\mathcal W=P/d-|GHZ_n^d\rangle\langle GHZ_n^d|$, where $P$ projects onto computational words using at most two distinct symbols. This is the orthogonal sum in lines 297–298, with the distinct arrangements specified by the orthogonal set $S$ at lines 690–692.
- $w_{n,d}(p)=\operatorname{Tr}(\rho_{n,d}(p)\mathcal W)$, $\hat E_G(r\mathcal W)=\sup_{\|\psi\|=1,\ \phi\text{ unit biseparable}}\{\langle\psi,(r\mathcal W+|\phi\rangle\langle\phi|)\psi\rangle-1\}$ over unit vectors, and $\epsilon_o^{n,d}(p)=\sup_{r\in\mathbb R}\{r w_{n,d}(p)-\hat E_G(r\mathcal W)\}$.

The source locators are also collected in [the literature note](../Library/Divergence/xuzhouzhaohu2023gme.md).

Issue [#25044](https://github.com/the-omega-institute/trureturing/issues/25044) fixes the universal reading: for every pair of integers $n,d\ge3$ and every real $p\in[0,1]$, $\epsilon_o^{n,d}(p)=E_G(\rho_{n,d}(p))$. The formal convex roof takes the real infimum over all finite ensembles with nonnegative weights summing to one, unit pure vectors and exact reconstruction of the density matrix. This universal equality is refuted.

## Motivation

The source distinguishes detecting entanglement from estimating its amount. At lines 250–266 its witness-data bound optimizes over all states compatible with a single measured expectation. A better witness can improve this lower bound without determining the entanglement of a particular compatible state. The equality question asks whether the noisy GHZ family nevertheless attains that bound, permitting exact quantification from this witness expectation.

## Gap

The bounded literature check recorded in #25044 reports:

- the arXiv v1 text states the question; the issue reports no other arXiv version;
- OpenAlex listed eight citing works, whose accessible texts were screened by search agent `1f8848854091e27f980eddd4` without finding an answer;
- the orchestrator's Zenodo searches for GME witnesses, geometric measures and GHZ lower bounds found no related settlement, and its repository search found no existing record of the source.

The v1 question and definitions are checked against the TeX source. The citing-work screening and the other reported searches are not independently reproduced here. `not-found-in-searched-scope`.

## Route

Throughout this route $n=d=3$ and $p=3/8$. All vectors belong to $(\mathbb C^3)^{\otimes3}$. Write $G=|GHZ_3^3\rangle\langle GHZ_3^3|$, $P=\texttt{supportProjector}\ 3\ 3$, $Q=I-P$, $\rho=I/72+(5/8)G$ and $W=P/3-G$. Trace expectations below mean the real part of the trace, as in `witnessValue`. The named lemmas below are private helpers in the canonical module.

1. **Projectors and expectation.** `ghz_unit`, `projector_data` and `orthogonal_positive` establish normalization, $P^2=P$, $PG=GP=G$, $G^2=G$, and positivity of $P-G$ and $Q$. `finite_ranks` gives $\operatorname{Tr}P=21$ and $\operatorname{Tr}Q=6$; `witness_value` gives $w_{3,3}(3/8)=-1/3$.
2. **Upper bound on the optimized witness estimate.** `test_unit`, `test_expectation` and `test_overlap` concern $\psi_*=(4|000\rangle+|111\rangle+|222\rangle)/\sqrt{18}$: it is unit, has $W$ expectation $-1/3$ and squared overlap $8/9$ with the unit biseparable vector $|000\rangle$ (`zero_biseparable`). For every real $r$, `hat_bdd` bounds the set defining $\hat E_G(rW)$ above by $|r|$; `hat_lower` inserts this pair into that set and gives $\hat E_G(rW)\ge-r/3-1/9$. The outer supremum has a candidate at $r=0$, and every candidate is at most $1/9$. Thus `epsilon_upper` establishes $\epsilon_o^{3,3}(3/8)\le1/9$.
3. **Biseparable constraint.** For every unit vector $\phi$ factoring across a nonempty proper bipartition, `biseparable_overlap` proves $3\langle\phi,G\phi\rangle\le\langle\phi,P\phi\rangle$. The nine words constant on each side of its chosen cut lie in $P$ (`join_support`); they are distinct because both parts of the cut are nonempty (`join_injective`, with precisely these two nonemptiness hypotheses). Cauchy–Schwarz bounds the squared modulus of the sum of the three constant-word amplitudes by the sum of squared amplitudes over those nine words.
4. **Pure-state certificate.** Set $B=-(2/3)W+Q/9$, $D=(2/3)G+(4/3)(P-G)+Q$ and $T=(3/2)G+(3/4)(P-G)+Q$, the definitions `b`, `dmat` and `dinv`. `d_positive` gives positive definiteness of $D$, and `d_inverse` gives $DT=I$. For every unit biseparable $\phi$, `inverse_bound` gives $\langle\phi,T\phi\rangle\le1$. For arbitrary vectors $\phi,\psi$, without normalization hypotheses, `weighted_cs` gives $|\langle\phi,\psi\rangle|^2\le\langle\phi,T\phi\rangle\langle\psi,D\psi\rangle$. Consequently, for every unit $\psi$, `pure_lower` gives $E_G(\psi)\ge\langle\psi,B\psi\rangle-1/9$. The overlap set is nonempty because it contains $|000\rangle$ and is bounded above by this quadratic estimate.
5. **Convex roof and contradiction.** `ensemble_nonempty` supplies a finite normalized pure-state ensemble of $\rho$. For every natural $k$, weights $a_i\ge0$ with $\sum_{i\in\mathrm{Fin}\,k}a_i=1$, and unit vectors $\psi_i$ satisfying $\rho=\sum_i a_i|\psi_i\rangle\langle\psi_i|$, `average_lower` proves $\sum_i a_i E_G(\psi_i)\ge13/108$, using `trace_b`: $\operatorname{Tr}(\rho B)-1/9=13/108$. Thus the nonempty ensemble-value set is bounded below, and `roof_lower` gives $E_G(\rho)\ge13/108$. Together with `epsilon_upper`, this gives $\epsilon_o^{3,3}(3/8)\le1/9=12/108<13/108\le E_G(\rho)$, contradicting `claim` at admissible parameters.

## Falsifier

A counterexample would not answer the question if it changed the source's witness, pure-state optimization or ensemble constraints. Here:

- computational words are functions $\mathrm{Fin}\,n\to\mathrm{Fin}\,d$; the support condition counts distinct symbols, so each distinct arrangement occurs once;
- `IsBiseparable` requires a unit vector and factorization across some cut with both parts nonempty, allowing complex factors;
- `hatE` optimizes over all unit $\psi$ and all such biseparable $\phi$, and `epsilonO` allows every real slope;
- `geometricMeasure` uses exact finite-ensemble reconstruction and arbitrary ensemble size, with nonemptiness and the lower bound supplied at the counterexample, rather than relying on the default value of an empty real infimum.

The proof uses the defining supremum of `hatE`, not the source's displayed closed formula. It needs neither an exact value of the convex roof nor an equality claim for any other parameters.

## Evidence

The canonical source is `D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.lean`.

- **Proof.** It proves `result : ¬ claim`; the compiled type of `claim` is `Prop`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Entanglement/Witness/NoisyGhzWitnessBoundGap.lean.json`.

Declaration statements:

- `result`: `sha256:a6847ccd6ac167e01099227094c9b15c764e4805850c48cf9d52c89135bc2172`;
- `claim`: `sha256:dd999811f0abd9d13461f1edb245ddce8199da425ecb62faa41b90c18fe9e590`.

## Triage

Tier 1 open question of a 2022 arXiv preprint published in 2023, preregistered in issue #25044 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that $\epsilon_o^{n,d}(p)=E_G(\rho_{n,d}(p))$ for every pair of natural numbers $n,d\ge3$ and every real $p$ with $0\le p\le1$, using the definitions above and the finite-ensemble convex roof.

**Computed, not formalized:** None.

**Argued, not formalized**.

- *Mechanism and missing information.* At $n=d=3$, $p=3/8$, the unit pure state $\psi_*$ and the noisy state $\rho$ have the same witness expectation (`test_unit`, `test_expectation`, `witness_value`), while the squared overlap $8/9$ of $\psi_*$ with the unit biseparable vector $|000\rangle$ (`test_overlap`, `zero_biseparable`) limits its pure geometric measure to at most $1/9$. The one-element ensemble of $|\psi_*\rangle\langle\psi_*|$ therefore gives its finite-ensemble convex roof an upper bound of $1/9$. In contrast, `roof_lower` bounds this noisy state's finite-ensemble convex roof below by $13/108$. Thus the witness expectation identifies states with different geometric measures. The extra observable $Q$ separates these two states: $\psi_*$ is supported on constant words, so $Q\psi_*=0$; $GQ=0$ (`projector_data`) and $\operatorname{Tr}Q=6$ (`finite_ranks`) give $\operatorname{Tr}(\rho Q)=6/72=1/12$. The term $Q/9$ in $B$ uses this additional information. These observations explain the strict gap without assuming that a finer entanglement witness must quantify entanglement exactly.
- *The weaker lower-bound statement survives.* For a unit three-qutrit vector $\psi$, every real $r$ satisfies $\hat E_G(rW)\ge r\langle\psi,W\psi\rangle-E_G(\psi)$, by taking the supremum over unit biseparable $\phi$ in its definition. Multiplying by nonnegative weights and summing over any normalized finite ensemble of a density matrix $\sigma$ gives $r\operatorname{Tr}(\sigma W)-\hat E_G(rW)\le\sum_i a_i E_G(\psi_i)$. For unit vectors, Cauchy–Schwarz bounds squared overlaps between zero and one, and `hat_bdd` applies to every real $r$ at $n=d=3$; the overlap and slope sets contain candidates. The nonempty ensemble-value set lies in $[0,1]$, so infimizing over ensembles and taking the supremum over $r$ preserves the lower-bound relation. Equality requires the state to attain the smallest geometric measure compatible with its witness expectation; the competing state $\psi_*$ excludes that possibility for $\rho$.
- *Nearby questions.* The exact value of $E_G(\rho_{3,3}(3/8))$, the equality locus for other $(n,d,p)$, and whether jointly measuring $W$ and $Q$ yields an exact convex-roof estimate remain open here.
- *Effect on the source.* The arXiv text states the equality as an open question, rather than a premise of its witness construction or lower-bound comparison. The strict gap rules out interpreting that lower bound as an exact formula throughout the noisy GHZ family. It does not contradict the source's lower-bound inequality, comparison with the fidelity bound, witness optimality claims, or separate conjecture about robustness as system size increases; their stated arguments do not assume an affirmative answer to this question, and they are not independently verified by this settlement.

## ASSUMED-UNVERIFIED

The literature check is bounded by the searches reported in #25044; it establishes neither exhaustive novelty nor priority. The eight citing works, their screening and the reported Zenodo and repository searches were not independently reproduced. No fresh arXiv version-history check or reading of the journal text is supplied; whether the published version retains the same question is unverified.

The source read is arXiv:2211.05563v1, `GMEwitness.tex`, md5 `e5fc01c6d6faa619a2bc9e11d7a16bb1`, particularly lines 247–325 and 682–701. The statements labelled “Argued, not formalized” are outside the statement of `result`. The source's closed conjugate formula is not formalized; passage from the finite-ensemble definition to a convex roof permitting countably infinite ensembles is not formalized. No exact convex-roof value, general strict-gap family, or settlement of the source's other conjectures is claimed.
