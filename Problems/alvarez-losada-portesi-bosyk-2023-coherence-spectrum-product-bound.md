---
slug: alvarez-losada-portesi-bosyk-2023-coherence-spectrum-product-bound
bibkey: alvarezlosadaportesibosyk2023complementarity
doi: 10.1088/1572-9494/acc92f
url: https://ctp.itp.ac.cn/EN/PDF/10.1088/1572-9494/acc92f
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.result
---

# The coherence vector and spectrum satisfy the product bound in every positive dimension

## Problem

Y. Alvarez, M. Losada, M. Portesi and G. M. Bosyk, *Complementarity between quantum coherence and mixedness: a majorization approach*, Communications in Theoretical Physics 75(5), 055102 (2023), DOI 10.1088/1572-9494/acc92f, Section 3.4, journal PDF p. 7:

> Finally, we state a conjecture for the greatest component of $\nu(\rho)\otimes\lambda(\rho)$ that allows us to obtain a nonoptimal but nontrivial bound for the tensor-product majorization relation, which depends only on the dimension of the Hilbert space.

> Conjecture 5. Let $\rho\in\mathcal S(\mathcal H_d)$. Then $\nu_1(\rho)\lambda_1(\rho)\ge\frac1d$. (20)

> For $d=2$ the conjecture is clearly valid, whereas for $d=3$ we have numerical evidence of its validity.

Here $\mathcal S(\mathcal H_d)$ is the set of density operators on the $d$-dimensional Hilbert space, with a fixed incoherent basis. Section 2.2, Eqs. (9)–(12), PDF p. 3, defines the pure-state squared-amplitude vector $\mu(|\psi\rangle\langle\psi|)$, its decreasing rearrangement $\mu^\downarrow$, and

$\mathcal U^{\rm psd}(\rho)=\{\sum_jp_j\mu^\downarrow(|\psi_j\rangle\langle\psi_j|):\rho=\sum_jp_j|\psi_j\rangle\langle\psi_j|\}$,

where the ensembles are finite, their weights are nonnegative and sum to one, and their vectors have norm one. The source defines $\nu(\rho)=\bigvee\mathcal U^{\rm psd}(\rho)$ in the majorization lattice; Section 2.3, PDF p. 4, defines $\lambda(\rho)$ as the decreasingly ordered spectrum. Thus the subscript $1$ denotes the greatest component in each vector. The definitions are also recorded in [the literature note](../Library/Entropy/alvarezlosadaportesibosyk2023complementarity.md).

Issue [#23165](https://github.com/the-omega-institute/trureturing/issues/23165) fixes the formal reading: for every $d\ge1$, every positive semidefinite complex $d\times d$ matrix $\rho$ of trace one, and every decreasing, nonnegative vector $\nu$ of sum one that majorizes every member of $\mathcal U^{\rm psd}(\rho)$, one has $\nu_1\lambda_1(\rho)\ge1/d$. This is proved. Applying it to the source's supremum uses that supremum's upper-bound property; the module does not construct the majorization lattice.

## Motivation

The paper studies the tensor product of vectorial measures of coherence and mixedness, retaining their majorization information instead of choosing a scalar measure. Its greatest component is $\nu_1(\rho)\lambda_1(\rho)$. A dimension-dependent lower bound on this component gives the nontrivial common majorization lower bound proposed in Eq. (21), beyond the paper's analytic qubit result and numerical qutrit investigation.

## Gap

The bounded literature check in #23165 records:

- the orchestrator's reading of the journal PDF retains Conjecture 5, with the source reporting the qubit case and numerical evidence for qutrits;
- the oracle-reported search found no publication settling Eq. (20), over searches of Zenodo, ResearchGate, SSRN and GitHub and a check of Aziz–Song–Ye–Wang, Physical Review Research 7, 023221 (2025);
- the orchestrator's issue and repository searches for the DOI suffix, Bosyk, Alvarez and coherence vectors found no existing settlement of this statement.

The oracle's related-work leads are Bosyk et al. (2021), Physical Review A 103, 012403, and Kumar (2017), Physics Letters A 381, 991–997, arXiv:1508.00262v3. Those readings and the oracle's searches were not independently reproduced here; no formula from either work is used as a premise of the formal proof.

`not-found-in-searched-scope`.

## Route

Write $A=\sqrt\rho$, $s=\sum_j(\operatorname{Re}A_{jj})^2$, $t=\operatorname{Re}\operatorname{Tr}A$, and $L=\texttt{maxEigenvalue}\,\rho$. The following helper names refer to the canonical module.

1. **A normalized column ensemble.** For $d\ge1$ and $\rho$ positive semidefinite with trace one, `column_ensemble` supplies $p:\mathrm{Fin}\,d\to\mathbb R$ and unit vectors $\psi_j$ with `IsDecomposition` $\rho\ d\ p\ \psi$, $p_j=\operatorname{Re}\rho_{jj}$, and $p_j|\psi_j(i)|^2=|A_{ij}|^2$ for every $i,j$. For $p_j>0$ the vector is the $j$th column of $A$ divided by $\sqrt{p_j}$; for $p_j=0$ the column vanishes and the assigned vector is the first coordinate unit vector with weight zero.
2. **The first component.** For $d\ge1$, any complex $d\times d$ matrix $\rho$, any $\nu$ satisfying `IsMajorizationUpperBound` $\rho\ \nu$, and any $p,\psi$ satisfying both `IsDecomposition` $\rho\ d\ p\ \psi$ and $p_j|\psi_j(i)|^2=|A_{ij}|^2$ for every $i,j$, `first_component_bound` gives $s\le\nu_1$. It uses the length-one majorization inequality for the ensemble average $u\in\texttt{coherenceSet}\,\rho$. The comparison of a coordinate with the largest sorted coordinate is `rearrangement_max`, whose hypotheses are $d\ge1$, an arbitrary real vector $x:\mathrm{Fin}\,d\to\mathbb R$, and an index $i:\mathrm{Fin}\,d$.
3. **The diagonal and spectral estimates.** For every natural $d$ and every complex $d\times d$ matrix $\rho$, `diagonal_cauchy_schwarz` gives $t^2\le d s$. For every positive semidefinite $\rho$ of trace one, `trace_sqrt_spectral` identifies $t=\sum_i\sqrt{\lambda_i}$. With the additional hypothesis $d\ge1$, `spectral_bound` proves $L>0$ and $1/\sqrt L\le t$: the eigenvalues are nonnegative, sum to one and satisfy $\lambda_i\le L$, so $\lambda_i\le\sqrt{\lambda_i}\sqrt L$.
4. **Assembly.** For a natural $d\ge1$ and real $v,l,t,s$ satisfying $l>0$, $1/\sqrt l\le t$, $t^2\le d s$ and $s\le v$, `assemble_bound` gives $1/d\le vl$. The theorem `result` applies it with $v=\nu_1$ and $l=L$.

## Falsifier

A proof would miss the source question if its ensembles, ordering or spectral quantity differed from the source's. The module uses squared complex moduli in the fixed basis, finite decompositions into unit vectors, and decreasing rearrangements before averaging. `IsMajorizationUpperBound` requires that $\nu$ is decreasing, nonnegative and has sum one, with all partial sums dominating those of the decreasing rearrangement of every member of `coherenceSet`; equality of total sums is also required by `Majorizes`.

For Hermitian $\rho$, `maxEigenvalue` is the real supremum of its finite eigenvalue range. For $d\ge1$ this range is nonempty and bounded above; for positive semidefinite $\rho$ of trace one, `spectral_bound` additionally proves that its supremum is positive. The fallback value on non-Hermitian matrices is outside the hypotheses of `result`. The column ensemble supplies an actual member of the coherence set, including when some weights vanish. There is no optimization-existence assumption hidden in a scalar infimum or supremum of ensemble values.

## Evidence

The canonical source is `D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.lean`.

- **Proof.** It proves `result` with the universally quantified hypotheses and product inequality stated above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Information/CoherenceVectorSpectrumProductBound.lean.json`.

Declaration statements:

- `result`: `sha256:28288867dc57f37c3742cf3234e9b36acc7a734f2f20b79c78a227ce922c3255`.

## Triage

Tier 1 conjecture of a 2023 paper, preregistered in issue #23165 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $d\ge1$, every positive semidefinite complex $d\times d$ matrix $\rho$ of trace one, and every decreasing, nonnegative real vector $\nu$ of sum one that majorizes every finite pure-state decomposition average in `coherenceSet` $\rho$, $1/d\le\nu_1\,\texttt{maxEigenvalue}\,\rho$.

**Computed, not formalized:** the random states of dimensions two to six that the orchestrator recorded in #23165 agree with the formal inequality.

**Argued, not formalized.**

- *Mechanism and bridge to the source.* For $d\ge1$ and positive semidefinite $\rho$ of trace one, `column_ensemble` supplies one normalized finite ensemble, including zero weights. Given any decreasing, nonnegative mass-one vector $\nu$ majorizing every such ensemble average, `result` applies without needing an optimizing ensemble or a least upper bound. In particular, the source's majorization supremum is such an upper bound by definition, so substituting it supplies the bridge to Conjecture 5 in the source's dimensions $d\ge2$.
- *Sharpness of the constant.* For $\rho=I_d/d$, the equally weighted coordinate basis decomposition gives the ordered average $(1,0,\ldots,0)$; hence the source's coherence vector is that top vector, while $\lambda_1=1/d$, giving equality. For a pure state with all squared amplitudes $1/d$, every positive-weight vector in any pure-state decomposition lies on the same ray: for a vector $w$ orthogonal to that ray, $0=\langle w,\rho w\rangle=\sum_jp_j|\langle w,\psi_j\rangle|^2$ forces each positive-weight term to vanish. Thus every decomposition average is uniform, the source's coherence vector is uniform and $\lambda_1=1$, again giving equality. These examples apply in every $d\ge1$, so the dimension-only constant cannot be increased.
- *Effect on Eq. (21).* Immediately below Conjecture 5 the source states, “If this conjecture is true, it follows that”, introducing its common majorization lower bound $b_d=(1/d,(d-1)/(d(d^2-1)),\ldots,(d-1)/(d(d^2-1)))$ for $d\ge2$. To verify that consequence, let $x=(\nu(\rho)\otimes\lambda(\rho))^\downarrow$, with $N=d^2$ components. Its first component is at least $1/d$. For $1\le k\le N$, decreasing order makes the sum of the first $k-1$ tail components at least $(k-1)(1-x_1)/(N-1)$, so $\sum_{i=1}^kx_i\ge x_1+(k-1)(1-x_1)/(N-1)\ge1/d+(k-1)(1-1/d)/(N-1)$. These are precisely the partial sums of $b_d$, with equal total sums. Consequently $b_d$ is a common majorization lower bound and lies below the lattice infimum in Eq. (21), using the source's lattice construction. The conjectural premise of this consequence is discharged; the tensor-product majorization statement and lattice infimum are not formalized by `result`.
- *Neighbouring questions.* The complete equality characterization and the optimal common tensor-product majorization bound in general dimension remain open here. The product estimate alone does not identify the remaining partial sums of that optimal bound or certify the source's numerical qutrit estimates. Corollaries 6–7 in Section 3.5 use the earlier majorization results, rather than Conjecture 5; this settlement does not formalize those scalar complementarity statements.

## ASSUMED-UNVERIFIED

The bounded literature check in #23165 does not establish exhaustive worldwide novelty or priority. The oracle-reported searches, its reading of Aziz–Song–Ye–Wang (2025), the two related-work leads, and the orchestrator's repository deduplication and numerical checks were not independently reproduced here. The journal PDF was read directly for the definitions, Conjecture 5, Eq. (21) and the dependencies of Corollaries 6–7.

The source's complete majorization lattice, the construction and leastness of its coherence-vector supremum, and the explicit instantiation of that supremum in `result` are not formalized in this module. The sharpness examples, the derivation of Eq. (21) and all other statements under “Argued, not formalized” are prose arguments, not additional Lean declarations. The reported computations do not prove untested cases. A complete equality classification, the optimal tensor-product bound beyond the established product estimate, and the source's other tensor-product and scalar results are not settled by this module.
