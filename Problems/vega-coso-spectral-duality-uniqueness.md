---
slug: vega-coso-spectral-duality-uniqueness
bibkey: vegacoso2026spectraldualityrigidity
doi: 10.48550/arXiv.2610.16454
url: https://arxiv.org/abs/2610.16454v1
triage: theorem
motivation_gids:
  - D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation.result
---

# Generic global uniqueness fails in the range $N\le m$

## Problem

Juan Antonio Vega Coso, *Axioms and internal rigidity of spectral duality structures*, arXiv:2610.16454v1, Section 9, page 18:

> Likewise, Proposition 4.16 is proved for $N>m$, and the case $N\le m$ is open.

Proposition 4.16, page 11, asserts in the setting of Proposition 4.15, with $N>m$ and (H1), an open dense subset of $\mathcal D=\{D:D\pi=0\}$ with null complement on which every perturbation satisfying (H2) has $\pi$ as its only insensitive distribution, at any level. The question considered here is the universal extension to $N\le m$. The source poses this range as open; it does not assert the extension as a theorem. Preregistration: [#26267](https://github.com/the-omega-institute/trureturing/issues/26267).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $N,m\ge2$, $N\le m$ | The first three hypotheses of `claim` | Includes equality and strict inequality. |
| Strictly positive amplitudes $A$ | All entries of the real matrix are positive | Finite indices are `Fin N` and `Fin m`. |
| Interior distribution $\pi$ and $\beta>0$ | Positive entries summing to one; positive real scalar | No additional restriction on the amplitude matrix. |
| (H1) on $(0,1)$ | `LinearIndependent ℝ f` with domain `Set.Ioo (0 : ℝ) 1` | Literal function domain and linear independence. |
| $\mathcal D=\{D:D\pi=0\}$ | Matrix subtype with `D.mulVec π = 0` | Induced finite-dimensional topology. |
| Generic set | `IsOpen G ∧ Dense G` | The null-complement requirement is omitted: refuting this weaker assertion also refutes the stronger extension. |
| $B=\beta A+D$, (H2) | Expanded sum $\sum_\nu f_\nu(\gamma)(A_{\nu z}+(\beta A_{\nu z}+D_{\nu z}))>0$ | All $z$ and all $\gamma\in(0,1)$. |
| Insensitivity at any level | Every real $c$, every nonnegative $\pi'$ summing to one, and the expanded coupling ratio constant at $c$ | The closed simplex is literal, inlined in the claim; no extra public predicate. |
| Only $\pi$ | Conclusion `π' = π` | Equality of the entire distributions. |
| Negative settlement | `result : ¬ claim` | Closed negation of the universal extension. |

The only public definition is `claim`. Its full right-hand side is the preregistered extension of the quoted question, using the source's definitions of spectral sums and insensitivity (pages 4–5), with the null-complement clause omitted as above. Every binder implements one of these clauses; none assumes the uniqueness conclusion. The source conventions are inlined literally; the proof uses `Matrix.vecMulVec` for the rank-one perturbation and Mathlib's subtype topology.

## Motivation

The settling module is `D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation`, with `generality: G`, `utility: kind=certified-instance; basis=refutes`, and `admission_basis: open-problem-resolution (#26267; Refuted)`. The symbolic two-parameter family is an obstruction on an open subset of the entire perturbation space, which rules out removal by an exceptional nowhere-dense choice. It supplies no classification of all dimensions.

## Gap

The bounded literature screen recorded in #26267 found no settlement of this extension. The source and its later cited papers were screened through arXiv author and text searches; the follow-up arXiv:2610.23684 concerns skeleton semiring factorization and arXiv:2611.01756 concerns stochastic exit-pair orders. Neither supplies this settlement. MathOverflow, Zenodo, AFTD, CoPEER, Machina Mathematica and repository checks yielded no matching settlement in the inspected scope. Semantic Scholar and the OpenAlex citing-work listing were rate limited. The Mangasarian generalized Perron–Frobenius paper was checked through metadata and an abstract/account, without its full primary text. Exhaustive literature completeness is `ASSUMED-UNVERIFIED`; these are preregistration-producer readings.

## Route

Take $N=m=2$, $A=\begin{pmatrix}1&2\\2&1\end{pmatrix}$, $\pi=(1/2,1/2)$, $\beta=1$ and $f(\gamma)=(1,\gamma)$. Write

$$D=\begin{pmatrix}a&-a\\b&-b\end{pmatrix},\qquad q=\left(\frac{2b-a}{a+b},\frac{2a-b}{a+b}\right).$$

The conditions $0<a<1$, $0<b<1$, $a/2<b<2a$ and $a\ne b$ define a nonempty open family. They make $q$ an interior distribution different from $\pi$. Every perturbation with $D\pi=0$ has the displayed coordinate form. The identity $Dq=(b-a)Aq$ gives the constant level $C(q,\gamma)=1/(2+b-a)$, and all source (H2) sums are positive. Every dense set of perturbations meets this open family, contradicting global uniqueness.

## Falsifier

Failure of the coordinate parametrization, the strict inequalities defining a nonempty relatively open set, the distribution properties of $q$, the constant-ratio identity, or the dense-set intersection would invalidate the refutation. These implications are proved by the module's consumed private lemmas and `result`. The closed settling theorem assumes no mathematical hypothesis. The published $N>m$ statement is outside its conclusion.

## Evidence

### Formal evidence

The Lean source is `D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation.lean`; its mirror is `Blueprint/D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation.scribe.cs`. The only public theorem is `D5.S3.ContinuousObservables.SpectralDualityUniquenessRefutation.result`. Its proof and all thirteen private auxiliary theorems have `proof_shape: bind-only` after same-delivery expansion: finite evaluation, algebra/order normalization and direct applications of pinned Mathlib linear-independence and density infrastructure. No escape witness is claimed. Each auxiliary is consumed by another declaration on the settling path. There are no D5 imports or direct frozen prerequisites. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact experiment

[Immutable experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/1b1b992af693545024317f083d815cb170d39f79/docs/reports/arxiv2610.16454-sec9-n_le_m-generic-global-uniqueness).
The program is `docs/reports/arxiv2610.16454-sec9-n_le_m-generic-global-uniqueness/check.py` at that commit, SHA-256 `988a571a3dfdabf15ed61422080e0b4e12e668b3ac4f16616e43f306a164a95c`.
The implementation seat executed `python3 /Users/auric/.op-scratch/op/vc2610sec9-stageb/check.py` on the verified immutable bytes, exit 0, final result `ALL_CHECKS_OK`.
The exact symbolic checks establish $D\pi=0$, $\sum q_i=1$, $Dq=(b-a)Aq$, $Bq=(1+b-a)Aq$ and the two constant coupling ratios as rational identities. The explicit rational point tested is $a=1/2,b=3/4$, with the matrix, distribution, levels and positivity/non-proportionality checks listed in Triage. The script also checks only the strict family inequalities at $(a,b)=(1/3,1/2)$ and $(3/5,7/10)$. This computation does not classify dimensions or replace the topology proof.

## Triage

### What the settlement shows

1. **Proved (kernel-checked):** The universal $N\le m$ extension fails already at $N=m=2$, $A=[[1,2],[2,1]]$, $\pi=(1/2,1/2)$, $\beta=1$, $f=(1,\gamma)$. Evidence: `result`, using `base_positive`, `base_interior` and `base_independent`.
2. **Proved (kernel-checked):** The obstruction occupies a nonempty relatively open subset of the entire space $D\pi=0$, so no dense generic subset can avoid it. Every member satisfies (H2) and has a distinct interior insensitive distribution $q$. Evidence: `perturbation_coordinates`, `badSet_open`, `badSet_nonempty`, `second_interior`, `second_ne`, `badSet_failure`, and their use in `result`. The stronger interiority fact is the statement of `second_interior`; `badSet_failure` packages the closed-simplex conclusion needed by `claim`.
3. **Proved (kernel-checked):** The algebraic mechanism is $Dq=(b-a)Aq$ and the resulting level $1/(2+b-a)$. Evidence: `second_algebra` and `family_coupling`.
4. **Computed:** At $a=1/2,b=3/4$, $q=(4/5,1/5)$, $B=[[3/2,3/2],[11/4,1/4]]$, $C(\pi,\gamma)=1/2$ and $C(q,\gamma)=4/9$. At this point $A$ has full rank, $A$ and $B$ are positive, and neither column of $B$ is proportional to either column of $A$. Evidence: the immutable experiment, command, exit 0 and SHA-256 in the experiment entry. These exact values and the column tests are computation, rather than separately stated Lean theorems.
5. **Open:** A full classification of the $N\le m$ range and the strict $N<m$ subrange is not supplied. The published $N>m$ theorem and fixed-level uniqueness variants are separate statements, not re-proved here.

The failure mechanism is a second generalized eigenvector in the probability simplex: (H1) and (H2) do not force a single insensitive distribution across all levels when $N=m=2$. The two levels differ because $a\ne b$. Fixed-level uniqueness is therefore not contradicted by this family. No result in the published $N>m$ range is refuted, and no formal dependency audit of all the source's other results is claimed; any conclusion requiring the universal affirmative $N\le m$ extension loses that premise.

## ASSUMED-UNVERIFIED

Literature completeness and the inaccessible citation-list/full-primary-text checks remain `ASSUMED-UNVERIFIED`. Source and literature readings are attributed to the preregistration producers. The strict $N<m$ case, the full classification and the dependency audit of other source results remain open. No empirical or physical realization claim is made.
