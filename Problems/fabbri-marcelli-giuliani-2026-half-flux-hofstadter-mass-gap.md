---
slug: fabbri-marcelli-giuliani-2026-half-flux-hofstadter-mass-gap
bibkey: fabbrimarcelligiuliani2026conductivity
doi: 10.48550/arXiv.2609.03832
url: https://arxiv.org/abs/2609.03832v1
triage: theorem
motivation_gids:
  - D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.result
---

# A uniform mass gap for the π/2-flux Hofstadter model

## Problem

S. Fabbri, G. Marcelli and A. Giuliani, *The conductivity matrix at the topological phase transition*, arXiv:2609.03832v1 (2026), Section 3.1, leave an analytic gap assertion supported by numerical evidence. In the source member `FMG_v1.tex`, lines 689–690, they write (mathematical macros expanded and the assumption cross-reference rendered):

> In the `MathematicaNotebook1.nb` sheet we provide numerical evidence of the validity of Assumption 2.1, and specifically of the fact that for all $m\in[-2,2]\setminus\{0\}$, $\min_{\vec{k}\in\mathbb{B}}(\lambda_4(\vec{k};m)-\mu)>0$ and $\max_{\vec{k}\in\mathbb{B}}(\lambda_3(\vec{k};m)-\mu)<0$. We expect that, with some additional technical effort, this can be fully proved analytically, but we prefer not to belabor the details of such a proof here.

Their Bloch Hamiltonian is Eq. `eqn:Hofst_Hamiltonian`, lines 663–671:

$$
H(\vec k;m)=-\begin{pmatrix}
d&1-i e^{2ik_1}&1-i e^{2ik_2}&0\\
1+i e^{-2ik_1}&0&0&-i+e^{2ik_2}\\
1+i e^{-2ik_2}&0&0&1+i e^{2ik_1}\\
0&i+e^{-2ik_2}&1-i e^{-2ik_1}&-d
\end{pmatrix},\qquad d=2+m.
$$

The substitution $d=2+m$ and the Fermi energy are specified at lines 686–687. Write $\lambda_1\le\lambda_2\le\lambda_3\le\lambda_4$ for its real eigenvalues, counted with multiplicity, $\vec k_F=(\pi/4,\pi/4)$, and $\mu:=\lambda_3(\vec k_F;0)$.

Issue [#22177](https://github.com/the-omega-institute/trureturing/issues/22177) fixes the reading: $\lambda_4(\vec k_F;0)=\mu$, and for every real $m\in[-2,2]\setminus\{0\}$ there is $\delta>0$ such that

$$
\mu+\delta\le\lambda_4(\vec k;m),\qquad
\lambda_3(\vec k;m)\le\mu-\delta
\quad\text{for every }\vec k\in\mathbb R^2.
$$

The same $\delta$ works for all momenta at a fixed mass; it may depend on the mass. This is proved.

## Motivation

The gap is a premise for applying the source's main conductivity theorem to its four-band Hofstadter example. A proof replaces the numerical support for the nonzero-mass gap with a uniform analytic inequality, while keeping distinct the remaining hypotheses concerning the massless bands and their conical crossing. The model and the source quotations are also recorded in [the literature note](../Library/StatisticalMechanics/fabbrimarcelligiuliani2026conductivity.md).

## Gap

The bounded literature check recorded in #22177 reports:

- the v1 source retains the analytic expectation;
- OpenAlex lists zero citing works for `W7208771349`, and the arXiv title-phrase search finds only the source among relevant works;
- the repository search finds no earlier issue, module, Library note or dossier for arXiv:2609.03832;
- MathDB and formal-conjectures have no match, and INSPIRE has no record;
- Semantic Scholar and Google Scholar are unavailable to that check.

`not-found-in-searched-scope`.

## Route

All momenta and masses below are real. Put $z_j=e^{2ik_j}$, $y_j=\operatorname{Im}z_j$, $d=2+m$, and $K=H-2I$.

1. **Hermiticity and the reference energy.** `bloch_isHermitian` holds for every real $k_1,k_2,m$. At the fixed point $(k_1,k_2,m)=(\pi/4,\pi/4,0)$, `fermi_charpoly` gives $X(X+4)(X-2)^2$, and `fermi_bands` identifies both the third and fourth bands with $2$. Thus the defined Fermi energy is $2$.
2. **The Schur certificate.** For every real $k_1,k_2,m$, `schur_congruence` gives a determinant-one congruence of the coordinate-reordered $K$ with $\operatorname{diag}(S,-2I_2)$. The coordinate order is $(1,4,2,3)$, and
   $$
   S=\begin{pmatrix}y_1+y_2-d&t\\\overline t&d-y_1-y_2\end{pmatrix},\qquad
   t=\frac{(1-i)(1-z_1+z_2+z_1z_2)}2.
   $$
   The congruence matrix is $P=\begin{pmatrix}I_2&0\\B^*/2&I_2\end{pmatrix}$, where $B$ has rows $(-1+iz_1,-1+iz_2)$ and $(-i-\overline z_2,-1+i\overline z_1)$. For complex $z_1,z_2$ with $|z_1|=|z_2|=1$, `offDiagonal_normSq` gives $|t|^2=2(1-y_1y_2)$; with any real $d$, `schur_det` gives $\det S=-q$, where
   $$q=(y_1-d)^2+(y_2-d)^2+2-d^2.$$
   `phase_norm` supplies the unit-modulus hypotheses for every real momentum. Consequently, `shifted_det` states $\det K=-4q$ for every real $k_1,k_2,m$.
3. **Strict positivity.** For real $y_1,y_2,m$ with $y_1\le1$, $y_2\le1$ and $m\ge-2$, `gapPolynomial_lower` proves $q\ge m^2/2$ at $d=2+m$. For every real momentum, the phase norms imply $y_j\le1$. Thus `gap_positive`, whose mass hypotheses are $m\ge-2$ and $m\ne0$, gives $q>0$.
4. **The band cut.** For complex unit-modulus $z_1,z_2$ and real $d$, assuming $q>0$ and that $\operatorname{diag}(S,-2I_2)$ is Hermitian, `schur_positive_index` proves its positive index is one. For every real $k_1,k_2,m$ with $m\ge-2$ and $m\ne0$, `shifted_inertia` transfers this count through the invertible congruence, uses the nonzero determinant to obtain rank four, and gives positive index one and negative index three for $K$. Under precisely these mass hypotheses, `band_signs` gives $\lambda_3<2<\lambda_4$ for every real momentum.
5. **A uniform distance.** For real $k_1,k_2,m$ with $-2\le m\le2$, and every row index in $\mathrm{Fin}\,4$, `row_bound` bounds the sum of entry norms by $10$; for every eigenvalue index, `shifted_eigenvalue_bound` uses Gershgorin to bound its absolute value by $10$. Under the same mass bounds, for every real momentum and every band index in $\mathrm{Fin}\,4$, `band_distance` proves $|\operatorname{band}(k_1,k_2,m,j)-2|\ge m^2/500$: the determinant has absolute value at least $2m^2$, and the product of the other three absolute eigenvalues is at most $1000$. This lemma does not require $m\ne0$.
6. **Conclusion.** For $-2\le m\le2$ and $m\ne0$, `result` combines `band_signs`, `band_distance` and `fermi_bands`, choosing $\delta=m^2/500>0$, to prove `claim`.

## Falsifier

A gap for a different Hamiltonian, a different band ordering, or only finitely many momenta would not settle this question. Here `bloch` includes the source's overall minus sign and the substitution $d=2+m$ entry by entry. `band` reverses Mathlib's decreasing eigenvalue index, so its indices $2$ and $3$ are exactly the source's third and fourth bands, with multiplicity. `fermiEnergy` is the third band at the specified zero-mass Fermi point.

The formal claim uses a common positive lower bound over all real momenta directly. It contains no infimum or supremum whose nonemptiness or boundedness is being presumed. The passage to attained extrema on the Brillouin torus is an additional analytic interpretation, described below; the classification of all zero-mass Fermi points is outside `result`.

## Evidence

The canonical source is `D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.lean` (495 lines).

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/SpectralTopology/HalfFluxHofstadterMassGap.lean.json`, statement `sha256:b2d6d41513472a3078b8e74ec71344c90c343870d3a031e7006e2a675beb098d`.

Declaration statements:

- `result`: `sha256:67e16a9d962355b62d6a41ea695120427775638f4f9ceb134e114b625e2eb2bd`;
- `claim`: `sha256:9484ef96870a727848baa40fb8471008d4fc61eba8ef80d4d90fec1771b50b94`.

## Triage

Tier 1 analytic expectation of a 2026 preprint, supported numerically by its authors, preregistered in issue #22177 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the fourth band at $(\pi/4,\pi/4)$ and zero mass equals $\mu:=\lambda_3(\pi/4,\pi/4;0)$; for every real $m$ with $-2\le m\le2$ and $m\ne0$, there exists a real $\delta>0$ such that $\mu+\delta\le\lambda_4(k_1,k_2;m)$ and $\lambda_3(k_1,k_2;m)\le\mu-\delta$ for all real $k_1,k_2$.

**Computed, not formalized** (orchestrator, Claude Code/Opus, recorded in #22177):

- For the sixteen tested nonzero masses in $[-2,2]$ on a $241\times241$ momentum grid, no violation of either separation inequality with gap $m^2/500$ was observed.
- At 2000 tested random momentum–mass triples, the shifted matrix had exactly three negative eigenvalues and the determinant identity agreed to within $10^{-13}$.

**Argued, not formalized.**

- *Decisive mechanism.* A negative product of four real eigenvalues permits either one or three negative factors, so a negative determinant alone cannot select the required band cut. For every real momentum and $m\ge-2$, $m\ne0$, `shifted_inertia` supplies the missing information: exactly three eigenvalues lie below $2$ and one above it. The determinant estimate then controls their distances, rather than merely their signs.
- *Extrema interpretation.* The matrix entries are continuous and $\pi$-periodic in each momentum, and ordered eigenvalues of Hermitian matrices are continuous. They therefore descend to continuous functions on the compact momentum torus, where their extrema are attained. The uniform inequalities give the strict minimum and maximum in the source quotation; conversely, those strict extrema give a common positive $\delta$ by taking the smaller separation. Neither this compactness bridge nor continuity and periodicity are assertions of `result`.
- *Removing the upper mass cutoff.* Fix any real $m\ge-2$ with $m\ne0$. `phase_norm` applies to all real momenta; direct inspection of the entries bounds each row sum of $K$ by $m+8\ge6$, since its diagonal magnitudes are at most $m+4$ and each of its two nonzero off-diagonal entries has norm at most $2$. Gershgorin therefore bounds every shifted eigenvalue in absolute value by $m+8$. The identity `shifted_det` for all real parameters and `gapPolynomial_lower` for $y_1,y_2\le1$, $m\ge-2$ give $|\det K|\ge2m^2$. Dividing out the other three eigenvalue bounds gives distance at least $2m^2/(m+8)^3>0$; `band_signs`, for real momenta and $m\ge-2$, $m\ne0$, supplies the directions. Thus the same argument extends the uniform assertion to every such fixed mass, although this extended assertion and bound are not formalized here.
- *Sharpness and the massless boundary.* At $\vec k_F$, the fourth coordinate vector is an eigenvector of $H$ with eigenvalue $2+m$, as direct substitution of $z_1=z_2=i$ shows. For every $m>0$, `band_signs` applies and identifies the unique eigenvalue above $2$ with the fourth band, so any admissible uniform gap at that mass is at most $m$. Hence no positive gap can be uniform also over all masses approaching zero. The bound used by the proof does not identify the optimal gap or its sharp asymptotic rate; these are neighbouring questions left undetermined here.
- *Effect on the source.* The nonzero-mass gap premise in the source's Section 3.1 application of its main conductivity theorem has an analytic justification. That application, including the conductivity conclusion at lines 706–710, still additionally needs the remaining model hypotheses: the zero-mass Fermi-point classification, separation of the other bands, and conical asymptotics. These and the conductivity theorem itself are not formalized by this settlement. The source's other flux examples and its questions concerning interactions or disorder are unaffected.

## ASSUMED-UNVERIFIED

The literature search is bounded and does not establish exhaustive worldwide novelty or priority. The OpenAlex, arXiv title-phrase, repository, MathDB, formal-conjectures and INSPIRE search readings are reported in #22177 and were not independently reproduced; Semantic Scholar and Google Scholar were unavailable to that search. The issue's floating-point computations were not independently reproduced, and the source's ancillary notebook was not executed. The statements under "Computed, not formalized" and "Argued, not formalized" are not formalized here. In particular, no formal proof is claimed here for the torus-extrema bridge, the extended mass range, optimality or asymptotics of the gap, the remaining source assumptions, or any conductivity formula.
