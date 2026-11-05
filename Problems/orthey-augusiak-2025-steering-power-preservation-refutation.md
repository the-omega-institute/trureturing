---
slug: orthey-augusiak-2025-steering-power-preservation-refutation
bibkey: ortheyaugusiak2025steering
doi: 10.1088/1367-2630/adda73
url: https://arxiv.org/abs/2410.20477v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.result
---

# The steering substitution need not preserve powers

## Problem

A. C. Orthey Jr and R. Augusiak, *Certifying classes of $d$-outcome measurements with quantum steering*, New J. Phys. 27, 064501 (2025), arXiv:2410.20477v2, Appendix “Robust self-testing”, Conjecture 1:

> For any prime $d$, we have that $\widetilde{B}_k^{(n)}=\widetilde{B}_k^n$, for every $n\in\{1,\ldots,d-1\}$. Note that this statement is true for $d=3$.

This quotation is from the downloaded v2 source `main2.tex`, line 1272, MD5 `b3c5b40a34f721352981dcf58659087e`. Its projective setting is explicit at line 1263:

> For simplicity, we will assume that the state is pure and the measurements performed by Bob are projective.

Write $\omega=e^{2\pi\mathrm i/d}$ and let $\oplus$ denote addition modulo $d$. The coefficients and substitution of lines 204–206 and 246–249 are

$\gamma_{yk}^{(n)}=\frac1d\omega^{kn(n-1)/2}\sum_{l=0}^{d-1}e^{-\mathrm i\sum_{m=1}^n\phi_{l\oplus m,y}}\omega^{knl}$,

$\widetilde B_k^{(n)}=\sum_y\gamma_{yk}^{(n)}B_y^n$, with $\widetilde B_k=\widetilde B_k^{(1)}$ in the projective setting of lines 293–305.

Issue [#21069](https://github.com/the-omega-institute/trureturing/issues/21069) fixes the following reading. For every prime $d$, every real phase array $\phi$ satisfying $\sum_j\phi_{j,y}=0$ for every $y$ and

$\sum_k\overline{\gamma_{y'k}^{(n)}}\gamma_{yk}^{(n)}=\delta_{yy'}$

for every $1\le n\le d-1$ and every $y,y'$, every family of unitary $d\times d$ complex matrices $B_y$ with $B_y^d=I$, every $k\in\{0,\ldots,d-1\}$ and every $1\le n\le d-1$, the identity $\widetilde B_k^{(n)}=(\widetilde B_k^{(1)})^n$ holds. This is `claim`; `result` refutes it. The definitions and source locators are also given in [the literature note](../Library/QuantumContext/ortheyaugusiak2025steering.md).

## Motivation

The substitution transfers the source's reference Heisenberg–Weyl operators into operators formed from Bob's unknown measurements. Identifying the independently transformed powers with powers of one operator is the step used in the appendix's robustness argument at lines 1331–1337. Whether this identification follows from phase admissibility and projectivity determines whether that argument applies to arbitrary prime dimensions under those assumptions.

## Gap

The bounded literature check recorded in #21069 reports:

- arXiv:2410.20477v2 retains Conjecture 1;
- OpenAlex W4410488541 and Crossref report zero citing works;
- the related works arXiv:2607.04035v2 and arXiv:2606.21362v3 do not treat the conjecture;
- MathDB, google-deepmind/formal-conjectures, and the repository search contain no settlement of this conjecture.

`not-found-in-searched-scope`. Only the source-paper reading is independently reproduced here; the other search readings remain attributed to #21069.

## Route

All witness objects below are the module's fixed five-dimensional objects. Put $\omega=\operatorname{windowRoot}(5)$, $X=\operatorname{shift}$ and $Z=\operatorname{clock}$, where $Xe_j=e_{j+1}$ modulo five and $Ze_j=\omega^je_j$. For every $y\in\{0,\ldots,4\}$, set

$\phi_{\cdot,y}=\frac{2\pi}{5}(-6y,0,y-1,1+2y,3y)$,

$R_y=\sum_{k=0}^4\overline{\gamma_{yk}^{(1)}}XZ^k$, and $B_0=\omega R_0$, $B_y=R_y$ for $y\ne0$.

1. **Admissibility.** `phases_zero` gives the zero phase sum for every $y\in\mathrm{Fin}\,5$. `coefficient_orthogonality` gives the required row orthogonality for natural $n$ with $1\le n\le4$ and every $y,y'\in\mathrm{Fin}\,5$. Its finite identities use `coefficient_formula` and the fixed-root identities of `root_relations`: $\omega^5=1$, $1+\omega+\omega^2+\omega^3+\omega^4=0$, and $\overline\omega=\omega^4$. Together these give `phases_admissible : Admissible 5 phases`.
2. **Projectivity.** For every $y,i,j\in\mathrm{Fin}\,5$, `reference_entry` gives $(R_y)_{ij}=0$ unless $i=j+1$ modulo five, and at that entry gives $\omega^{(a_j+yj)\bmod5}$, where $a=(0,4,1,0,0)$. With the fixed unitary $U=\operatorname{diag}(1,1,\omega^4,1,1)$, `reference_factorization` gives $R_y=U(XZ^y)U^*$ for every $y\in\mathrm{Fin}\,5$. `reference_projective` gives unitarity and $R_y^5=I$ for each such $y$, using the reused Weyl displacement power law. `witness_projective` gives `IsProjectiveFamily 5 B`, including the scalar modification at $y=0$.
3. **The two required reconstructions.** For these fixed phases and $R_y$, `reconstruction` gives $\sum_y\gamma_{y0}^{(1)}R_y=X$ and $\sum_y\gamma_{y0}^{(2)}R_y^2=X^2$. These statements concern only $k=0$ and powers $1,2$. With the fixed $g=(3+\omega+\omega^4)/5$, `special_coefficients` gives $\gamma_{00}^{(1)}=\gamma_{00}^{(2)}=g$. Consequently `transformed_one` and `transformed_two` give $\widetilde B_0^{(1)}=X+(\omega-1)gR_0$ and $\widetilde B_0^{(2)}=X^2+(\omega^2-1)gR_0^2$ for this witness.
4. **A nonzero entry.** For this same witness, `defect_entry` identifies the $(0,3)$ entry of $(\widetilde B_0^{(1)})^2-\widetilde B_0^{(2)}$ with $g(g-1)(\omega-1)^2$. `g_nontrivial` gives $g\ne0,1$, using $(\omega+\omega^4)^2+(\omega+\omega^4)=1$; primitivity gives $\omega\ne1$. Applying `claim` at the prime $d=5$, these admissible phases, this projective family, $k=0$, and $n=2$ with $1\le2\le4$ would force this entry to vanish. This contradiction is `result : ¬ claim`.

The named witness lemmas are private, consumed helpers of `result`.

## Falsifier

A discrepancy between the formal coefficients, admissibility conditions, or measurement model and the source would invalidate the intended settlement. The module uses the source's phase indices $l\oplus m$ with $m=1,\ldots,n$, the conjugated row indexed by $y'$ in coefficient orthogonality, and projective Fourier components $B_{n|y}=B_y^n$. It requires both unitarity and $B_y^d=I$ for every $y$.

The module restricts Bob's Hilbert space to $\mathbb C^d$, a subcase of the source's arbitrary Bob space. Its `claim` has no shared-state or steering-violation hypothesis. The settlement addresses the unconditional operator identity preregistered in #21069; it does not assert a counterexample to a robustness bound under an additional near-maximal-violation hypothesis.

## Evidence

The canonical source is `D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.lean` (339 lines).

- **Proof.** It proves `result : ¬ claim`.
- **Definitions.** `coeff`, `Admissible`, `IsProjectiveFamily`, `transformed`, and `claim` encode the coefficients, hypotheses, substitution, and universal identity above.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Measurements/SteeringPowerPreservationRefutation.lean.json`, statement `sha256:da7d239d5d7d5c3218aa534cddba8cffb465ed7ce2bd72c10ad9cd468f13d20d`.

Declaration statements:

- `result`: `sha256:73a149a006ead24883e04715d35fc248207f8e73b825c0f0f8f42a956f4e330b`;
- `claim`: `sha256:2985db26f8f1a0f930ef162ff2498ec73923e6071220be3a125a850a84cd3847`.

## Triage

Tier 1 explicit conjecture of Orthey and Augusiak (2025; arXiv:2410.20477v2), preregistered in issue #21069 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that for every prime $d$, every admissible phase array, every projective family of $d\times d$ complex matrices, every $k\in\mathrm{Fin}\,d$, and every natural $n$ with $1\le n\le d-1$, the transformed $n$th operator equals the $n$th power of the first transformed operator. Here admissibility includes zero phase sums and coefficient row orthogonality at every such power, and projectivity includes unitarity and $B_y^d=I$ for every $y$.

**Argued, not formalized**.

- *Mechanism and missing structure.* For fixed $k$, write $c_y=\gamma_{yk}^{(1)}$. Expanding the square gives $\sum_y c_y^2 B_y^2+\sum_{y\ne z}c_yc_zB_yB_z$, whereas the separately transformed second operator is $\sum_y\gamma_{yk}^{(2)}B_y^2$. Coefficient row orthogonality does not impose this product identity for arbitrary projective $B_y$. For the fixed five-dimensional witness, `transformed_one`, `transformed_two`, and `defect_entry`, with precisely the phases and matrices of Route, isolate the uncancelled contribution. Multiplying $R_0$ by $\omega$ preserves its fifth power and unitarity but changes the two transformed expressions incompatibly.
- *A sufficient repair.* For a fixed prime $d$ and fixed $k$, suppose additionally that some $y_0$ and scalar $\lambda$ with $\lambda^d=1$ satisfy $\gamma_{yk}^{(n)}=\lambda^n\delta_{y,y_0}$ for every $y$ and every $1\le n\le d-1$. Then $\widetilde B_k^{(n)}=\lambda^nB_{y_0}^n=(\lambda B_{y_0})^n=(\widetilde B_k^{(1)})^n$. This is a sufficient extra compatibility condition, not a consequence of admissibility established here. A classification of weaker sufficient conditions is open.
- *Nearby cases.* The $n=1$ identity is immediate from the definition for every input. For the fixed unmodified reference family $B_y=R_y$ in dimension five, `reconstruction` establishes the identity at $k=0$ for powers $1,2$ only. The module does not settle the source's assertion for all admissible qutrit phases, nor classify primes beyond five.
- *Effect on the source.* Orthey and Augusiak's appendix explicitly assumes Conjecture 1 at lines 1275–1276 and uses it at lines 1331–1337. Its proposed extension to arbitrary prime $d>3$ therefore lacks the claimed unconditional identity; that step needs an additional hypothesis or a replacement estimate. This refutation alone does not disprove the resulting robustness inequalities under their steering-violation hypotheses. The main text's robustness theorem is restricted to $d=3$ (lines 528–544), which is not settled here. The exact self-testing theorems at maximal violation (lines 311–377) concern additional state-dependent hypotheses; `result` supplies no counterexample to them.

## ASSUMED-UNVERIFIED

The bounded literature check in #21069 does not establish exhaustive worldwide novelty or priority. Its OpenAlex/Crossref citation counts, readings of arXiv:2607.04035v2 and arXiv:2606.21362v3, and MathDB, google-deepmind/formal-conjectures, and repository no-hit searches were reported there and are not independently reproduced here. The directly reproduced source is arXiv:2410.20477v2; the journal PDF and other arXiv versions were not compared with it.

The general arguments explicitly labelled “not formalized” are not additional Lean theorems. The preregistration's separate floating-point readings for 162 discretized qutrit phase arrays and random projective observables were not reproduced and supply no universal qutrit conclusion here. A complete qutrit classification, a classification in other prime dimensions, weaker repair hypotheses, and whether a replacement argument proves the source's higher-dimensional robustness bounds remain open in this dossier. No robustness theorem or physical noise model is formalized by this module.
