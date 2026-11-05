---
slug: tavakoli-zambrini-cruzeiro-uola-abbott-2021-pure-state-htmb
bibkey: tavakolizambrinicruzeirouolaabbott2021contextual
doi: 10.1103/PRXQuantum.2.020334
url: https://arxiv.org/abs/2010.04751v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Contextuality/PureStateHTMBBound.result
---

# Pure preparations cannot violate the HTMB inequality in finite dimension

## Problem

A. Tavakoli, E. Zambrini Cruzeiro, R. Uola and A. A. Abbott, *Bounding and simulating contextual correlations in quantum theory*, PRX Quantum 2, 020334 (2021), arXiv:2010.04751v3, subsection “Mixed states as resources for quantum contextuality”, state:

> This gives us strong evidence (i.e., up to numerical precision) that pure states cannot violate the HTMB inequality~\eqref{eq:HTMB}, and we conjecture this to indeed be the case exactly.

The quotation is from line 506 of the e-print member `Manuscript_infocontext_reresubmission.tex`, md5 `f767464510150f9e02bc504393cf40e8`. The scenario and Eq. (33) are at lines 492–500; the numerical pure-state bound is at lines 502–507. See also [the literature note](../Library/Observer/tavakolizambrinicruzeirouolaabbott2021contextual.md).

Alice receives two trits $x=(x_1,x_2)\in\mathbb Z_3^2$, and Bob guesses either coordinate using one of two three-outcome measurements. Write $P_x=\operatorname{projector}(\psi_x)=|\psi_x\rangle\langle\psi_x|$. Issue [#25326](https://github.com/the-omega-institute/trureturing/issues/25326) fixes the finite-dimensional reading: for every $d\in\mathbb N$, every family of unit vectors $\psi_x\in\mathbb C^d$ and every pair of POVMs $(M_b)_{b\in\mathbb Z_3}$ and $(N_b)_{b\in\mathbb Z_3}$, assume

$$
\sum_{x:\,x_1+a x_2=k}P_x=\sum_{x:\,x_1+a x_2=0}P_x
\qquad(a\in\{1,2\},\ k\in\mathbb Z_3).
$$

Each POVM has positive semidefinite effects summing to the identity. Then the module's `htmbValue` satisfies

$$
\operatorname{htmbValue}(\psi,M,N)
=\frac1{18}\sum_{x\in\mathbb Z_3^2}
\left(\operatorname{Re}\operatorname{tr}(P_xM_{x_1})+
\operatorname{Re}\operatorname{tr}(P_xN_{x_2})\right)
\le\frac23.
$$

This is `claim`, and `result : claim` proves it.

## Motivation

The authors identify a possible distinction between preparation contextuality and settings where pure states suffice: purifying states or selecting pure components can destroy preparation operational equivalences. An exact pure-state HTMB bound determines whether a violation of this particular inequality can have a pure-preparation realization, even when finite dimension and the two POVMs are unrestricted.

## Gap

Issue #25326 records the bounded literature check by the orchestrator (Claude Code, Opus):

- The arXiv v3 TeX contains the conjecture; the journal text was not read.
- Semantic Scholar listed 21 citing records and OpenAlex reported 18; searches of six citing preprints listed in the issue found no settlement of the HTMB pure-state conjecture.
- A web search for the conjecture's wording returned only the source, a Zenodo search for “HTMB” returned no records, and repository searches found no prior matching record.

These reported searches were not independently reproduced here. Their conclusion is `not-found-in-searched-scope`, not exhaustive novelty or priority.

## Route

Fix $d\in\mathbb N$ and write $P_{ij}=\operatorname{projector}(\psi_{(i,j)})$ for $i,j\in\mathbb Z_3$.

1. **Additive grid.** `additive_form` applies to any family of complex $d\times d$ matrices satisfying both displayed parity-sum equivalences, for every $k\in\mathbb Z_3$, and gives $P_{ij}=P_{i0}+P_{0j}-P_{00}$ for every $i,j$. Positivity and purity are not hypotheses of this lemma.
2. **Score reduction.** `value_reduction` assumes all nine vectors have norm one, both measurement families sum to the identity, and the additive identity holds for every $i,j$. It gives $\operatorname{htmbValue}=(D_{\rm col}+D_{\rm row})/6$, where $D_{\rm col}=\sum_i\operatorname{Re}\operatorname{tr}(P_{i0}M_i)$ and $D_{\rm row}=\sum_j\operatorname{Re}\operatorname{tr}(P_{0j}N_j)$. Positivity is not needed for this reduction.
3. **Constant axes.** `discrimination_three` bounds the discrimination sum of any three unit vectors by $3$ when the three effects are positive semidefinite and sum to the identity. `constant_discrimination` makes that sum exactly $1$ if all three projectors equal the zeroth projector, the zeroth vector has norm one, and the effects sum to the identity. Thus, under the hypotheses of `claim`, a constant projector axis gives $D_{\rm col}+D_{\rm row}\le4$.
4. **Nonconstant axes.** `projector_difference_span` assumes four unit vectors $a,b,c,e\in\mathbb C^d$ with $P(a)-P(b)=P(c)-P(e)$ and $P(c)-P(e)\ne0$; it puts $a$ and $b$ in $\operatorname{span}_{\mathbb C}\{c,e\}$. `cross_in_plane` assumes all nine vectors are unit, the additive identity holds everywhere, and there exist $i,j$ with $P_{i0}\ne P_{00}$ and $P_{0j}\ne P_{00}$. It produces a complex subspace $s$ with $\dim s\le2$ containing every $\psi_{(k,0)}$ and every $\psi_{(0,k)}$.
5. **Dimension bound.** `discrimination_bound` assumes three unit vectors lying in a common complex subspace $s$ of dimension at most two and three positive semidefinite effects summing to the identity. Their discrimination sum is at most $2$. Applying it to each axis in the nonconstant case gives $D_{\rm col},D_{\rm row}\le2$. The score reduction gives $\operatorname{htmbValue}\le2/3$ in every case.

## Falsifier

A proof for only one parity equivalence, only projective measurements, or a restricted finite dimension would not establish `claim`. The module requires both coefficients $a=1,2$, allows arbitrary three-outcome POVMs, and quantifies over every natural $d$.

Each parity fibre has exactly three labels: for every $x_2$ there is exactly one $x_1=k-a x_2$. Multiplying the displayed sums by $1/3$ therefore gives precisely equality of the uniform mixtures. This matches the source's quantum-model definition, where preparation equivalences are matrix equalities, and its HTMB scenario. The imported `projector` has entries $v_u\overline{v_v}$, and the score uses the Born-rule trace with normalization $1/18$.

No infinite-dimensional statement or mixed-preparation bound is encoded. At $d=0$ no unit preparation family exists; the theorem imposes no lower bound on dimension and remains conditional on its normalization hypotheses.

## Evidence

The canonical source is `D5/S3/Quantum/Contextuality/PureStateHTMBBound.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** `#print axioms` reports only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Contextuality/PureStateHTMBBound.lean.json`.

Declaration statements:

- `result`: `sha256:19377919cf876acdbaf728936b69f70710d20fad9c978b3fb44d938f9f00bb0d`;
- `claim`: `sha256:ab44674760c377e6c7e8226d49b6c04a7a6b577747ad46912984590cad9baaae`.

## Triage

Tier 1 conjecture stated in a 2020 arXiv preprint published in PRX Quantum (2021), preregistered in issue #25326 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; the per-declaration proof shapes are listed in the delivery PR. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural dimension $d$, every nine unit vectors in $\mathbb C^d$, and every two positive semidefinite three-outcome measurements each summing to the identity, both parity-sum equivalences for every $k\in\mathbb Z_3$ imply $\operatorname{htmbValue}\le2/3$.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Decisive mechanism.* For the pure grid under both equivalences, `additive_form` gives the additive identity. With all nine vectors unit and a nonconstant projector on each axis, `cross_in_plane` confines both axes to a common subspace of dimension at most two; `discrimination_bound` then bounds each axis sum by two for positive semidefinite effects summing to the identity. If either projector axis is constant, unit normalization and measurement completeness give one for that axis by `constant_discrimination`, while the other axis has three unit vectors and a POVM and is bounded by three by `discrimination_three`. These alternatives explain why increasing finite ambient dimension cannot improve the bound.
- *Sharpness.* Let $e_0,e_1,e_2$ be the standard basis of $\mathbb C^3$, set $\psi_{(i,j)}=e_j$, $M_i=I_3/3$ and $N_j=|e_j\rangle\langle e_j|$. All vectors are unit and both effect families are positive semidefinite and complete. Each parity fibre contains each $j$ once, so its projector sum is $I_3$. Every first-coordinate term is $1/3$ and every second-coordinate term is $1$, giving $9(1/3+1)/18=2/3$. Thus the uniform finite-dimensional bound is sharp; attainment is not asserted by `result`.
- *Effect on the paper.* The source states at line 510, “This shows that sufficiently strong contextual quantum correlations can require the use of mixed states.” The exact finite-dimensional pure-state exclusion supplies the pure-state premise of that conclusion for HTMB. Combining it with a verified finite-dimensional mixed-state violation would exclude every pure-preparation realization of the violating correlations under both equivalences. The source reports such a six-dimensional violation, $\mathcal A_{\rm HTMB}\approx0.698$, at line 508; its construction is not certified here. The tight mixed-state maximum, explicitly left open at line 509, remains unresolved by this theorem.
- *Neighbouring questions.* Infinite-dimensional realizations, quantitative bounds for approximate parity equivalences, and the mixed-state optimum remain open in this dossier. The source's SDP hierarchy, other inequalities and simulation-cost questions are not settled by `result`.

## ASSUMED-UNVERIFIED

The literature check is bounded to the searches reported in #25326 and does not establish exhaustive worldwide novelty or priority. The citation listings, six citing-preprint readings, web and Zenodo searches, and repository search reported by the orchestrator were not independently reproduced. The journal text was not read, so whether it retains the conjecture unchanged is unverified; the quotation and formal comparison use arXiv:2010.04751v3.

The sharpness computation and all statements under “Argued, not formalized” are not additional Lean conclusions. The source-to-Lean comparison and the fibre-count explanation are mathematical arguments rather than separate compiled declarations. The source's SDP numerical bounds and its cited mixed-state violation were read as source statements, not reproduced or formally certified. Infinite dimension, approximate equivalences, attainment in each fixed dimension and the exact mixed-state maximum are not established by `result`.
