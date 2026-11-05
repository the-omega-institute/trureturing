---
slug: arias-di-giulio-keski-vakkuri-tonni-2023-charge-sector-majorization
bibkey: ariasdigiuliokeskivakkuritonni2023capacity
doi: 10.1007/JHEP03(2023)175
url: https://arxiv.org/abs/2301.02117v1
triage: theorem
motivation_gids:
  - D5/S3/Entropy/ChargeSectorMajorizationRefutation.result
---

# Majorization need not survive normalization in a common charge sector

## Problem

R. Arias, G. Di Giulio, E. Keski-Vakkuri and E. Tonni, *Probing RG flows, symmetry resolution and quench dynamics through the capacity of entanglement*, arXiv:2301.02117v1, JHEP 03 (2023) 175, Section 7, “Symmetry-resolved related issues”, ask (`CDraft-Final.tex`, line 4140):

> For instance, given two density matrices such that $\rho\succ \sigma$, we may ask whether this majorization order survives  once we decompose $\rho$ and $\sigma$ according to (\ref{eq:decompositionrho}). One can try to diagnose this aspect using $M_A^{(n)}(q)$ in (\ref{SR-M_n}), given that these quantities are entanglement monotones also in a fixed charge sector. We leave this analysis for future investigations.

The referenced equation is the normalized charge-block decomposition of Section 6, equation (6.1), TeX lines 3550–3569: $\rho_A=\bigoplus_q p(q)\rho_A(q)$, with $p(q)=\operatorname{Tr}(\Pi_q\rho_A)$ and $\operatorname{Tr}\rho_A(q)=1$. Section 6 obtains this decomposition for a reduced state commuting with its subsystem charge; the registered comparison uses one common subsystem charge operator. See [the literature note](../Library/Entropy/ariasdigiuliokeskivakkuritonni2023capacity.md).

Issue [#22533](https://github.com/the-omega-institute/trureturing/issues/22533) fixes the sectorwise reading: does $\rho\succ\sigma$ imply $\rho(q)\succ\sigma(q)$ for every charge whose weight is positive in both states? This implication is refuted already for finite diagonal states.

The formal `claim` quantifies over every $n\in\mathbb N$, charge map $c:\mathrm{Fin}\,n\to\mathbb Z$ and real vectors $r,s:\mathrm{Fin}\,n\to\mathbb R$ with nonnegative entries and $\sum_i r_i=\sum_i s_i=1$. Put $p_r(q)=\sum_{i:c(i)=q}r_i$, the module's reused `pushforward`, and let $\operatorname{sec}_q(r)$ be the descending list of $r_i/p_r(q)$ for all indices with $c(i)=q$, the module's `sectorSpectrum`. Zero eigenvalues retain their multiplicities. The claim says that $\operatorname{desc}(r)\succ\operatorname{desc}(s)$ implies $\operatorname{sec}_q(r)\succ\operatorname{sec}_q(s)$ for every integer $q$ with $p_r(q)>0$ and $p_s(q)>0$.

For equal-length descending lists $x,y$, the reused `Majorizes` requires every prefix sum of $x$ to be at least the corresponding prefix sum of $y$ for $1\le k\le |x|$, and equal total sums. This is the direction used in the source's definition of majorization (TeX line 830).

## Motivation

The question connects a comparison of whole entanglement spectra to comparisons conditioned on a measured charge. An affirmative answer would let global majorization supply the ordering needed to compare Schur-concave quantities inside each normalized block. A negative answer identifies information about charge labels that a global spectral comparison does not control.

## Gap

Issue #22533 records a bounded literature check: the search reported no settlement among the 19 citing works listed by INSPIRE, two targeted arXiv searches, MathDB and formal-conjectures. It also records no pre-existing repository reference to the paper. The arXiv version listing and retention of the question in the journal version are reported there. These search findings are preregistration-reported; the direct source reading here covers arXiv v1.

`not-found-in-searched-scope`.

## Route

All the following private lemmas concern the fixed four-level data $c=(0,0,1,1)$, $r=(6,6,7,1)/20$ and $s=(7,5,4,4)/20$; none asserts a conclusion for arbitrary vectors or charges.

1. **State hypotheses.** `r_state` and `s_state` establish nonnegativity of every entry and total mass one for these respective vectors.
2. **Global order.** `full_spectra` identifies their descending lists as $(7,6,6,1)/20$ and $(7,5,4,4)/20$. `global_majorizes` proves majorization in the proposed direction for these lists; their prefix sums are $(7,13,19,20)/20$ and $(7,12,16,20)/20$.
3. **Positive normalized sector.** At charge zero, `sector_weights` proves $p_r(0)=p_s(0)=3/5$, so both positivity hypotheses hold. For these same vectors, charge map and charge zero, `sector_spectra` identifies the normalized descending lists as $(1/2,1/2)$ and $(7/12,5/12)$.
4. **Contradiction.** `sector_failure` refutes majorization between these charge-zero lists: its first prefix inequality would require $1/2\ge7/12$. `result` instantiates `claim` with the four-level data and charge zero, supplying both state hypotheses, `global_majorizes` and the two strictly positive sector weights, to obtain this contradiction.

## Falsifier

The refutation answers the source question under the registered sectorwise reading. Faithfulness requires the same charge operator for both states, normalization by each state's own positive sector weight, and the source's direction of majorization. The formal definitions use a shared charge map, divide by the corresponding `pushforward`, retain all indices in the charge eigenspace, and sort in descending order. Thus the compared sector lists have the same length even when some eigenvalues vanish; zero-weight sectors are outside the claimed implication.

For the matrix interpretation take $Q_A=\operatorname{diag}(0,0,1,1)$, $\rho=\operatorname{diag}(r)$ and $\sigma=\operatorname{diag}(s)$. These diagonal states commute with the same $Q_A$ and their spectra and normalized blocks are precisely the lists above. Their realization as reductions of total-charge eigenstates is argued below; this matrix and purification bridge is not formalized in the module.

## Evidence

The canonical source is `D5/S3/Entropy/ChargeSectorMajorizationRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Reuse.** It uses `Majorizes` from `LinDTIMajorizationRefutation`, `desc` from `PositiveSimplexGeometryAndMixing`, and `pushforward` from `CapacityMonotone`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Entropy/ChargeSectorMajorizationRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:14131ed0450d463729355d24c3942ae06046c4dba86450ac729b918f900348a2`;
- `claim`: `sha256:426437ee97955ca012af67eba04352ffb19a55a650d6e6ee51b46b97783fe930`.

## Triage

Tier 1 question of a 2023 JHEP paper, preregistered in issue #22533 before any Lean.
`theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| `result` | bind-only | none: the fixed spectra, sector weights and failed prefix inequality reduce to rational arithmetic and the imported definitions | open-problem-resolution |
| `sectorSpectrum`, `claim` | bind-only | none | definitions used by `result` |
| the fixed-data definitions and private witness lemmas | bind-only (consumed on the proof path of `result`) | none | consumed helpers |

Every declaration is bind-only. The bind-only form is admitted under the open-problem-resolution basis of CLAUDE.md §3.2; no escape witness is claimed. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every natural $n$, integer charge map $c$ on $\mathrm{Fin}\,n$, and pair of nonnegative real unit-mass vectors $r,s$, majorization of their descending full spectra implies majorization of their normalized sector spectra for every integer charge with positive weight in both vectors.

**Computed, not formalized** (exact rational arithmetic): for the four-level witness, the charge-one blocks have equal positive weight and the normalized charge-one spectrum of $r$ majorizes that of $s$.

**Argued, not formalized.**

- *Failure mechanism.* Global sorting discards charge labels. In the fixed witness of `full_spectra`, the largest weight of $r$ lies at charge one, while the largest weight of $s$ lies at charge zero. The charge-zero blocks in `sector_spectra`, with the common positive weight established by `sector_weights`, instead compare a uniform pair to a nonuniform pair in the direction ruled out by `sector_failure`. The computed equality of the charge-one weights, together with `sector_weights` at charge zero, shows that requiring equal probabilities for every charge does not repair this witness. A global spectral order does not specify how spectral weight is assigned to the charge eigenspaces.
- *Physical realization.* For either fixed probability vector $t=r$ or $t=s$, set $|\Psi_t\rangle=\sum_{i=0}^3\sqrt{t_i}|i\rangle_A|i\rangle_B$ and $Q_B=\operatorname{diag}(1,1,0,0)$. The norm squared is $\sum_i t_i=1$. Every occupied basis pair has $Q_A$ charge plus $Q_B$ charge equal to one, so $|\Psi_t\rangle$ is a charge-one eigenstate of $Q_A\otimes I+I\otimes Q_B$. Taking the partial trace over $B$ removes terms with unequal basis indices and gives $\operatorname{diag}(t)$, realizing both counterexample states in the source's pure-state setting.
- *Sufficient extra structure.* Suppose $r,s$ are nonnegative unit-mass vectors on the same finite charge-labelled basis and $s=Dr$, where $D$ is nonnegative, every row and column sums to one, and $D_{ij}=0$ whenever $c(i)\ne c(j)$. Each charge block of $D$ is then doubly stochastic and preserves that sector's total mass. For a sector with positive mass, division by this common mass gives $y=D_qx$ for the two normalized block vectors. For any set $K$ of $k$ output indices, $\sum_{i\in K}y_i=\sum_j a_jx_j$ with $a_j=\sum_{i\in K}(D_q)_{ij}$, $0\le a_j\le1$ and $\sum_j a_j=k$. Sort $x$ decreasingly. Subtracting $x_k$ from each entry gives $\sum_j a_jx_j\le kx_k+\sum_{j=1}^k(x_j-x_k)=\sum_{j=1}^kx_j$ for $1\le k\le\dim q$. Choose $K$ to contain the $k$ largest entries of $y$; column sums give equality of totals. Hence sectorwise majorization follows under this additional mixing constraint. This supplies a sufficient condition, not a characterization of all pairs with sectorwise order.
- *Surviving special cases.* If every basis index has the same charge, the unique positive sector has mass one and its spectrum is the full spectrum, so the implication reduces to its premise. If a charge eigenspace has one basis index and both weights there are positive, both normalized block spectra are $[1]$, so majorization in that sector is automatic. Neither observation supplies a general classification for degenerate charge eigenspaces.
- *Effect on the source.* Section 7 poses preservation as a question. The trace decomposition in Section 6 is obtained by substituting the direct-sum decomposition into a trace; this does not require a majorization comparison between two states. The refutation therefore removes no premise of that calculation. It excludes inferring every sector's Schur-concave comparison from global majorization alone; when sectorwise majorization is supplied independently, such comparisons remain its defining consequence. The separate questions about RG-flow ordering, quench ordering and the general moment-decomposition formula are not settled by `result`.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The 19-work INSPIRE search, two targeted arXiv searches, MathDB and formal-conjectures checks, arXiv version-list reading, journal-version reading and pre-existing repository search are reported in #22533 and have not been independently reproduced. The direct paper reading is arXiv:2301.02117v1, `CDraft-Final.tex`, MD5 `5739b2bdf5eab61756172c2a3f55d9e0`.

The statements in “Computed, not formalized” and “Argued, not formalized”, including the matrix and pure-state interpretation, the sufficient mixing condition, the special cases and the assessment of effects on the source, are not formalized by `result`. A necessary and sufficient structural condition for inferring sectorwise preservation from global order is not supplied here. No conclusion is drawn about preservation restricted to a particular field theory, RG flow or quench family, or about the source's other open questions.
