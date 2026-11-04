---
slug: schnell-ketzmerick-eckardt-2018-bose-selection-cubic-refutation
bibkey: schnellketzmerickeckardt2018bose
doi: 10.1103/PhysRevE.97.032136
url: https://arxiv.org/abs/1802.04088v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.result
---

# The expected two-bath Bose-selection bound is refuted for cubic spectra

## Problem

A. Schnell, R. Ketzmerick and A. Eckardt, *On the number of Bose-selected modes in driven-dissipative ideal Bose gases*, Phys. Rev. E 97, 032136 (2018), DOI 10.1103/PhysRevE.97.032136, arXiv:1802.04088v2, section “Rates with product structure”, `main.tex` lines 1173–1178 (TeX macros expanded and mathematical delimiters normalized):

> We expect that there is a generalization of the above arguement also to non-ohmic systems described by arbitrary spectral densities. We have checked functions of the form (remember that $J$ must be odd) $J(\varepsilon)\propto\vert\varepsilon\vert^d\mathrm{sgn}(\varepsilon)$ with some power $d$ (not necessarily integer) and similarly observe $M_S\leq2M_B-1$.

Here $M_B$ is the number of baths and $M_S=|S|$ the number of selected modes. The two-bath matrix in `main.tex` lines 1062–1083 uses opposite bath spectra and projector couplings, with weights $f_i=|\langle i|f\rangle|^2$ and $g_i=|\langle i|g\rangle|^2$. The selection condition is Eq. `MS-problem`, lines 374–382. These definitions are also recorded in [the literature note](../Library/StatisticalMechanics/schnellketzmerickeckardt2018bose.md).

Issue [#25984](https://github.com/the-omega-institute/trureturing/issues/25984) fixes a generic reading for $M_B=2$. For $m\in\mathbb N$, take unrestricted real energies $\varepsilon$ and coordinatewise positive real vectors $F,G$, and put $f_i=F_i/\sum_jF_j$, $g_i=G_i/\sum_jG_j$. The module's `asym` is
$A_{ij}=J_d(\varepsilon_j-\varepsilon_i)(f_if_j-g_ig_j)$,
where `spow` defines $J_d(0)=0$ and $J_d(x)=x|x|^{d-1}$ for $x\ne0$.

`IsSelected A S w` means that, for every index $i$, membership in $S$ implies $w_i>0$ and $(Aw)_i=0$, while nonmembership implies $w_i=0$ and $(Aw)_i<0$. Write $V_{d,m}$ for `violating d m`: the parameter triples $(\varepsilon,F,G)$ with $F,G>0$ admitting such $S,w$ with $|S|\ge4$. The proposition `claim` says that for every real $d>0$ and every natural $m$, $\operatorname{int}(V_{d,m})=\varnothing$ in the full real parameter space $\mathbb R^{3m}$. This generic reading is weaker than an unconditional three-mode ceiling; it is refuted.

## Motivation

The source distinguishes a few macroscopically occupied modes from an extensive selected set. A bound depending only on the number of baths would constrain fragmented condensation independently of the number of single-particle modes. The non-Ohmic expectation would extend the source's Ohmic product-coupling argument beyond spectra linear in the energy difference.

## Gap

The v2 source contains the quoted expectation. Issue #25984 records a bounded check of six identifiable citing works: Petiziol–Eckardt (arXiv:2311.02170), Vorberg–Ketzmerick–Eckardt (arXiv:1803.08866), Geiger–Knebel–Frey (arXiv:1806.07339), Diermann–Holthaus (arXiv:1911.12563), Schnell et al. (arXiv:2204.07147), and Mori (arXiv:2203.16358). The issue attributes the readings to the search contributor and reports no settlement of the restricted two-bath non-Ohmic bound. It distinguishes examples with more reservoirs or general antisymmetric networks from this two-projector family, and records no prior repository issue or Problems dossier found by its searches.

`not-found-in-searched-scope`.

## Route

All helper names below belong to the canonical module and are private.

1. **Cubic skew symmetry and a kernel identity.** `spectral_three` proves $\operatorname{spow}(3,x)=x^3$ for every real $x$. For every natural $m$, all real $m$-component $\varepsilon,F,G$ and every pair of indices, `asym_skew` proves $A_{ji}=-A_{ij}$ at $d=3$, without positivity assumptions. For every real $5\times5$ matrix $a$ satisfying $a_{ji}=-a_{ij}$ for all indices, `pfaffian_kernel` proves $a\pi(a)=0$, where `pfaffianVector` is the vector of four-dimensional principal Pfaffians with alternating signs starting positive. No rank assumption is required.
2. **An open positivity region.** `couplingDomain` consists of five-component parameter triples with every coordinate of $F$ and $G$ strictly positive. For each pair of indices, `asym_continuousOn` proves continuity of the cubic matrix entry on this domain; the positive sums of the coupling coordinates supply the nonzero denominators. For each index, `pfaffian_continuousOn` proves continuity of the corresponding Pfaffian coordinate on the same domain. `couplingDomain_open` and `neighborhood_open` prove that the domain and the set $U$ of its points with every coordinate of $\pi(A)$ strictly positive are open in the ambient real product space.
3. **A point and selected occupations.** The parameter `base` has $\varepsilon=(1,2,3,4,5)$, $F=(5,4,4,4,4)$ and $G=(6,6,3,3,3)$. `base_mem` proves that this point belongs to $U$. For every point in $U$, `neighborhood_subset` uses the universal five-element selected set and $w=\pi(A)$ to prove membership in $V_{3,5}$; the condition on unselected indices is vacuous because every index is selected.
4. **Interior and contradiction.** `interior_nonempty` proves that $\operatorname{int}(V_{3,5})$ is nonempty. The proof of `result` applies `claim` at the positive real exponent $3$ and natural size $5$, contradicting that nonemptiness.

## Falsifier

The refutation would not answer the source's expectation if the matrix, selection signs or meaning of genericity differed. The formal matrix has the source's two normalized product couplings and opposite spectra. At $d=3$ its odd power is exactly cubic. Multiplying $A$ by the omitted positive factor $2\pi/\hbar$, or by a positive spectral proportionality constant, preserves every zero and strict sign in the selection condition.

The formal occupation vector is not normalized. For any witness with $|S|\ge4$, its sum is positive, so dividing by that sum preserves all selection conditions and gives unit total occupation. This normalization argument is not a separate Lean declaration. The parameter space imposes no energy-distinctness condition; the exhibited base energies are distinct. The proved neighbourhood is open in the full parameter space, rather than merely on a constrained slice of coupling vectors. Physical realization of the bath model is outside the formal statement.

## Evidence

The canonical source is `D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.lean`.

- **Proof.** It proves `result : ¬ claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/StatisticalMechanics/BoseSelectionCubicTwoBathRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:d793eee090f362910b905136055852650b93e6aab3439d299408e0b25a72dfb8`;
- `claim`: `sha256:d46c56af776573c200b3eee95cad934c6dc1b2783fa12a86ad491629fac1bdc3`.

## Triage

Tier 1 stated expectation of a 2018 paper, preregistered in issue #25984 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** it is false that, for every real $d>0$ and every natural $m$, the set of parameter triples with coordinatewise positive coupling vectors admitting the defined selection condition with at least four selected modes has empty interior.

**Computed, not formalized:** None.

**Argued, not formalized.**

- *Mechanism and missing structure.* For Ohmic spectra, the source's Eq. `vector-chain` expresses the selected equations in the four vectors $f$, $\varepsilon f$, $g$, $\varepsilon g$ restricted to $S$ (`main.tex` lines 1093–1142). For a nonempty selected set with positive coupling weights, the coefficient of $\varepsilon f$ is $-\sum_{j\in S}f_jw_j<0$; independence of the four restricted vectors would instead force every coefficient to vanish. The source explicitly invokes “generally the four vectors will be linearly independent” at line 1141. For cubic spectra, expanding $(\varepsilon_j-\varepsilon_i)^3$ introduces the additional vectors $\varepsilon^2f$, $\varepsilon^3f$, $\varepsilon^2g$ and $\varepsilon^3g$: summing each expanded term against $w_j$ gives its corresponding scalar moment. There are up to eight vectors, so the four-vector independence argument does not extend to five selected modes. Oddness and product coupling alone do not supply that missing reduction. For linear spectra the stated contradiction still applies whenever those four restricted vectors are linearly independent. A three-mode bound under other spectral restrictions is not established here.
- *Strict positivity and perturbations.* The formal route uses `base_mem`, `neighborhood_open` and `neighborhood_subset`: at $d=3$, $m=5$, every point in the open set $U$ with positive coupling and Pfaffian coordinates has the universal selected set and the stated kernel witness. Since the base belongs to $U$, a nonempty open set of parameters with strictly ordered energies can also be obtained by intersecting $U$ with $\varepsilon_1<\cdots<\varepsilon_5$. This intersection contains the base. That additional energy-order restriction is not formalized. The proof gives no numerical radius or sampling frequency.
- *Effect on the paper and surviving questions.* The conjectural non-Ohmic extension of the $2M_B-1$ ceiling cannot be used even as a generic two-bath bound. The source's Ohmic argument and Fig. 7 explicitly concern linear spectra (`main.tex` lines 1145–1171 and 1180–1201), and this cubic refutation does not contradict them. The conclusion's discussion of size-independent bounds and fragmented condensation cannot use the refuted ceiling as justification for arbitrary non-Ohmic spectra. A five-mode example does not determine whether a larger size-independent bound exists, whether selected sets can grow extensively, or what happens for more than two baths; these questions are not settled here. The settlement makes no claim about the source's continuum-rate or driven-rotor results.

## ASSUMED-UNVERIFIED

The bounded literature check is the one reported in #25984; the six citing-work readings, the reported OpenAlex and Crossref citation counts, and the preregistration's repository-search scope have not been independently reproduced. They do not establish exhaustive worldwide novelty or priority. The source's numerical non-Ohmic observations have not been reproduced. The preregistration's floating-point singular-value check and random-perturbation frequencies have not been reproduced and are not used as proof.

The rank calculation, the occupation-normalization and positive-prefactor arguments in Falsifier, and the arguments and consequences labelled “Argued, not formalized” are outside the compiled statement of `result`. The formalization establishes the specified rate-asymmetry selection problem, not existence of a microscopic thermal reservoir realization, a derivation of the kinetic model, uniqueness of the selected solution, or thermodynamic-limit condensation. Bounds for other spectra, other system sizes and additional baths are not classified by this settlement.
