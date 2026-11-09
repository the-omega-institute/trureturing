---
slug: ptkurt2204
bibkey: ptaszynski2022thermalheat
doi: 10.48550/arXiv.2204.08421
url: https://arxiv.org/abs/2204.08421v4
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.result
---

# Negative scaled heat-current kurtosis in a six-state thermal network

## Problem

K. Ptaszyński, *Bounds on skewness and kurtosis of steady state currents*, arXiv:2204.08421v4, Section III A, item 3, Eq. (19), states:

> In classical Markovian systems driven only by temperature differences kurtosis of the heat current is always nonnegative

The inequality is $\mathcal K^h\ge0$. Equations (4) and (10) define $\mathcal K=c_4/c_2$ and $c_m=\chi^{(m)}(0)$, using scaled current cumulants. This is not the standardized fourth central moment. The source and locators are in [the Library note](../Library/StatisticalMechanics/ptaszynski2022thermalheat.md).

[Issue #22747](https://github.com/the-omega-institute/trureturing/issues/22747) fixes the finite real-root formulation and the [corrected directed-rate conventions](https://github.com/the-omega-institute/trureturing/issues/22747#issuecomment-6446742619). The public `claim` quantifies over finite state and bath counts, energies, positive inverse temperatures, nonnegative off-diagonal bath rates, and the counted bath. It asserts existence of a branch and nonnegativity of $c_4/c_2$ for every such branch having $c_2>0$.

### Statement echo

| Source clause or explicit convention | Lean counterpart | Scope |
| --- | --- | --- |
| $k_{ij}=\sum_\alpha k_{ij}^\alpha$, Eq. (65) | `totalRate` | Finite bath sum. |
| “where $k_{ij}$ is the transition rate from the state $j$ to $i$.” | Directed rates $q_\alpha(i,j)=k_{ji}^\alpha$ | Row $i$, column $j$ uses $q_\alpha(j,i)$; the diagonal sums rates leaving column state $i$. |
| Bath-resolved ratio, Eq. (66) | `ThermalDetailedBalance` | Paired positive support; the ratio law applies on positive edges. |
| Counted-bath heat tilt, Eq. (67) | `tiltedRateMatrix` | Off-diagonal factor $\exp(-t(E_i-E_j))$ for the counted bath; unchanged escape diagonal. |
| Dominant eigenvalue and zero-field derivatives, Eqs. (68)–(70) | `IsSourceSCGF` | Zero value and $C^4$ regularity at zero; greatest real characteristic root at every real field. |
| Nonnegative thermal kurtosis, Eq. (19) | `claim` | All finite carriers; positive inverse temperatures and nonnegative off-diagonal rates; branch existence and the universal branch implication. |
| Exact refutation of that assertion | `result` | $\neg\mathrm{claim}$. |

The branch-existence conjunct and real-root formulation are explicit binding conventions. The proof uses the existence conjunct, zero value, regularity and characteristic equation; it does not use the greatest-root comparison. The proof reuses `MarkovMpembaTripletRefutation.generator` for the escape diagonal. The claim retains its literal outgoing-rate expression.

## Motivation

The source proposes thermal kurtosis as a diagnostic of forces other than temperature differences. Its Section III D reports a random-network screen with $N\le6$ states and $L\le4$ baths. An exact six-state two-bath counterexample tests the universal inequality within that finite thermal model.

## Gap

The literature screen recorded in #22747 covers the source, citing works arXiv:2208.11206, 2305.09759, 2404.00422 and 2411.19643, later-author works, arXiv keyword queries, OpenAlex, Semantic Scholar, Zenodo and MathOverflow. It reports no proof or refutation of this thermal fourth-current inequality in the searched scope. Rate limits affected citation queries. These are attributed literature readings, not a proof of exhaustive novelty; completeness is `ASSUMED-UNVERIFIED`.

The repository's unicyclic skewness and kurtosis bounds concern different rate-vector statements and do not settle this thermal inequality. The exact finite-root refutation is separate from standalone physical SCGF existence and Perron–Frobenius identification.

## Route

Use six states with alternating energies $(0,1,0,1,0,1)$ and two inverse temperatures $\log2$ and $\log8$. The hot bath connects consecutive low–high pairs with upward rates $(1,6,6)$ and downward rates $(2,12,12)$. The cold bath connects each high state to the next low state cyclically, with downward rate $8$ and reverse rate $1$. Count the cold-bath heat current.

The private declarations `beta8_pos`, `q8_nonneg` and `q8_thermal` certify the binding thermal hypotheses. The private determinant certificates `det_M8`, `matrix8_eq` and `det8` give

$$\det(zI-W(t))=P(z)-18432(e^{3t}-1)-288(e^{-3t}-1),$$

$$P(z)=63504z+50202z^2+13968z^3+1507z^4+66z^5+z^6.$$

`jetPow_eq` and `polynomial_jet` express iterated derivatives through a finite binomial recurrence. `polyJet_certificate` solves the triangular derivative equations, and `implicit_cumulants` gives, for every $C^4$ zero branch satisfying this characteristic equation,

$$c_2=\frac{3581}{2401},\qquad c_4=-\frac{113056891}{1129900996}.$$

`rational_sign_certificate` certifies

$$\frac{c_4}{c_2}=-\frac{113056891}{1685204276}<0.$$

`result` obtains a branch from the assumed `claim` and contradicts its nonnegativity conclusion with these certificates.

## Falsifier

The assertion is refuted under the corrected directed-rate, paired-support and finite real-root conventions of #22747. A claim about the physical long-time SCGF additionally needs an existence and identification bridge. The module supplies no standalone branch-existence theorem, irreducibility theorem, or Perron–Frobenius identification theorem. The source display's escape diagonal is interpreted according to its explicit $j\to i$ rate sentence and probability-conservation convention; the uncorrected displayed indexing is not the formal claim.

## Evidence

The Lean source is [PtaszynskiThermalHeatKurtosisRefutation.lean](../D5/S3/StatisticalMechanics/PtaszynskiThermalHeatKurtosisRefutation.lean), with generality `I` and admission basis `open-problem-resolution (#22747; Refuted)`. Its sole public theorem is `result`, proving the negation of `claim`. The associated Scribe displays the full negated proposition.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The exact experiment is [the published checker directory](https://github.com/the-omega-institute/trureturing-experiments/tree/04bc4585bad1ab10dc1c6b07b5a7dbd5fb14d5c3/docs/reports/ptaszynski-heat-current-kurtosis-sign), at immutable revision `04bc4585bad1ab10dc1c6b07b5a7dbd5fb14d5c3`, script `check.py`, SHA-256 `4aff2b5160036fc0d8a13624cea38ad5d6062074f8271daa0c4ba332219def02`. `git cat-file -e` confirms that object and path. Executing its exact bytes as `python3 .lake/scratch/ptkurt2204-stageb/check.py` exits 0 and returns `ALL_CHECKS_OK`. The program verifies the determinant identity and symbolic fourth-cumulant sign for $R\ge8$; it checks $c_2>0$ explicitly at $R=8$. Its transition construction has paired support and bath ratios $1/2$ and $1/R$, and its diagonal subtracts each rate from its source column. These give local detailed balance and column conservation. The positive formula below establishes $c_2>0$ on the half-line. It also checks one instance with six distinct energies. No experiment program or data is embedded here.

## Triage

Tier 1 published numerical conjecture; resolution `Refuted`. There is no digestion atom. Proof steps are classified `bind-only`; the external named-problem settlement supplies the admission basis. The numerical witness has utility `certified-instance` with `basis=refutes`.

### What the settlement shows

1. **Proved (kernel-checked):** the explicit $R=8$ six-state two-bath rates satisfy the corrected thermal hypotheses (`beta8_pos`, `q8_nonneg`, `q8_thermal`), and every supplied zero characteristic branch has $c_2=3581/2401$ and $c_4=-113056891/1129900996$ (`det8`, `implicit_cumulants`). `result` refutes the exact binding universal claim.
2. **Proved (kernel-checked):** `polynomial_jet`, `polyJet_certificate` and `rational_sign_certificate` certify the finite triangular derivative equations and negative ratio. **Explanation:** in the fourth derivative equation, the terms $50202(8c_1c_3+6c_2^2)+36\cdot13968c_1^2c_2+24\cdot1507c_1^4$ are subtracted from $81(18432+288)$ before division by $63504$. For the certified branch this yields the negative fourth derivative. This identity explains the nonlinear mechanism; the module does not claim a separate public identity theorem.
3. **Computed:** the immutable exact checker above verifies the determinant formula and $c_4<0$ for the full symbolic family $R\ge8$. **Paper argument:** the paired transition construction, with bath ratios $1/2$ and $1/R$ and rate-subtracting escape diagonal, satisfies paired support, local detailed balance and column conservation; the displayed exact second-cumulant formula supplies $c_2>0$ on this half-line. Its shifted fourth-cumulant numerator is minus a polynomial with fourteen positive coefficients. The half-line theorem is not formalized; the Lean instance has $R=8$.
4. **Open:** standalone SCGF existence and Perron–Frobenius identification, the minimum state count, and additional hypotheses restoring nonnegative kurtosis.

The nearest certified surviving statement is conditional: every $C^4$ zero characteristic branch for this explicit generator has the displayed second and fourth derivatives. For the symbolic family, the triangular equations give $c_2=27(4424+6932R+3954R^2+1425R^3+160R^4+19R^5)/(2(4R+31)^3(R^2+2R+4))$. Every numerator coefficient and denominator factor is positive for $R\ge8$, proving the second-cumulant sign in prose. The checker certifies the shifted fourth-cumulant polynomial algebraically. This half-line argument is not a Lean theorem. No classification of all thermal networks or positive-kurtosis subclass is asserted.

The universal inequality cannot supply a valid premise in the finite-root model. The source's diagnostic inference that negative heat-current kurtosis entails nonthermal forces therefore needs additional hypotheses in that model. Transferring this consequence to physical long-time cumulants requires the open SCGF-identification bridge. Independently established source results outside this inequality are not adjudicated by this settlement.

## ASSUMED-UNVERIFIED

Literature completeness and absence of an external published settlement are `ASSUMED-UNVERIFIED`. The bounded screen in #22747 is attributed to its producers. Physical SCGF existence and identification, the minimal state count and restoring hypotheses remain open. The numerical family beyond $R=8$ is checked by exact symbolic computation and has no claimed Lean proof.
