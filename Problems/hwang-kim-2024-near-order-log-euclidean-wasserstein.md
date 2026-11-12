---
slug: hwang-kim-2024-near-order-log-euclidean-wasserstein
bibkey: hwangkim2024nearorder
doi: 10.1007/s11117-024-01099-4
url: https://arxiv.org/abs/2407.07438v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.result
---

# Hwang–Kim: log-Euclidean to Wasserstein near order

## Problem

Jinmi Hwang and Sejong Kim, *Near-order relation of power means*,
arXiv:2407.07438v1, page 17, final unnumbered question of §6:

> It would be an interesting problem to study whether the weak log-majorization relation generalizes to the near-order or entrywise eigenvalue relation. Note that (6.21) is a generalization of (4.14). From this point of view, we give an open question:

$$
\mathrm{LE}(\omega;\mathbb A)\preceq\Omega(\omega;\mathbb A).
$$

The question quantifies over every dimension $m\geq1$, every input count
$n\geq2$, positive definite complex matrices $A_j$, and weights $w_j>0$
with $\sum_jw_j=1$. Equation (6.21) is a different, proved comparison;
the question itself has no equation number.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Positive definite matrices in $\mathbb P_m$ | `claim`, `Matrix (Fin m) (Fin m) ℂ`, `Matrix.PosDef` | All complex inputs; real witnesses are a specialization. |
| Positive probability weights | `claim`, positivity of every weight and its finite sum equal to one | No weight is omitted. |
| $A\preceq B\iff I\leq A^{-1}\#B$ | `NearOrder`, existing `PsiMeanTraceConcavity.geometricMean` at weight $1/2$ | Source equation (3.5), with the same operand order. |
| $\mathrm{LE}=\exp(\sum_jw_j\log A_j)$ | `logEuclidean` | Literal functional-calculus expression, source equation (4.10). |
| Bures–Wasserstein distance | `buresWassersteinDistance` | Literal square-root trace expression from §2; real parts read the real traces. |
| $\Omega=\arg\min_{X>0}\sum_jw_jd_W(X,A_j)^2$ | `wassersteinBarycenter` | `Classical.epsilon` selects the actual positive definite minimizer predicate, including comparison with every positive definite matrix. |
| Universal final comparison | `claim` | Every dimension, input count, input and positive probability vector is retained. |
| Failure of the universal comparison | `result` | Exactly the negation of `claim`. |

The multivariable argmin definition is Bhatia–Jain–Lim,
arXiv:1803.03357, page 1, equation (2); see the
[source note](../Library/Eigenstructure/hwangkim2024nearorder.md) and
[barycenter note](../Library/Eigenstructure/bhatiajainlim2018wasserstein.md).
The existing geometric-mean owner is reused directly. The multivariable
means retain the source expressions. Definitions outside admissible
positive definite inputs have no bearing on the quantified claim.

## Motivation

The source asks whether its weak log-majorization comparison strengthens
to near order. [Preregistration #21282](https://github.com/the-omega-institute/trureturing/issues/21282)
identifies that exact question and its literal conventions. The settlement is
**Refuted**, by `D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation.result`.

## Gap

Weak log-majorization does not supply positivity of
$L^{-1}\#W-I$. Noncommuting eigenspaces allow the necessary determinant
condition for that positivity to fail even with two strictly positive inputs.

## Route

Use equal weights and

$$
A=\begin{pmatrix}4&0\\0&1\end{pmatrix},\qquad
B=\frac1{64}\begin{pmatrix}19&-3\sqrt{15}\\-3\sqrt{15}&61\end{pmatrix},\qquad
K=\frac1{8\sqrt{265}}\begin{pmatrix}35&-3\sqrt{15}\\-3\sqrt{15}&125\end{pmatrix}.
$$

The private theorems `witnessA_pos`, `witnessB_pos`, `witnessK_pos` and
`witnessK_riccati` verify strict positivity and $KAK=B$.
`wasserstein_witness` identifies the actual least-squares selector with
$W=(I+K)A(I+K)/4$; its proof uses the trace-norm variational inequality
and its equality condition to establish the minimizing matrix uniquely.
`logEuclidean_witness` identifies the actual logarithmic expression with
the explicit spectral matrix $L$.

Write $d=5/8+10/\sqrt{265}$. The private theorems `witnessL_det`,
`witnessW_det`, and `nearOrder_riccati` give $\det L=1$,
$\det W=d^2$, and a positive definite $C=L^{-1}\#W$ satisfying $CLC=W$.
The determinant equation and positivity give $\det C=d$.
If $I\leq C$, then $\det(C-I)=1+d-\operatorname{tr}C\geq0$.
Cayley–Hamilton trace identities yield

$$
\operatorname{tr}W+d\operatorname{tr}L
=\operatorname{tr}(LC)\operatorname{tr}C,\qquad
\operatorname{tr}(LW)+2d=\operatorname{tr}(LC)^2.
$$

Thus near order forces

$$
T=(\operatorname{tr}W+d\operatorname{tr}L)^2
-(1+d)^2(\operatorname{tr}(LW)+2d)\leq0.
$$

`witness_trace_test` proves $T>3/2500$ by rational intervals for
$\sqrt{\sqrt2}$ and $\sqrt{265}$, and `trace_obstruction` gives the contradiction.
These names refer to private declarations in the settling module.

## Falsifier

The universal `claim` implies near order for the displayed pair and equal
weights. The kernel-checked `result` derives a contradiction at exactly
those inputs. An incorrect argmin identification or an incorrect positive
trace certificate would invalidate that route; both are proved inside the
module rather than assumed as hypotheses of the public claim.

## Evidence

The formal source is
[`HwangKimNearOrderRefutation.lean`](../D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation.lean).
Its only public theorem is `result`; the axiom closure of every public
declaration is contained in `{propext, Classical.choice, Quot.sound}`.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Exact external checker

[Experiment directory at commit `0633f84b7cbcfd429c7fb70d140978a010582b1c`](https://github.com/the-omega-institute/trureturing-experiments/tree/0633f84b7cbcfd429c7fb70d140978a010582b1c/docs/reports/hwang-kim-2024-near-order-log-euclidean-wasserstein).
The checked file is `check.py`, SHA-256
`2d4d6daa173673ea7668a6fdec975ac704d56b763e14c456fdcd927c7f714eee`.
Command: `python3 /tmp/op-hk2407/continuation/check.py`,
using the exact bytes obtained from that commit; Python 3.14.8,
SymPy 1.14.0; exit 0, `ALL_CHECKS_OK`.
The checker verifies the explicit real symmetric matrices, strict positivity,
noncommutation, Riccati and logarithmic identities, rational root brackets,
and $3/2500<T<121/100000$. It also verifies symbolic second-order
rotation-family identities, including the whole second-order Riccati
equation. These symbolic identities and finite integer cross-checks do not
constitute a Lean proof of a uniform analytic family.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Exact scope |
| --- | --- | --- |
| Near order fails for two strictly positive $2\times2$ matrices at equal weights. | **Proved, kernel-checked:** `result`, with `witnessA_pos`, `witnessB_pos`, `logEuclidean_witness` and `wasserstein_witness`. | Literal source conventions in `claim`; this is a refutation of the universal assertion. |
| The explicit inputs are real symmetric and noncommuting. | **Computed:** the exact external checker in Evidence, exit 0 and the recorded SHA-256. | The displayed pair only; noncommutation is not a separately delivered Lean theorem. |
| Near order forces $\operatorname{tr}C\leq1+\det C$, contradicted by the positive $T$ certificate. | **Proved, kernel-checked:** `trace_obstruction` and `witness_trace_test`, used by `result`. | Positive $2\times2$ matrices with the stated determinant and Riccati hypotheses; Cayley–Hamilton trace identities and PSD determinant nonnegativity. |
| $3/2500<T<121/100000$ and the rotation-family jet identities. | **Computed:** the exact external checker in Evidence, exit 0 and the recorded SHA-256. | The two-sided bound is for this explicit witness. The family calculation verifies symbolic second-order identities and the stated finite coefficient cross-checks, not a universal analytic Lean theorem. |
| Lean formalization of the all-$r$ small-rotation family, common scaling, unitary and direct-sum extensions, and the commuting-case reduction. | **Open:** no such theorem is delivered. | These are follow-up formalization targets, independent of the already refuted universal claim. |
| The separate entrywise-eigenvalue question. | **Refuted by the revision2 companion:** `HwangKimWeightedSpectralRefutation.result`; the original `result` alone states no entrywise comparison. | The specified strictly positive weighted witness has an exact strict minimum-eigenvalue separator. Weak log-majorization survives. |

The obstruction concerns positivity of a relative geometric mean minus the
identity; the eigenvalue-product comparison does not impose that positivity.
At a commuting boundary, one eigenvalue of this difference is zero, and
rotation can destroy its semidefiniteness. The symbolic family calculation
explains this mechanism without enlarging the kernel-checked scope.

For the scalar commuting reduction, the surviving comparison follows in
prose from weighted AM–GM on the square roots:
$\prod_j a_j^{w_j}\leq(\sum_jw_j\sqrt{a_j})^2$.
Simultaneous diagonalization applies this coordinatewise. This explanation
is not an additional Lean theorem; the formalization remains open as listed.
The refutation invalidates the proposed strengthening, not any proved theorem
in the source; no source theorem is asserted here to depend on the open question.

### Revision2 companion scope

The complete Ma–Zhang revision2 note and approved eight-group scope are
retained at [#29594](https://github.com/the-omega-institute/trureturing/issues/29594).
The canonical exposition in the original Blueprint Scribe preserves both
witnesses, the exact trace criterion, commuting equality, all-dimension and
all-input-count quantifiers, reverse consequences and scientific boundaries.
Haobo Ma is affiliated with ChronoAI Pte Ltd, Singapore only; Wenlin Zhang
with NUS and ChronoAI Pte Ltd, Singapore. The source is CC BY 4.0.
These are returns of existing written research, without a new discovery or
publication claim.

| Group | Formal return and remaining boundary |
| --- | --- |
| 1 | `HwangKimStrictSpectralConverseRefutation.result` reuses the original actual witness and proves strict comparison of both decreasingly ordered eigenvalues, refuting the strict-spectral converse. The original `result` remains reusable. |
| 2 | `BuresWassersteinTransport.finite_barycenter_of_dual` proves the global minimum over every positive definite competitor, uniqueness and actual epsilon selection from strictly positive normalized finite transport data. The characterization is attributed to Bhatia–Jain–Lim, arXiv:1712.01504v1, Theorem 8 and (62)–(63). |
| 3 | `HwangKimTwoDimensionalCriterion.near_order_iff` proves both directions with positive definite L,W, det L=1, d=√det W, and exactly d≥1 and E≤0. |
| 4 | `HwangKimWeightedSpectralRefutation.result` uses exactly weights (3/4,1/4), A*=diag(256,1), B*=[[13,3√3],[3√3,7]]/4. The actual mean identities and λmin(W*)<107/100<λmin(L*) are proved on its live path. The theorem refutes the full universal entrywise claim. A separate kernel-checked exact application proves near-order failure for this same actual pair, using C²≥I and det(W−(107/100)I)<0; no bind-only theorem is retained. |
| 5 | **Open formal obligation:** arbitrary finite commuting positive definite inputs, actual common-basis log-Euclidean and argmin formulas, Loewner/near comparison and equality iff all inputs coincide, retaining every strictly positive weight. BJL (18),(22) supplies the published commuting formulas; scalar AM–GM alone does not identify the actual matrix barycenter. A compiled exact application verifies the actual formulas, Loewner comparison and equality for arbitrary finite positive diagonal data; the full commuting-family and near-order obligations remain open. |
| 6 | **Open formal obligation:** both counterexample types for every m,n≥2, with suitable chosen strictly positive normalized weights. Actual direct-sum means and repeated-input/split-weight correspondence are required. Identity padding changes the full-size minimum eigenvalues; for the second witness the second largest sorted index / count above 107/100 supplies the separator. No assertion is made for every prescribed weight vector. |
| 7 | The first strict-spectral converse is formally refuted. The other reverse and Qhalf consequences are retained as attributed written deductions from the second witness and BJL Theorem 1/(19),(54), without adding those published comparisons as axioms. Their exact formal consumers, including the near-to-entrywise bridge, remain separate obligations. |
| 8 | The source, credits, exact finite-check scope, attribution and open boundaries are preserved. The complete eight-group formal return is **incomplete**. The two general theorems have faithful compiled Reg attempts whose inspector status remains `declared_unresolved`; the mirrored Reg sources identify the precise linked unfinished scope. Independent review, applicable final-head CI and merge are not certified here. |

For the second witness the proof uses the established finite transport
criterion with M*=(3I+K*)/4 and K*=[[9,2√3],[2√3,90]]/(4√399), so
Ω=M*A*M*. The logarithmic sum is log(2)H with
H=[[51,√3],[√3,1]]/8. Positivity of H−I/10 and (107/100)^10<2
prove the lower spectral bound by CFC. The source's sharper explicit
λmin(L*)=2^((13−√157)/4) is preserved as written context, without claiming
that exact expression as a separately delivered Lean endpoint.

BJL weak log-majorization remains valid. Its actual Conjecture 1/(25)
concerns weak majorization, equivalently all unitarily invariant norms;
it is **not refuted**. Qhalf=(ΣwⱼAⱼ¹/²)² differs from Ω. The unposed
stronger entrywise Qhalf≤λΩ reading is the one obstructed by the written
second-witness deduction. Hiai arXiv:2508.20309v2, Propositions 4.6–4.7,
compares LE with a quasi-arithmetic mean (Qhalf at q=1/2), not Ω.
Gan–Huang's near-to-entrywise implication and spectral-geometric comparison
are distinct. Near and Loewner order agree for commuting X,Y in a common
basis; diag(2,1) and diag(1,2) show that identical sorted spectra do not
suffice. The all-r analytic rotation family and complete reverse-implication
classification remain open, and the original priority/access limitations
below remain in force.

### Literature status

The definitions and standard comparison results are literature-attested.
The exact witness and rotation coefficient have status `suspected-novel`
within the read scope recorded on #21282. That screen includes
Gan–Huang arXiv:2312.15394v2 and Hiai arXiv:2508.20309v2; their comparison
statements do not settle this exact question. The journal body and four
citing bodies were unread in that screen. Completeness is
**ASSUMED-UNVERIFIED**, with no unconditional priority claim.

## ASSUMED-UNVERIFIED

- Agreement of the final question between arXiv:2407.07438v1 and the journal body.
- Completeness of the literature screen, including unread citing works with
  DOIs `10.1007/s43037-025-00424-7`, `10.1080/03081087.2025.2564162`,
  `10.1016/j.jmaa.2025.130187` and `10.1007/s00025-025-02491-6`.
- Priority beyond the sources actually read; the formal proof certifies the
  mathematical refutation independently of that bibliographic boundary.
