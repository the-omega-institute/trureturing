---
slug: duschenes-garciamartin-holmes-cerezo-2026-chaar-concatenation
bibkey: duschenesgarciamartinholmescerezo2026moments
doi: 10.1103/grdp-jph9
url: https://arxiv.org/abs/2511.12700v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.result
---

# Concatenation can increase the cHaar moment norm

## Problem

M. Duschenes, D. García-Martín, Z. Holmes and M. Cerezo, *Moments of Quantum Channel Ensembles*, PRX Quantum **7**, 033050 (2026), DOI [10.1103/grdp-jph9](https://doi.org/10.1103/grdp-jph9), [arXiv:2511.12700v2](https://arxiv.org/abs/2511.12700v2), Appendix B, Conjecture 1, asks whether the cHaar moment norm is non-increasing with concatenations:

$$\|\widehat T_{\mathrm{cHaar}}^{(t)k'}\|_{HS}^2\leq\|\widehat T_{\mathrm{cHaar}}^{(t)k}\|_{HS}^2\quad(k'\geq k).$$

The verbal source clause is: “Further, it is conjectured that the cHaar norm is monotonically non-increasing with environment dimension and concatenations,”. Only the concatenation clause is refuted. [Preregistration #15553](https://github.com/the-omega-institute/trureturing/issues/15553) specifies the conventions and witness. [The Library note](../Library/QuantumChannels/duschenesgarciamartinholmescerezo2026moments.md) contains the source definitions, norm convention and locators.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Haar unitary on system and environment, with fixed pure ancilla; partial trace over environment. | `cHaarChannel d e U X`. | Reuses `PartialTraceMutualInformation.partialTraceRight`; its sum is exactly the preregistered sum. `Matrix.single 0 0 1` is the pure coordinate-zero ancilla. |
| The order-$t$ ensemble moment of the channel tensor power. | `momentOp d e t`. | All tensor factors use the same Haar sample, for every $t$. |
| Hilbert–Schmidt norm, squared. | `hsNormSq`, used in `claim`. | The definition is the double sum of `Complex.normSq` specified by #15553. Private `hsNormSqCorrespondence` equates this sum with the frozen `RHLinalg.frobSq` used by `normReindex`, `normNormal` and `result`. |
| All positive dimensions, moment orders and concatenation counts, with $k'\geq k$. | `claim`. | Positive $d,t,k$ and nonzero $e$; positive counts suffice for the witness. |
| Refutation at $d=e=t=2$, $k=4$, $k'=5$. | `result : ¬ claim`. | Literal universal claim negation; exact instance values are `instanceN4`, `instanceN5`. |

## Motivation

`CHaarConcatenationNonmonotone.result` refutes the finite-dimensional concatenation assertion. A decaying eigenmode is compatible with norm growth because the limiting projection is not orthogonal in the Hilbert–Schmidt geometry.

## Gap

The source and literature screen leave the finite-dimensional concatenation clause unsettled in the searched scope. M. Duschenes, *Effects of Noise on Optimization, Statistics, and Simulation of Quantum Systems*, University of Waterloo thesis (2026-06-23; [hdl:10012/23660](https://hdl.handle.net/10012/23660)), restates the hierarchy as a conjecture for all $t,k,d,s$ and gives no settlement of the concatenation clause. Its numerical check at $k=1,3$ does not reach the increase, which at $d=e=2$ first appears from $k=4$ to $k=5$ ([comment on #15553](https://github.com/the-omega-institute/trureturing/issues/15553#issuecomment-6111775899)). This is not an exhaustive-literature or originality claim. Theorem “cHaar explicit”, part 3, has a large-dimension limit scope and does not assert this finite-dimensional monotonicity.

## Route

Use the existing two-copy Haar average and its identity/swap commutant. `twirlFormula` derives its trace coefficients, and `momentOp2Formula` evaluates the order-two channel moment for every $d\geq2$ and nonzero $e$. At $d=e=2$, `moment22Reindex` identifies the literal moment with $A=P+Q/15+2R/5$. `aPow` gives the power normal form; `normNormal` evaluates its squared norm. The exact values in `instanceN4` and `instanceN5` contradict `claim`.

## Falsifier

A mismatch in the Haar measure, fixed ancilla, partial trace, tensor-copy convention, matrix-unit indexing or norm would invalidate the correspondence. The settlement compares exact fourth and fifth powers of the ensemble moment, with all factors sharing a Haar sample within each moment.

## Evidence

The Lean module is `D5/S3/Quantum/RandomCircuits/CHaarConcatenationNonmonotone.lean`, with its canonical Blueprint Scribe. Admission is `open-problem-resolution (#15553; Refuted)`, with certified-instance utility under `refutes`. The seven owner publications expose existing frozen proofs. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9). Every other newly authored public theorem would be an audit target; this module has none. No Reg file is delivered.

### Experiment reading

[Experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/4b35e9f007321a3364bb926919e27879aa107ad6/docs/reports/duschenes-et-al-2025-chaar-concatenation-monotonicity), path `docs/reports/duschenes-et-al-2025-chaar-concatenation-monotonicity/check.py`, commit `4b35e9f007321a3364bb926919e27879aa107ad6`. Command: `python3 check.py`. Exit $0$; `bad= 0`. Script SHA-256: `41bf402e6e928d46607598eca1e3ba176896fadb01f48ba2fe0d2376404dd9e8`. The implementation seat reran the pinned source.

The executed exact matrix-power checks cover $(d,e)=(2,2),(2,3),(3,2)$ and $1\leq k\leq8$, not every pair in $2\leq d,e\leq3$. The script checks the exact $N_4,N_5$ and difference at $(2,2)$, and eventual strict increase through $k=60$ of the closed-form sequence for each $2\leq d,e\leq6$. A seeded $20{,}000$-sample Haar Monte Carlo check at $(2,2)$ compares the second moment with the exact matrix, with tolerance $0.02$ and printed maximum deviation $0.0021$. These are finite computations, not a proof of the uniform family or an unbounded tail.

## Triage

Tier 1 published open conjecture; concatenation clause Refuted. Each claim has the evidence kind stated below.

### What the settlement shows

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Mechanism at $d=e=2$: with $u=I$, $w=2F-I$, $A=P+Q/15+2R/5$. | Proved; kernel-checked. | Private `moment22Reindex` identifies the moment; `aPow` proves $A^k=P+(1-(2/5)^k)Q/9+(2/5)^kR$ for $k\geq1$. |
| Squared norm $1+3b^2+z^2$ for real coefficients, and exact fourth/fifth values. | Proved; kernel-checked. | `normNormal`, `instanceN4`, `instanceN5`; $N_4=1213852/1171875<N_5=30362908/29296875$. Public `result` refutes `claim`. |
| Eventual strict increase at $t=2$ for every $d,e\geq2$. | Proved in prose. | Derivation below, based on the general order-two entry formula. No uniform Lean theorem is claimed. |
| Environment-dimension monotonicity clause. | Open. | Its display reverses its words; the intended direction is unclear and is not addressed. |
| Exact matrix powers, closed-form finite tails and Monte Carlo agreement. | Computed. | Exactly the pinned experiment and tested ranges in Evidence; command, exit and SHA-256 there. |
| The source's large-dimension theorem and other results. | Literature reading; scope statement. | “cHaar explicit”, part 3, concerns the large-dimension limit. This finite-dimensional witness does not refute that theorem. Any use requiring universal finite-dimensional concatenation monotonicity needs a replacement hypothesis or estimate. |

### Eventual increase for every $d,e\geq2$

Write $H=d^2e^2-1$, $F$ for the swap on the two system copies, $u=\operatorname{vec}(I)$ and $v=\operatorname{vec}(dF-I)$. Then $\langle u,v\rangle=0$, $\|u\|^2=d^2$ and $\|v\|^2=d^2(d^2-1)$. The general order-two entry formula says that the moment $B$ acts on a matrix $X$ as

$$B(X)=\frac{e^2}{H}\left(\operatorname{tr}X-\frac{\operatorname{tr}(FX)}{de}\right)I+\frac eH\left(\operatorname{tr}(FX)-\frac{\operatorname{tr}X}{de}\right)F.$$

Thus $Bu=u+\gamma v$, $Bv=\lambda v$, and $B$ annihilates the orthogonal complement of their span, where

$$\gamma=\frac{e-1}{H},\qquad \lambda=\frac{e(d^2-1)}H,\qquad 0<\lambda<1.$$

Indeed $H-e(d^2-1)=(e-1)(d^2e+1)>0$. Set $P=uu^\dagger/d^2$, $Q=vu^\dagger/d^2$ and $R=vv^\dagger/[d^2(d^2-1)]$. These three matrices are pairwise orthogonal for the Hilbert–Schmidt inner product, with squared norms $1,d^2-1,1$. For $k\geq1$, the triangular action gives

$$B^k=P+\frac{\gamma(1-\lambda^k)}{1-\lambda}Q+\lambda^kR
=P+\frac{1-\lambda^k}{d^2e+1}Q+\lambda^kR.$$

Consequently, for $c=(d^2-1)/(d^2e+1)^2>0$,

$$N_k=1+c(1-\lambda^k)^2+\lambda^{2k},$$

$$N_{k+1}-N_k=(1-\lambda)\lambda^k\left[2c-(1+c)(1+\lambda)\lambda^k\right].$$

Since $\lambda^k\to0$, every sufficiently large $k$ satisfies $\lambda^k<2c/[(1+c)(1+\lambda)]$, so the displayed difference is strictly positive. At $d=e=2$, $\lambda=2/5$, $c=1/27$, and the growing $Q$ coefficient is $(1-(2/5)^k)/9$. The same difference formula gives strict decrease when $\lambda^k>2c/[(1+c)(1+\lambda)]$, equality at the threshold, and strict increase below it. The limit $N_k\to1+c$ survives; uniform non-increase over all concatenations fails. The family derivation is prose, while Lean supplies the general entry formula and the exact finite witness.

## ASSUMED-UNVERIFIED

Literature completeness and originality are unverified beyond the recorded screen. The environment-dimension clause remains open. The all-$d,e$ eventual-increase derivation is not a uniform kernel-checked theorem.
