---
slug: hirche-guan-tomamichel-2023-renyi-order-three-equality
bibkey: hircheguantomamichel2023renyicombining
doi: 10.1109/ISIT54713.2023.10206941
url: https://arxiv.org/abs/2305.02589v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.result
---

# Order-three Rényi information-combining equality

## Problem

C. Hirche, X. Guan and M. Tomamichel, “Chain Rules for Rényi Information
Combining”, arXiv:2305.02589v1, Section V, Conjecture V.5, state:

> For $\alpha\in[2,3]$ the same holds with $\geq$ exchanged by $\leq$ and
> for $\alpha\in\{2,3\}$ the above holds with equality.

The settlement is the $\alpha=3$ equality clause for two independent,
equiprobable binary classical-quantum inputs. Each input has two
positive semidefinite, trace-one complex matrices in an arbitrary finite
dimension. Put $H_i=\widetilde H_3^\downarrow(X_i|B_i)_{\rho_i}$ and
$H_{\rm out}=\widetilde H_3^\downarrow(X_1+X_2|B_1B_2)_\tau$, with $X_2$
traced out of the CNOT state. Then

$$
\begin{aligned}
H_1+H_2\leq\log2&\Longrightarrow
H_{\rm out}=h_3(h_3^{-1}(H_1)\ast h_3^{-1}(H_2)),\\
\log2\leq H_1+H_2&\Longrightarrow
H_{\rm out}=H_1+H_2-\log2+
 h_3(h_3^{-1}(\log2-H_1)\ast h_3^{-1}(\log2-H_2)).
\end{aligned}
$$

Here $p\ast q=p(1-q)+(1-p)q$, and $h_3^{-1}$ is the inverse on probabilities
in $[0,1/2]$. Both guards hold at the common boundary. The binding matrix,
inverse and natural-logarithm conventions are in
[#15115](https://github.com/the-omega-institute/trureturing/issues/15115).

## Motivation

The frozen declaration
`D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.result : claim`
proves both branches. It provides the quantum, noncommuting counterpart of the
classical order-three equality and the explicit expression anticipated in the
remark after Proposition V.4 of the pinned PDF. Positive definiteness and
commutativity are not additional hypotheses.

## Gap

The preregistration's literature reading found no quantum order-three settlement
in the source, the named citing works or the screened later papers. This is
`not-found-in-searched-scope`, not an exhaustive literature or priority claim.
The pinned PDF numbers the order-two result Proposition V.3, equation (V.13),
and its dual result Proposition V.4, equation (V.14). The order-three remark
follows V.4; Conjecture V.5 is equation (V.15).

## Route

For one input let $r=(\sigma_0+\sigma_1)/2$,
$A=r^{-1/3}\sigma_0r^{-1/3}/2$, $B=r^{-1/3}\sigma_1r^{-1/3}/2$,
$S=A+B$ and $D=A-B$. Functional calculus gives $S^3=r$, including singular
$r$; negative powers act on the support. Cyclicity of the trace gives

$$
K=e^{-2H}=\operatorname{tr}(A^3+B^3)
 =\frac{1+3t}{4},\qquad t=\operatorname{tr}(SD^2).
$$

The product marginal is $r_1\otimes r_2$. Its functional-calculus powers
factorize, so the XOR moment is $t_1t_2$ and

$$
e^{-2H_{\rm out}}=\frac{1+3t_1t_2}{4}
 =\frac{4K_1K_2-K_1-K_2+1}{3}.
$$

Positivity yields $K_i\in[1/4,1]$ and $H_i\in[0,\log2]$.
The scalar identity $e^{-2h_3(p)}=(1+3(1-2p)^2)/4$ and
$1-2(p\ast q)=(1-2p)(1-2q)$ give the first branch. Reflecting
$H_i$ to $\log2-H_i$ replaces $K_i$ by $1/(4K_i)$ and gives the second.
The proof reuses `GHZMeasureBiseparableBound.IsDensity`,
`PartialTraceMutualInformation.partialTraceLeft`,
`PartialTraceMutualInformation.kronecker_eq_conj_diagonal_eigenvalues`,
`ProjectionProbabilityFlow.trace_hermitian_product_real`, and
`RHLinalg.trace_mul_nonneg_of_posSemidef`.

## Falsifier

A counterexample would consist of four density matrices satisfying the stated
independence and equiprobability assumptions for which either guarded equality
fails. Correlated input systems or unequal classical weights are outside this
claim. A source-convention mismatch or a prior published settlement would
invalidate the stated fidelity or literature boundary independently of kernel
compilation.

## Evidence

The settling declaration is `result : claim` in
`D5/S3/Quantum/Information/RenyiInformationCombiningOrderThree.lean`; its Scribe
has one Proved `OpenProblemResolutionClaim`. All theorem proofs are classified
`bind-only`, the helpers have named consumers, and the admission basis is
`open-problem-resolution (#15115; Proved)`. Utility is `none`: this is a general
identity, with no fixed numerical certificate. The axiom closure of every public
declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},
\mathrm{Quot.sound}\}$.

Experiment entry:
[`docs/reports/hirche-guan-tomamichel-2023-renyi-order-three-xor/`](https://github.com/the-omega-institute/trureturing-experiments/tree/7847a3ca3e7432801ff09b0db12c8d2b9ffa9616/docs/reports/hirche-guan-tomamichel-2023-renyi-order-three-xor),
script `docs/reports/hirche-guan-tomamichel-2023-renyi-order-three-xor/check.py`,
commit `7847a3ca3e7432801ff09b0db12c8d2b9ffa9616`, SHA-256
`f5936cfa8d9def03e4c21033e0027d6b067ee06cb2528312df3b8a2ea43bf746`.
Command: `python3 check.py 7`, exit 0; reading:
`trials=400 max_abs_err=1.343e-14`. The checked scope is 400 random
noncommuting input pairs with dimensions 1–4 and random ranks, including
rank-deficient matrices; literal support inverse powers, the four-system state
with $X_2$ traced out, both branches, the closed formula and the input entropy
ranges are checked. Numerical agreement is supporting evidence, not a proof.

The escape audit for the sole public theorem `result` is unfinished under
[#15282](https://github.com/the-omega-institute/trureturing/issues/15282).
The dependent-family source reconstruction bridge elaborates, but whole-family
variation, sensitivity of all three entropy readouts, actual observational
dependence and exact source-selection occurrence evidence are missing. No Reg
source or completed four-slot registration is delivered.

## Triage

### What the settlement shows

- **Proved in this module — the mechanism and equality.** The private
  `input_trace_moment`, `kronecker_rpow`, `xor_moment`, `output_entropy_exp`
  and `scalar_readout` occur in the proof of `result`. At order three the
  sandwich exponent is $-1/3$, the cubic trace is affine in $t$, and the XOR
  moment factorizes. Thus the explicit closed form is
  $H_{\rm out}=-\frac12\log((4K_1K_2-K_1-K_2+1)/3)$.
  Both source branches are kernel-checked for arbitrary finite dimensions,
  singular marginals and noncommuting inputs. No extension to correlated
  inputs or unequal classical weights is asserted.
- **Proved in the source; cited here — order two.** Proposition V.3,
  equation (V.13), gives the order-two equality. Proposition V.4 is its
  dual-entropy equality. Expanding the square of the sandwiched blocks gives
  the quadratic counterpart of the same method. This source argument is
  cited; the module does not formalize an order-two theorem.
- **Computed — numerical readings.** The pinned experiment entry and command
  in Evidence give exit 0, `trials=400 max_abs_err=1.343e-14`, with SHA-256
  and tested dimensions and ranks stated there. A uniform assertion beyond
  this experiment is not inferred from its sampling; the order-three theorem
  supplies the exact finite-dimensional conclusion.
- **Open — other orders.** The inequality clauses of Conjecture V.5 for
  $\alpha\notin\{2,3\}$, and closed forms at other integer orders, are neither
  proved nor refuted here. They require separate statements and evidence.
- **Source dependency boundary.** The order-three equality supplies this
  endpoint of Conjecture V.5 and the formula anticipated after V.4. The
  paper's independently proved chain rules and order-two result retain their
  stated hypotheses and conclusions; no all-order conjecture is settled.

## ASSUMED-UNVERIFIED

The literature reading does not exclude an unindexed prior settlement or prove
priority. The numerical experiment has only the tested scope stated above.
The missing four-slot audit evidence remains the explicit boundary in #15282;
mathematical compilation and an Observe finding do not complete it.
