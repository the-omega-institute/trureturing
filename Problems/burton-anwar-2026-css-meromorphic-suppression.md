---
slug: burton-anwar-2026-css-meromorphic-suppression
bibkey: burton2026meromorphic
doi: 10.48550/arXiv.2605.06251
url: https://arxiv.org/abs/2605.06251v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CSSMeromorphicSuppression.result
---

# Burton–Anwar CSS meromorphic suppression

## Problem

Simon Burton and Hussain Anwar, “Meromorphic Quantum Computing”, arXiv:2605.06251v1 (2026), Section 4, Conjecture 4.8, asks whether every CSS code $[[n,1,d]]$ with logical operators $X^{\otimes n}$ and $Z^{\otimes n}$ has coherent error suppression $O(\varepsilon^d)$ at $z=0,\infty,\pm1$. The binding conventions are the binary stabilizer subspaces and decoder amplitudes recorded in issue #14813.

## Motivation

For $\psi_z=(1,z)$, the codeword derivation in Theorem 4.4 and Appendix B gives, up to common normalization,
$$Q(z)=\sum_{g\in G_X}z^{\mathrm{wt}(g)},\qquad P(z)=\sum_{g\in G_X}z^{\mathrm{wt}(g+1)}.$$
The settling declaration `D5/S3/Quantum/Information/CSSMeromorphicSuppression.result` proves the universal claim `claim`, with `utility: none`.

## Gap

The source states the four-point conjecture but does not prove its distance lower bound. The exact-order sentence immediately after the conjecture is stronger than the conjecture and is contradicted by the source’s own $[[15,1,3]]$ example. The source corollary printed after Theorem 4.4 also contains an identically zero denominator.

## Route

The proof maps each $g\in G_X$ to $g+1$, a non-stabilizer logical-X representative, so every numerator exponent is at least $d$ while $Q(0)=1$. The degree-$n$ reversal exchanges the numerator and denominator roles at infinity. A binary character-sum factorization of $P-Q$ and $P+Q$ restricts to odd logical-Z representatives (and complements of even stabilizers), giving the distance divisibility at $1$ and $-1$ and the fixed-point equalities. The kernel-checked public result is the sole settling theorem; private helpers are consumed on its live proof path.

## Falsifier

A CSS code satisfying the issue #14813 hypotheses with a local order below $d$ at one of $0,\infty,1,-1$ would refute the result. The exact equalities of local orders with $d_X$ and $d_Z$ are computed for the tested finite corpus and are not asserted as a universal Lean theorem here.

## Evidence

The module compiles with the axiom closure of every public declaration contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. Its Scribe node carries `OpenProblemResolutionClaim` with resolution `Proved`. The Library note `Library/QuantumBounds/burton2026meromorphic.md` records Section 4, Proposition 4.3, Theorem 4.4, the misprinted corollary, Conjecture 4.8 and Appendix B.

**Numerical experiment.** The exact-arithmetic check is pinned at [burton-anwar-2026-css-meromorphic-suppression](https://github.com/the-omega-institute/trureturing-experiments/tree/602ec65402d492351ebc19230b04caa93001cda8/docs/reports/burton-anwar-2026-css-meromorphic-suppression). Command: `python3 check.py`; exit code 0. Script SHA-256: `3a59a3e7d8503363420a9c0ed3738e8d611a06de9e74effc0caa6901953a684b`. Readings: 81 codes tested, 0 violations, exact equality with $d_X$ at $0,\infty$ and $d_Z$ at $\pm1$ for all 81; the Steane code has $d=3$ and orders $(3,3,3,3)$; 74 tested codes have $d=1$ and 7 have $d=3$; minimum order minus distance is 0. The corpus is the Steane code and 80 sampled codes with $n\in\{5,7,9,11\}$.

Source-example reading: the script is pinned at [check-source-example.py](https://github.com/the-omega-institute/trureturing-experiments/blob/8ad710e0dfe08b1a4c097f0f9264e9c3186e4a6a/docs/reports/burton-anwar-2026-css-meromorphic-suppression/check-source-example.py). Command `python3 check-source-example.py`; exit 0; script SHA-256 `09ba6babcf13112d1b2d5ce414360e9f80273775a5ea393871ddf142417c6896`. Tested scope: only the source $[[15,1,3]]$ decoder $f(z)=(z^{15}+15z^7)/(15z^8+1)$, at $0,\infty,1,-1$; local degrees $(7,7,3,3)$.

## Triage

`theorem`; resolution `proved` for MQC-1 / Conjecture 4.8.

| Item | Status | Evidence and boundary |
| --- | --- | --- |
| $g\mapsto g+1$ maps each X-stabilizer to a logical-X representative, every numerator exponent is at least $d$, and the denominator is $1$ at $0$ | proved | `logical_X`, `logical_X_weight`, `decoderNum_X_dvd`, `decoderDen_eval_zero`, `decoderNum_eval_zero`, and `zero_suppression` on the live path to `result`. |
| Degree-$n$ reciprocity gives the point at $\infty$ | proved | `reverseDen_eq_num`, `reverseNum_eq_den`, and `infinity_suppression` in the settled module. |
| At $\pm1$, the binary character-sum identity factors $P\mp Q$ through logical-Z representatives | proved | `full_fourier`, `group_char_sum`, `coset_fourier`, `decoder_scaled_sub`, `decoder_scaled_add`, `logical_Z_of_odd_dual`, `odd_dual_weight`, `even_dual_complement_weight`, `decoder_sub_one_dvd`, `decoder_add_one_dvd`, and the two fixed-point evaluations. |
| Exact local degrees equal $d_X$ at $0,\infty$ and $d_Z$ at $\pm1$ | computed | `python3 check.py` in the pinned experiment entry above, exit 0, script SHA-256 `3a59a3e7d8503363420a9c0ed3738e8d611a06de9e74effc0caa6901953a684b`; scope is the Steane code and 80 sampled CSS codes with $n\in\{5,7,9,11\}$. A universal exact-degree theorem is open here. |
| The source’s post-Conjecture-4.8 gloss claiming order-$d-1$ zeros of $f'$ | computed | The source-example reading above (`python3 check-source-example.py`, exit 0, SHA-256 `09ba6babcf13112d1b2d5ce414360e9f80273775a5ea393871ddf142417c6896`) gives local degrees $7,7,3,3$ at $0,\infty,1,-1$, so the gloss is false in general; the settled theorem claims only the lower bound $m_z(f)\ge d$. |
| The corollary after Theorem 4.4 | proved (misprint) | Its printed denominator $W(1,h)-W(1,h)$ is identically zero. The character-sum factorization above is the nonzero identity used by this proof; the result does not depend on the printed corollary. |
| CSS codes with $k>1$ and multivariate decoders | open | The module treats one logical qubit and one variable. |
| Non-CSS codes, or CSS codes whose logical operators are not $X^{\otimes n},Z^{\otimes n}$ | open | These hypotheses are outside `CSSCode` and `claim`. |
| The full fixed-point and critical-point structure beyond the four stabilizer states | open | No global classification of the decoder’s other fixed or critical points is asserted. |

### What the settlement shows

**Proved.** The support-complement argument, degree-$n$ reversal, and binary character orthogonality establish the four fixed points and the distance lower bound in the exact CSS conventions of issue #14813.

**Computed.** On all 81 enumerated codes in the pinned experiment, the local degree is exactly $d_X$ at $0$ and $\infty$ and exactly $d_Z$ at $1$ and $-1$. The universal exact-degree identification remains open.

**Computed.** The source’s order-$d-1$ derivative gloss fails on its own $[[15,1,3]]$ example, whose local degrees are $7,7,3,3$.

**Proved (misprint).** The displayed post-Theorem-4.4 denominator $W(1,h)-W(1,h)$ vanishes identically; the proof uses the binary character-sum form instead.

**Open.** Multivariate $k>1$ decoders, non-CSS or differently logical codes, and the remaining fixed/critical-point structure require additional statements outside this settlement.

## ASSUMED-UNVERIFIED

The literature search supports only the preregistered “not found in searched scope” boundary; worldwide priority is not a kernel fact. The source’s analytic CP$^1$ interpretation is cited through the Library note and codeword derivation, while the Lean theorem proves the stated polynomial and root-multiplicity claim under the binding definitions. The computed exact-degree and derivative-gloss readings are finite numerical/source checks, not additional frozen Lean declarations.

The §3.9 escape audit for `D5/S3/Quantum/Information/CSSMeromorphicSuppression.result` is unfinished (`DTR-Unregistered`). A faithful `DependentFamily` registration needs a source-bound decoder readout, the complete guarded four-point law, and checked variation, sensitivity and observational-dependence witnesses. Those binding proofs are not delivered. See [issue #14883](https://github.com/the-omega-institute/trureturing/issues/14883).
