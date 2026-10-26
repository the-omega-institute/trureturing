---
slug: bouthat-chavez-sheng-2026-path-chs-remark43
bibkey: bouthatchavezsheng2026graphinequalities
doi: 10.48550/arXiv.2606.17356
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result
url: https://arxiv.org/abs/2606.17356v1
---

# The two identities of Remark 4.3

## Problem

Bouthat, Chávez and Sheng, *A general framework for inequalities on simple graphs*, arXiv:2606.17356v1, Remark 4.3, state the two path CHS identities as unproved and then assert a one-term simplification under $n+1\ge d/2$.

For every $n\ge1$ and even $d\ge2$, the symmetric value $h_d(\lambda(P_n))$ equals both the trigonometric sum and the bilateral zero-extended binomial sum printed in Remark 4.3.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $\|P_n\|_{X,d}^d=h_d(\lambda(P_n))$ | `PathCHSNormClosedForm.chs` | Same complete homogeneous symmetric value. |
| All $n\ge1$ and even $d\ge2$ | Arithmetic and parity hypotheses in `claim` | No degenerate path witness is used. |
| Trigonometric sum, $1\le k\le n$ | `trigForm`, with `Finset.Icc 1 n` | Every factor and exponent is literal. |
| Sum over all integers | `bilateralForm`, using `finsum` | Zero-extended binomials have finite support. |
| Both equalities | The two conjuncts in `claim` | Both are proved by `result`. |

## Motivation

The settling GID is `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result`, preregistered in #18566. The closed form for the original path-norm problem is `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` (#18565).

## Gap

The two full identities are proved. A uniform corrected truncation and uniform one-term boundary correction remain outside these Lean statements.

## Route

Partial fractions at the distinct Chebyshev nodes express complete homogeneous polynomials through nodal derivative weights. The weights are $2(-1)^{k+1}\sin^2(\pi k/(n+1))/(n+1)$. Pairing the bilateral indices identifies the binomial sum with the finite second-difference expression. These two routes give the two conjuncts of `result`.

The admission basis is `open-problem-resolution (#18566; Proved)`. The recurrence invariant `scaled_S_eval` proves $t^n S_n(t^{-1})=\operatorname{cont}(t^2;1,1;n)$ for $t\ne0$. It and its consumers `node_reciprocal_product`, `chs_eq_node_hsymm`, `chs_eq_trig` and `result` are content with `scaled_S_eval` as escape witness. Utility is `none`.

## Falsifier

An $n\ge1$ and even $d\ge2$ at which either expression differs from the complete homogeneous symmetric value would contradict `result`.

## Evidence

`D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result` proves the full literal `claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The four-slot escape audit is unfinished: [#18981](https://github.com/the-omega-institute/trureturing/issues/18981). No validated registration is claimed. The missing evidence comprises exact source reconstruction, realization bridges, whole-family variation and sensitivity for the dependent finite spectra and ring-polymorphic identities.

Experiment: [the published check of Remark 4.3](https://github.com/the-omega-institute/trureturing-experiments/tree/768095c6e50e44440547f401c54866f9d982711a/docs/reports/bouthat-chavez-sheng-2026-path-chs-remark). Command: `python3 /tmp/op-chavez/rework-51566/bcs-check.py 30 60`; exit 0. The file is the byte-exact `check.py` from that commit, SHA-256 `f967f78544056b1b68df4e3055cd34c76ad0183a4d9b37602166e74ac6b582fc`. For $1\le n\le30$ and even $2\le d\le60$, both full expressions agree with the exact symmetric value (the trigonometric evaluation uses 80-digit arithmetic). The printed finite truncation fails in 81 cases, beginning at $(1,4)$. The one-term formula fails in the 29 tested boundary cases $n+1=d/2$, with difference one, and agrees in the tested strict region $n+1>d/2$. At $(2,6)$ the exact symmetric value is one and the proposed expression is zero. Uniform corrections beyond this finite scope are open here.

## Triage

- **Proved, kernel-checked — #18565.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` gives the finite binomial formula and its real-root norm for every $n\ge1,m\ge2$.
- **Proved, kernel-checked — #18566.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result` gives both displayed identities for every $n\ge1$ and even $d\ge2$.
- **Refuted, kernel-checked — #18567.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result` disproves the one-term universal claim using $n=2,d=6$; the utility classification is `certified-instance` with `basis=refutes`.
- **Literature — open completeness boundary.** The source and the preregistrations' bounded literature screens identify no prior settlement. Completeness is `ASSUMED-UNVERIFIED`.

- **Computed.** The 81 truncation failures and 29 boundary discrepancies have exactly the finite scope in Evidence. No uniform theorem follows from those checks.
- **Open.** A corrected truncation range and the strict-versus-boundary rule for all $n,d$ require separate statements and proofs.

### What the settlement shows

- **Proved, kernel-checked.** `result` establishes both full formulas, including the full integer-indexed sum rather than the printed finite truncation.
- **Failure mechanism, explanation.** At $d/2=n+1$, the bilateral $j=-1$ term is $\binom{n+d-1}{0}-\binom{n+d-1}{-1}=1$. The printed lower cutoff is zero and discards this term. This identifies the boundary omission; the uniform corrected formula is not a Lean theorem here.
- **Computed nearest surviving statement.** The one-term expression agrees on the tested strict region $n+1>d/2$; at every one of the 29 tested boundary cases it is smaller by one. The uniform extensions are open.
- **Source dependence.** The original path-norm question is answered by #18565 and the two full identities by #18566. The closing simplification and finite truncation cannot be substituted for the full sum without further conditions. No other theorem of the source is asserted to require the false boundary formula.

## ASSUMED-UNVERIFIED

Literature completeness and independent priority are unverified. The source v1 and the bounded screens in #18566 are the literature evidence. The escape audit is unfinished under #18981.
