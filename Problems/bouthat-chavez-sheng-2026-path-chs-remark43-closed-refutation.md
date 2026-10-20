---
slug: bouthat-chavez-sheng-2026-path-chs-remark43-closed-refutation
bibkey: bouthatchavezsheng2026graphinequalities
doi: 10.48550/arXiv.2606.17356
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result
url: https://arxiv.org/abs/2606.17356v1
---

# The one-term formula at the boundary

## Problem

Bouthat, Chávez and Sheng, *A general framework for inequalities on simple graphs*, arXiv:2606.17356v1, Remark 4.3, state the two path CHS identities as unproved and then assert a one-term simplification under $n+1\ge d/2$.

The closing assertion is false. At $n=2,d=6$, $h_6(\lambda(P_2))=1$, whereas $((n^2+n-d)/((n+d)(n+d+1)))\binom{{n+d+1}}{{d/2}}=0$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $\|P_n\|_{X,d}^d=h_d(\lambda(P_n))$ | `PathCHSNormClosedForm.chs` | Same complete homogeneous symmetric value. |
| All $n\ge1$ and even $d\ge2$ | Arithmetic and parity hypotheses in `claim` | No degenerate path witness is used. |
| $d/2\le n+1$ | Natural quotient guard in `claim` | Exact for even $d$; equality is included. |
| One-term rational-binomial expression | Literal right side of `claim` | Real arithmetic and `Nat.choose`. |
| Failure of the universal formula | `result : ¬ claim` | Witness $n=2,d=6$ satisfies every guard. |

## Motivation

The settling GID is `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result`, preregistered in #18567. The closed form for the original path-norm problem is `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` (#18565).

## Gap

The one-term universal claim is refuted. A uniform corrected truncation and uniform one-term boundary correction remain outside these Lean statements.

## Route

The proof specializes the general `chs_formula` to $n=2,m=3$. Exact evaluation gives one, while the numerator of the proposed expression vanishes. This contradicts the universal claim. All hypotheses hold, including $d/2=n+1$.

The admission basis is `open-problem-resolution (#18567; Refuted)`. The result is bind-only under the finite-instance bypass test: if the two eigenvalues are $a,b$, the spectral trace and determinant identities give $a+b=0$ and $ab=-1$. Thus $b=-a$, $a^2=1$, and the seven terms $h_6(a,b)=\sum_{k=0}^6 a^{6-k}b^k$ reduce to $a^6=1$. This derivation is an algebraic explanation, not a separate Lean declaration. The delivered proof uses `chs_formula` directly. Utility is `kind=certified-instance; basis=refutes`.

## Falsifier

A value different from one for the exact symmetric value at $n=2,d=6$, or a failed hypothesis at that witness, would invalidate this refutation.

## Evidence

`D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result` proves the negation of the full literal `claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment: [the published check of Remark 4.3](https://github.com/the-omega-institute/trureturing-experiments/tree/768095c6e50e44440547f401c54866f9d982711a/docs/reports/bouthat-chavez-sheng-2026-path-chs-remark). Command: `python3 /tmp/op-chavez/bcs-check.py 30 60`; exit 0. The file is the byte-exact `check.py` from that commit, SHA-256 `f967f78544056b1b68df4e3055cd34c76ad0183a4d9b37602166e74ac6b582fc`. For $1\le n\le30$ and even $2\le d\le60$, both full expressions agree with the exact symmetric value (the trigonometric evaluation uses 80-digit arithmetic). The printed finite truncation fails in 81 cases, beginning at $(1,4)$. The one-term formula fails in the 29 tested boundary cases $n+1=d/2$, with difference one, and agrees in the tested strict region $n+1>d/2$. At $(2,6)$ the exact symmetric value is one and the proposed expression is zero. Uniform corrections beyond this finite scope are open here.

## Triage

- **Proved, kernel-checked — #18565.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormClosedForm.result` gives the finite binomial formula and its real-root norm for every $n\ge1,m\ge2$.
- **Proved, kernel-checked — #18566.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43.result` gives both displayed identities for every $n\ge1$ and even $d\ge2$.
- **Refuted, kernel-checked — #18567.** `D5/S3/Combinatorics/Graph/PathCHS/PathCHSNormBCSRemark43ClosedRefutation.result` disproves the one-term universal claim using $n=2,d=6$; the utility classification is `certified-instance` with `basis=refutes`.
- **Literature — open completeness boundary.** The source and the preregistrations' bounded literature screens identify no prior settlement. Completeness is `ASSUMED-UNVERIFIED`.

- **Computed.** The 81 truncation failures and 29 boundary discrepancies have exactly the finite scope in Evidence. No uniform theorem follows from those checks.
- **Open.** A corrected truncation range and the strict-versus-boundary rule for all $n,d$ require separate statements and proofs.

### What the settlement shows

- **Refuted, kernel-checked.** `result` exhibits the failure of the claimed one-term formula with every source hypothesis satisfied.
- **Failure mechanism, explanation.** At $d/2=n+1$, the bilateral $j=-1$ term is $\binom{n+d-1}{0}-\binom{n+d-1}{-1}=1$. The printed lower cutoff is zero and discards this term. This identifies the boundary omission; the uniform corrected formula is not a Lean theorem here.
- **Computed nearest surviving statement.** The one-term expression agrees on the tested strict region $n+1>d/2$; at every one of the 29 tested boundary cases it is smaller by one. The uniform extensions are open.
- **Source dependence.** The original path-norm question is answered by #18565 and the two full identities by #18566. The closing simplification and finite truncation cannot be substituted for the full sum without further conditions. No other theorem of the source is asserted to require the false boundary formula.

## ASSUMED-UNVERIFIED

Literature completeness and independent priority are unverified. The source v1 and the bounded screens in #18567 are the literature evidence. The other public theorems in this delivery have unfinished escape audits under #18981.
