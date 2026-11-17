---
slug: skoric-truncated-binomial-mean
bibkey: skoric2021signatures
doi: 10.26421/QIC21.11-12-4
url: https://arxiv.org/abs/2012.15493v2
triage: theorem
motivation_gids:
  - D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.result
---

# Škorić's normalized truncated-binomial mean

## Problem

Boris Škorić, *Quantum digital signatures with smaller public keys*, arXiv:2012.15493v2, §6.2, equation (35), journal p.966, states Conjecture 1:

> Let $f(x,r)$ be defined as $f(x,r)=\frac1r\frac{\sum_{w=0}^r w\binom{x}{w}}{\sum_{w=0}^r\binom{x}{w}}$, $r\leq x/2$. The function $f(x,r)$ is decreasing in $r$.

The preregistered integer reading is proved: for natural $x\geq2$ and positive integer caps $r<s$ with $2s\leq x$, $f(x,s)\leq f(x,r)$. Preregistration: [#24239](https://github.com/the-omega-institute/trureturing/issues/24239).

### Statement echo

| Source clause | Lean counterpart | Fidelity and boundary |
| --- | --- | --- |
| Equation (35), including both endpoints | `f` | Literal finite sums over `Finset.range (r+1)` with `Nat.choose` cast to the reals and the factor $1/r$. |
| Integer counting size | natural `x` | The preregistered counting interpretation; no real upper argument is quantified. |
| Positive cap and $r\leq x/2$ | $1\leq r<s$ and $2s\leq x$ in `claim` | Both compared caps are positive and in the source domain; no integer-division rounding is introduced. |
| Decreasing in the cap | `result : claim` | Decreasing means nonincreasing: $f(x,s)\leq f(x,r)$. |
| Extra binder $2\leq x$ | `claim` | Implied whenever distinct positive admissible caps exist; rows with no such pair impose no comparison. |
| Real field division at cap zero | totalized `f` | Zero cap is outside every asserted comparison. All compared denominators are positive. |

## Motivation

Conjecture 1 supplies a scalar monotonicity premise in source Propositions 1 and 2. Proving it removes that named premise; the remaining derivations and protocol security analysis are not formalized by this settlement.

## Gap

The source poses the cap comparison rather than proving it. The registered conclusion is the unrestricted integer-row comparison on the source's positive caps. The bounded literature screen in #24239 located no verified exact settlement; literature completeness is `ASSUMED-UNVERIFIED`. No worldwide priority claim is made.

## Route

For a positive finite row $(a_k)_{k=0}^m$ satisfying $ka_k^2\geq(k+1)a_{k-1}a_{k+1}$ for $1\leq k<m$, put $S_r=\sum_{k=0}^r a_k$ and $T_r=\sum_{k=0}^r ka_k$. The private helpers prove the weighted-ratio comparison and inward-product domination. Symmetrizing $S_rT_r$ and partitioning by the sum of the two indices bounds every high block against the subtraction in

$$D_r=(r+1)S_{r+1}T_r-rS_rT_{r+1}
=S_rT_r-(r+1)a_{r+1}\sum_{j=0}^{r-1}(r-j)a_j.$$

The low pair $(0,1)$ has positive contribution, so `D_positive` proves $D_r>0$. The positive denominators give `adjacent_strict`; `chain_nonstrict` chains these comparisons. The private `choose_fac` uses `Nat.choose_succ_right_eq`, and `choose_row_pos` uses `Nat.choose_pos`, to specialize to $a_k=\binom{x}{k}$ in `result`.

## Falsifier

A source-domain counterexample would be natural $x,r,s$ with $2\leq x$, $1\leq r<s$, $2s\leq x$ and $f(x,r)<f(x,s)$. `result` rules out this entire quantified class. Failure of a real-upper-argument extension or a protocol security claim would not contradict this theorem.

## Evidence

The settling declaration is `D5.S3.Entropy.PoissonBinomial.SkoricTruncatedBinomialMean.result` in `D5/S3/Entropy/PoissonBinomial/SkoricTruncatedBinomialMean.lean`. It proves the literal `claim`. The public surface is `f`, `claim`, `result`; the general row argument remains private. The module is generality G, has `utility: none`, and is admitted by `open-problem-resolution (#24239; Proved)`. It imports Mathlib only and has no D5 frozen prerequisite.

The four-slot escape audit for `result` is unfinished: [#26175](https://github.com/the-omega-institute/trureturing/issues/26175). No valid Reg mirror is delivered. A faithful dependent-family registration still needs source reconstruction, whole-family variation and sensitivity, and actual observational dependence. No `declared_validated` registration is claimed.

### Finite exact experiment

[Experiment directory at `bb743940e170f91b8b857c02220cdc6f35e8c3ea`](https://github.com/the-omega-institute/trureturing-experiments/tree/bb743940e170f91b8b857c02220cdc6f35e8c3ea/docs/reports/skoric-truncated-binomial-mean).

The pinned script is `docs/reports/skoric-truncated-binomial-mean/check.py`, SHA-256 `0edc1713935c3c2e946497746c197ff2b40ba9c9b50a77b69f3720c5aa954e28`. The implementation-seat command `git -C /Users/auric/trureturing-experiments show bb743940e170f91b8b857c02220cdc6f35e8c3ea:docs/reports/skoric-truncated-binomial-mean/check.py | python3` exits 0 and reports `ALL_CHECKS_OK`. It uses exact integer and rational arithmetic.

## Triage

1. **Proved; kernel-checked:** generic positive-row adjacent strict decrease under the displayed factorial log-concavity hypothesis, through private `D_positive`, `adjacent_strict`, and `chain_nonstrict`. Their caps and positivity assumptions are explicit; these are not independent public distribution corollaries.
2. **Proved; kernel-checked:** the integer binomial specialization through private `choose_fac` and `choose_row_pos`.
3. **Proved; kernel-checked:** the registered `claim`, by public `result`.
4. **Computed:** the pinned exact checker verifies 100 fidelity identities for $z=1,\ldots,100$; 328350 source-domain cap pairs and 19900 adjacent comparisons for integer rows $x=2,\ldots,200$; 786 ULC rows of lengths 3 through 8; 18430 cap pairs for 305 rational upper arguments in $[2,40]$; and 116 interior Poisson-binomial laws with 2 through 7 coordinates. Its final reading is `ALL_CHECKS_OK`. These are exactly the finite ranges checked, not a universal proof.
5. **Open as registered Lean extensions:** biased binomials, interior Poisson-binomial rows, and real falling-product upper arguments have no separate registered declaration in this module. Applying the row argument to these families requires verifying their positivity and factorial log-concavity in the chosen representation. The finite experiment supplies only the scopes in item 4.

### What the settlement shows

**Proved; kernel-checked:** the decisive mechanism is the positive convolution remainder in `D_positive`. `adjacent_strict` applies whenever the row is positive through the next cap and satisfies the factorial inequality there. `chain_nonstrict` covers $1\leq r\leq s\leq m$, so the generic argument does not require the half-row restriction. The integer binomial specialization is used in `result`, whose public conclusion retains the registered source domain.

**Explanation:** positivity of the surviving low pair explains strict adjacent decrease. This module does not classify equality when positivity is relaxed; such a classification remains open here. The finite biased-binomial, Poisson-binomial and real-upper-argument checks do not certify their uniform extensions.

**Source consequence:** Conjecture 1 no longer supplies an unproved scalar premise in Propositions 1 and 2. Their other assumptions and the deferred swap-test/security analysis remain outside the Lean conclusion.

## ASSUMED-UNVERIFIED

Literature completeness remains `ASSUMED-UNVERIFIED`: citation databases may omit work; the identified citing paper and the full Shanthikumar–Yao theorem/model correspondence are unread or unverified; broker-reported readings are not all independently replayed; MathDB's solution count and exhaustive broad author/citation coverage are unknown. The bounded source and literature evidence is recorded in #24239. Four-slot registration evidence is unfinished under #26175.
