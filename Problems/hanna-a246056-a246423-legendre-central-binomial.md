---
slug: hanna-a246056-a246423-legendre-central-binomial
bibkey: hanna2014a246056a246423
doi: null
url: https://oeis.org/A246056
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.result
---

# Hanna’s ternary-digit residue conjecture

## Problem

P. D. Hanna, [OEIS A246056](https://oeis.org/A246056), Name and Comments; [preregistration #18887](https://github.com/the-omega-institute/trureturing/issues/18887).

> Conjecture: a(n) == 1 (mod 3) when n = 2*A005836(k) for k >= 0, and a(n) == 0 (mod 3) otherwise, where A005836 gives numbers whose base-3 representation contains no 2.

Its generating function is $\sum_{n\ge0}x^n(1-2x)^{-2n-1}Q_n(2x)Q_n(3x)$, with offset zero. The conjecture is proved.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The Name generating function | `term` and coefficientwise `A` | Literal preregistered rational expressions; the coefficient at $m$ uses $n\le m$. |
| Every natural index | Outer universal quantifier in `claim` | Includes zero. |
| Integer coefficient | Existential integer $z$ equal to the rational coefficient | Explicit cast to $\mathbb Q$; integrality is retained. |
| $n=2\,A005836(k)$ | An $m$ with $n=2m$ and $2\notin\operatorname{Nat.digits}(3,m)$ | Zero has the empty digit list and qualifies. |
| Residue one on that support, zero otherwise | Both implications in `claim` | Neither support nor complement is dropped. |

The public `result` proves exactly `claim`, without additional hypotheses. The definitions are mirrored in [the Library note](../Library/RecurrenceComposition/hanna2014a246056a246423.md).

## Motivation

The two generating functions differ only in the linear denominator. Their integer lifts share the alternating binomial-square transform. The companion settlement is preregistered as [#18888](https://github.com/the-omega-institute/trureturing/issues/18888) and has its own result and dossier.

## Gap

The preregistration records the source and literature screen: the OEIS comments cite no proof; searches of the OEIS Open catalogue, formal-conjectures, the cited OEIS-proof papers and the repository found no settlement in the searched scope. The classical Legendre generating function and Lucas congruence are established results. Literature completeness and independent priority are `ASSUMED-UNVERIFIED`.

## Route

Write $Q_n(t)=\sum_{k=0}^n\binom nk^2t^k$ and
$R(x)=\sum_{n\ge0}x^n(1+x)^{-2n-1}Q_n(-x)$.
The integer coefficient transform gives
$[x^N]R=0$ for odd $N$ and $[x^{2m}]R=(-1)^m\binom{2m}m$.
Every source summand has order at least its index, so every coefficient uses a finite sum. Mapping the integer series to the rationals proves integrality without an analytic convergence assumption.

Modulo three the second polynomial factor becomes one, while $2=-1$. The resulting series is $R$. Lucas’ recurrence proves that $(-1)^m\binom{2m}m$ is one exactly when the ternary digits of $m$ contain no two, and zero otherwise.

## Falsifier

The full source generating function, its offset zero and the complementary residue class are essential. A finite coefficient test alone does not prove the all-index assertion. The settling result has no hypotheses and proves the complete claim, with an integer coefficient witness at every index in its stated domain.

## Evidence

The settling declaration is `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialModThree.result`. The shared supporting module is `D5/S1/Recurrence/Invariants/HannaLegendreCentralBinomialTransform`. The source definitions and the complete result statement have Blueprint descriptions. The axiom closure is checked separately from the literature priority claim.

Experiment: [published program and data](https://github.com/the-omega-institute/trureturing-experiments/tree/335fe22acf7d96c96020b362815b153f6600ba7e/docs/reports/oeis-a246056-legendre-central-binomial-mod3). Command: `python3 check.py 300 b246056.txt`, exit 0, `RESULT PASS`; `check.py` SHA-256 `06014b6eda1775f2e30f136a4e8a590c84d394dcbf668613d2914b970dfacc8e`. Tested degrees $0\ldots300$: equality with the b-file, the exact reduced-series coefficients, reduction modulo three and the ternary-digit residue rule.

The escape audit is unfinished for the eleven public theorems enumerated in [#19311](https://github.com/the-omega-institute/trureturing/issues/19311). No Reg registration is delivered. Missing evidence consists of faithful full-telescope realization bridges, enrolled readouts and compiled variation, sensitivity and observational-dependence proofs.

## Triage

### What the settlement shows

- **Kernel-checked:** both original all-index residue conjectures, including integrality, are stated by `HannaLegendreCentralBinomialModThree.result` and `HannaLegendreCentralBinomialModFour.result` under the namespace `D5.S1.Recurrence.Invariants`.
- **Kernel-checked:** the shared exact integer binomial-square identity is `HannaLegendreCentralBinomialTransform.square_binomial_sum`; the alternating central-binomial coefficient formula is `HannaLegendreCentralBinomialTransform.R_coeff`.
- **Proved in prose:** the rational closed form is $R(x)=(1+4x^2)^{-1/2}$. Indeed the formal binomial expansion gives $\binom{-1/2}{m}4^m=(-1)^m\binom{2m}m$, so its coefficients equal the kernel-checked formula. The fractional power denotes the rational formal binomial series with constant coefficient one.
- **Kernel-checked:** `HannaLegendreCentralBinomialTransform.T_coeff`, `T_odd` and `T_even` give the exact first-moment coefficients for $T(x)=\sum_{n\ge0}n x^n(1+x)^{-2n-1}Q_n(-x)$; these are private, consumed declarations. `T_mod_two` gives $T\equiv x\pmod2$. The mod-four module's `twice_T2_four`, `source_residue_four` and `result` prove the correction and its cancellation at degree two, explaining why the exponent starts at two.
- **Proved in prose:** $T(x)=x(1-2x)(1+4x^2)^{-3/2}$. The coefficient of $x^{2m}$ in the last factor is $(-1)^m(2m+1)\binom{2m}m$. Multiplication by $x-2x^2$ gives exactly `T_odd` and `T_even`, since $2(2m+1)\binom{2m}m=(2m+2)\binom{2m+1}m$; the constant coefficient is zero.
- **Computed:** `check.py` checks A246056 against its b-file, the exact reduced-series coefficients and the ternary residue law for degrees $0\ldots300$; its pinned program, hash, command and exit are in the [A246056 experiment entry](hanna-a246056-a246423-legendre-central-binomial.md#evidence). This is a finite check.
- **Computed:** `check_a246423.py` checks A246423 against its b-file, the exact $R$ and $T$ coefficients and both moment/residue reductions for degrees $0\ldots300$; its pinned program, hash, command and exit are in the [A246423 experiment entry](hanna-a246423-legendre-central-binomial.md#evidence). This is a finite check.
- **Open:** the separate route-check program's Legendre substitutions at $n=0\ldots8$, symbolic WZ residual and square relation through degree $80$ have no program in the two published experiment commits cited here. No independently reproduced reading of that program is claimed. The exact identities above have their own proof evidence.
- **Open:** residues modulo eight are unaddressed. The full Kummer valuation theorem and a general formal Legendre generating-function theorem are not added.

The shared formulas hold for every index; the generic coefficient constructions are over commutative rings. The two source residue laws have their stated fixed moduli. The inspected source identifies no further theorem conditional on either conjecture. Its separate Formula expressions, recurrences and asymptotics are outside these settling statements.

## ASSUMED-UNVERIFIED

Literature-screen completeness and independent priority remain `ASSUMED-UNVERIFIED`. Source and literature readings attributed to the orchestrator are recorded in the preregistration. The escape audit is unfinished as specified in #19311. The unarchived route-check computation is not independently verified.
