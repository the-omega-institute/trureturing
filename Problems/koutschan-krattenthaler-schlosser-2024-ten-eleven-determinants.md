---
slug: koutschan-krattenthaler-schlosser-2024-ten-eleven-determinants
bibkey: koutschan2024determinantevaluations
doi: 10.1016/j.jsc.2024.102352
url: https://arxiv.org/abs/2401.08481v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.result
---

# Koutschan–Krattenthaler–Schlosser Conjecture 23, equation (10.11)

## Problem

Koutschan, Krattenthaler and Schlosser, arXiv:2401.08481v1, Conjecture 23, states: “Moreover, the following identities are conjectured to hold for all n ≥ 3:”. Equation (10.11) is

$G_{1,1,0,-2}(n)=-\frac1{49}G_{2,3,0,-6}(n)=-\frac27G_{6,4,5,-3}(n-1)=-\frac4{5577}G_{7,6,5,-7}(n-1)$.

The preregistration is [#19237](https://github.com/the-omega-institute/trureturing/issues/19237). The [Library note](../Library/RecurrenceComposition/koutschan2024determinantevaluations.md) records the source definition and all three equations.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Equation (1.2): falling factorial divided by $p!$ for $p\ge0$, zero for $p<0$ | `ShiftedG.binom` | Rational `Ring.choose` on the nonnegative branch, integer lower argument. |
| Section 10 determinant | `ShiftedG.G` | Integer parameters, rational entries, integer powers of 2 and zero-based `Fin n` indices. |
| “for all n ≥ 3” | `TenEleven.claim` | Natural size and the original lower bound. |
| Every consecutive equality of (10.11) | `TenEleven.claim` and `TenEleven.result` | Original coefficients, signs and size shifts; a chain is a conjunction of adjacent equalities. |

Natural subtraction is truncated at zero; within the source range it agrees with integer subtraction. The rational/integer coercions express the same source entries. There are no additional assumptions on the conjecture.

## Motivation

The determinant families share a rational column transformation. A common multiplier relates their generating functions, while small leading blocks determine the numerical ratios. This connects the same-size links and the size shifts in equations (10.10)–(10.12).

## Gap

The preregistrations #19228, #19236 and #19237 record a tier-1 published named conjecture. Their bounded literature screen covers the source, the author-hosted account, citing works and Chen–Chern–Yoshida arXiv:2507.15665v2. No prior settlement of these three equations was found in that inspected scope. Later works identified in the preregistration remain unread; completeness and publication priority are `ASSUMED-UNVERIFIED`.

## Route

Write the columns as power series and use

$h(t)=((1-t)(1-2t)(1-2t+2t^2))^{-1}$.

The factorizations $1-(1-2t)^4=8t(1-t)(1-2t+2t^2)$ and $t^4-(1-t)^4=-(1-2t)(1-2t+2t^2)$ make multiplication by $h$ convert column differences to the required columns. The multiplier has constant coefficient one, so its lower triangular coefficient matrix preserves determinants. Backward column differences also preserve determinants. Shared columns and a zero upper-right block reduce the same-size identities to leading determinants of sizes at most three. A first-row expansion gives each size shift.

The ShiftedG module's `det_smat_mul`, `det_diff`, `det_shift`, `shared_columns` and `det_comparison` implement these reductions; their applications in the `link_*` and size-shift lemmas give the source constants. The companion results combine the required links with rational arithmetic.

## Falsifier

A mismatch in the negative-lower-index binomial branch, integer exponent, parameter tuple, coefficient, adjacent equality or size shift would invalidate source fidelity. The public definitions and complete Scribe formulas expose each of these choices. The proof quantifies over all source sizes and does not infer a universal identity from the numerical checks.

## Evidence

`D5/S1/Recurrence/Algebraic/KoutschanKrattenthalerSchlosserTenEleven.result` proves `TenEleven.claim`. The three settling modules also prove the other two equations under their own preregistrations. Every declaration is classified `bind-only`; each auxiliary declaration has a named consumer. Admission is `open-problem-resolution (#19237; Proved)`, with `generality: I` and `utility: none`.

The escape audit is unfinished for all thirteen new public theorems, under [#19547](https://github.com/the-omega-institute/trureturing/issues/19547). No valid Reg mirror or `declared_validated` registration is asserted. The missing evidence is a typed source reconstruction and selection, realization-to-readout correspondence, and whole-family variation, sensitivity and observational-dependence proofs.

### Experiment

The checker is in [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f98805bfaf38b762694ef23efb2b5d1beb6cd0ec/docs/reports/koutschan-krattenthaler-schlosser-2024-shifted-g-1010-1011), commit `f98805bfaf38b762694ef23efb2b5d1beb6cd0ec`, script `check.py`, SHA-256 `6c3b5744d0d36f325a7b2e2996695759043796288d1c34cd2464b80bca9ab6f8`.

Command in that repository: `python3 docs/reports/koutschan-krattenthaler-schlosser-2024-shifted-g-1010-1011/check.py`; exit 0, `RESULT PASS`.

All three identities are checked for $3\le n\le10$. Seven same-size links are checked through size $N=10$, with their individual minimum sizes $3,2,3,1,2,1,2$ in the order BC, PD, PE, TF, HI, VJ, VK. Both size-shift structures are checked for $2\le n\le10$, the Proposition 22 pieces with the checker variable $1\le n\le9$ (the B-family size is $n+1$ and the H-family size is $n$), and the uniform difference identity symbolically for the six parameter sets specified by the checker. These are exact-arithmetic checks within the stated scope, separate from the universal Lean proofs.

## Triage

Tier 1; `theorem`; resolution `Proved`; no digestion atom. Each of #19228, #19236 and #19237 has its own settling module, dossier and resolution claim. The common helpers belong to the ShiftedG settling module; no independently admitted supporting module is asserted.

### What the settlement shows

- **Mathematics — kernel-checked:** all three binding claims, by `ShiftedG.result`, `TenTen.result` and `TenEleven.result`, in their full module namespaces. Every adjacent equality is retained.
- **Implementation — kernel-checked:** the literal rational binomial and determinant conventions and all three literal claims are compiled in the three-module layout. Public helper statements used across modules have full Scribe nodes.
- **Admission — recorded basis:** each module uses its own preregistered `open-problem-resolution` basis (#19228, #19236, #19237); no independent helper escape witness is claimed. The helpers are consumed proof organization, not separately claimed new content.
- **Literature — open:** the supplied bounded-screen gaps and publication priority remain `ASSUMED-UNVERIFIED`; this delivery makes no exhaustive originality claim.
- **Consequences — kernel-checked:** the same multiplier reductions supply (10.10)–(10.12). The private `ShiftedG.shiftedG_all` proves (10.12) at every positive size, in the form $n+1$ for every natural $n$.
- **Consequences — proved in prose, conditional on the cited product evaluations:** writing $P(n)=G_{3,0,3,3}(n)$, equation (10.10) expresses each chain member as a rational multiple of $P(n)$. If $P(n)=F(n)$, substitution gives the corresponding rational multiple of $F(n)$; the size shifts use $n+1$ or $n-1$ as displayed. Similarly, if $G_{2,1,2,0}(n)=H(n)$, (10.12) gives $G_{7,4,7,-1}(n)=H(n+1)/2$ for positive $n$. Combining with the source's Proposition 22 gives its linked families. The product evaluations themselves and these product-formula corollaries are not separately formalized here.
- **Mechanism and lower ranges — kernel-checked:** `link_BC`, `link_PD`, `link_PE`, `link_TF`, `link_HI`, `link_VJ`, `link_VK`, `prop_H`, `prop_B` and `p_shift_all` state the individual ratios and size shifts. The seven same-size links require sizes at least $3,2,3,1,2,1,2$, respectively. No uniform claim of sharpness is made.
- **Computed:** the experiment entry specifies the tested size ranges, symbolic substitutions and finite block checks. It does not classify an unbounded family.
- **Future question — open:** classification of other completely factoring determinant parameter families by this multiplier orbit, including the source's eighteen fully factoring families, is not addressed.
- **Source consequences — scope:** these equations may be used as proved identities in their stated ranges. The source's other conjectures and independent product evaluations keep their own evidence and hypotheses.

## ASSUMED-UNVERIFIED

Literature-search completeness, worldwide novelty and priority; unread later works in the preregistration; classification of all multiplier orbits; and separate formalization of the product evaluations and product-formula consequences. The escape audit remains unfinished under #19547. Numerical checks establish only their stated finite or symbolic scope.
