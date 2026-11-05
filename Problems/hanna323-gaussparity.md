---
slug: hanna323-gaussparity
bibkey: hanna2019a323689
doi: null
url: https://oeis.org/A323689
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.result
---

# Hanna's A323689 Gaussian coefficient parity

## Problem

Paul D. Hanna's [OEIS A323689](https://oeis.org/A323689) defines $\sum_{m\ge0}(x^m+i)^m/(1+ix^m)^{m+1}$, with constant coefficient replaced by $1$. Its COMMENTS conjecture says odd coefficients occur only at $N=r^2$; its FORMULA also asserts oddness at every such index. The preregistration is [#21417](https://github.com/the-omega-institute/trureturing/issues/21417). The source is OEIS-only, with no identified DOI or arXiv id.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Literal rational summand in NAME and FORMULA | `HannaGaussianSquareParity.summand` | Same powers, imaginary unit and formal inverse; no leading factor. |
| Locally finite coefficient series | `HannaGaussianSquareParity.A` | Degree zero is $1$; at positive degree $N$, the sum has $1\le m\le N$. |
| Real coefficients and integer parity | `HannaGaussianSquareParity.claim` | Every natural degree has an ordinary integer representative embedded in the complex numbers. |
| Off-support conjecture and on-support FORMULA | `HannaGaussianSquareParity.result` | Oddness is equivalent to $N=r^2$, including degree zero. |

The settling result has no hypotheses. The public definitions retain the binding source conventions. The auxiliary recursive array and rational kernel are used within the proofs.

## Motivation

The two source series share a rational kernel. A symmetric integer array and fourth-root phases reduce parity to diagonal terms of a finite symmetric support.

## Gap

The bounded literature screen in #21417 found no settlement in the inspected source records, identifier searches or related Delannoy sources. The recorded OEIS revision retains the conjectural label. The unread dissertation lead and unavailable citation and later-author screens remain gaps. Literature completeness and originality are `ASSUMED-UNVERIFIED`.

## Route

Write $K_m(t)=(t+i)^m(1+it)^{-(m+1)}$. The integer array has boundary entries $w(0,k)=w(m,0)=1$ and recurrence $w(m+1,k+1)=w(m,k+1)+w(m+1,k)+w(m,k)$. Nested induction in the shared private `kernel_coefficient` proves $[t^k]K_m(t)=i^m(-i)^k w(m,k)$. The private `weight_symmetric` proves symmetry; `weight_odd` proves oddness of every weight. The private `phase_pair` and `kernel_pair` give an even ordinary integer for each transposed off-diagonal pair.

The private `coefficient_matrix` helper in each settling module extracts its exact exponent support. `HannaGaussianKernelParity.supported_matrix_integral` applies pairing to that support. The private `diagonal_parity` helper identifies the single possible diagonal index; `HannaGaussianSquareParity.result` gives the complete assertion.

## Falsifier

Changing any exponent, the leading power, the degree-zero convention or either direction of the odd-support equivalence changes the source assertion. The universal proof uses no finite experiment. A missing literature exclusion limits a novelty claim without changing the theorem under its displayed definitions.

## Evidence

`D5/S1/Recurrence/Algebraic/HannaGaussianSquareParity.result` proves the complete `HannaGaussianSquareParity.claim`. The shared module has admission basis `escape-witness`; `kernel_coefficient` is on both result paths. This settling module has `generality: G`, `utility: none` and `admission_basis: open-problem-resolution (#21417; Proved)`. There is no atom or cover.

The four-slot escape audit is unfinished for all seven public family theorems under [#22307](https://github.com/the-omega-institute/trureturing/issues/22307). No valid Reg mirror or `declared_validated` registration is asserted. Missing evidence comprises typed source reconstruction and selection, an enrolled readout bridge, and whole-family variation, sensitivity and observational dependence.

### Experiment

The checker and source tables are in [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/e0de2857d1d1616ee67af65221cc0028b888e4dd/docs/reports/oeis-a323689-hanna-square-parity), commit `e0de2857d1d1616ee67af65221cc0028b888e4dd`, script `check.py`, SHA-256 `b1a69c4f5dc4789d36755d31f212795fcb209457a7e947e60f8b1f8bf94305a4`.

Command from that revision's repository root: `python3 docs/reports/oeis-a323689-hanna-square-parity/check.py`; exit $0$, `ALL_CHECKS_OK`.

The checker verifies all $625$ kernel pairs $0\le m,k\le24$ by polynomial division, binomial expansion and the Delannoy recurrence. Literal rational summand division reproduces each source's coefficients $0$ through $80$. All $10001$ A323689 table entries $0\le N\le10000$ and all $10202$ A324300 entries $0\le N\le10201$ have zero coefficient, integrality and parity mismatches. These are finite fidelity checks.

## Triage

Tier $1$; resolution `Proved`; family preregistrations #21417 and #21418 have separate settling results and dossiers.

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Symmetry makes off-diagonal phase pairs even ordinary integers; the diagonal weight is odd. | **Proved, kernel-checked:** shared private `kernel_coefficient`, `weight_symmetric`, `phase_pair`, `kernel_pair` and public `weight_odd`; `supported_matrix_integral` states the resulting parity identity. |
| A323689 support is $mk=N$; A324300 support is $m+(m+1)k=N$. Swapping preserves each and fixes $N=m^2$ and $N=m(m+2)$. | **Proved in prose:** commutativity gives the first symmetry; the second equation is $(m+1)(k+1)=N+1$. Substituting $m=k$ gives the two diagonal indices. Each module's private `coefficient_matrix` and `diagonal_parity` implement these facts and feed its `result`. |
| The pairing mechanism extends to every finite set of natural indices and every symmetric decidable support, with this kernel. | **Proved, kernel-checked:** `HannaGaussianKernelParity.supported_matrix_integral`, with no other support hypothesis. |
| Exact tables and small-kernel checks support fidelity; they are not the unbounded proof. | **Computed:** the experiment above, exit $0$, with its script SHA-256 and exact ranges. No computation beyond those ranges is asserted. |
| Distinct nonzero absolute values in A323689, asymptotics and stronger residue formulas. | **Open:** neither settling result nor the finite experiment asserts these properties. |

**Source consequences — kernel-checked:** both the off-support conjecture and on-support parity assertion hold, together with integer representatives, at all natural indices. The same mechanism settles the companion preregistration. Other generating-function identities, distinct-value observations and other source sequences retain their separate proof obligations.

## ASSUMED-UNVERIFIED

Literature completeness, priority and absence of a settlement outside inspected sources remain unverified. The preregistrations name the dissertation and unavailable citation and later-author screens. Four-slot registration is unfinished under #22307; a mathematical proof is not a completed registration.
